use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Debug, Clone)]
pub struct Error(pub String);

impl<'a> super::Transformation for Transformation<'a> {
    type Err = Error;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Error> {
        let insts : Result<Vec<_>,_> = self.0.pkgs.iter().map(|inst| {
            let mut newinst = inst.clone();
            for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                newinst.pkg.oracles[i].code = returnify(&oracle.code, oracle.sig.tipe == Type::Empty)?;
            }
            Ok(newinst)
        }).collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            (),
        ))
    }
}

pub fn returnify(cb: &CodeBlock, none_ok: bool) -> Result<CodeBlock, Error> {
    match cb.0.last() {
        Some(Statement::IfThenElse(expr, ifcode, elsecode)) => {
            let mut retval = cb.0.clone();
            retval.pop();
            retval.push(Statement::IfThenElse(
                expr.clone(),
                returnify(ifcode, none_ok)?,
                returnify(elsecode, none_ok)?,
            ));
            Ok(CodeBlock(retval))
        }
        Some(Statement::Return(_)) | Some(Statement::Abort) => Ok(cb.clone()),
        _ => {
            if !none_ok {
                Err(Error("Missing return at end of code block with expected return value".to_string()))
            } else {
                let mut retval = cb.0.clone();
                retval.push(Statement::Return(None));
                Ok(CodeBlock(retval))
            }
        }
    }
}

/// Unit tests for returnify.
/// - First, all cases where blocks already end properly should be preserved:
///     preserves_return_none, preserves_return_some, preserves_abort
/// - Second, if a block ends in a non-return-type statement, a Return(None) is added
///     adds_return
/// - Finally, returnify should also consider ell branches of if-then-else
///     adds_if_return_with_branches, adds_else_return_with_branches
#[cfg(test)]
mod test {
    use super::{Transformation,returnify};
    use crate::expressions::Expression;
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, Statement};
    use crate::types::Type;
    use crate::block;

    #[test]
    fn preserves_return_none() {
        let code = block!{
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Sample(Type::Integer)),
            Statement::Return(None)
        };
        assert_eq!(code, returnify(&code, true).unwrap());
    }

    #[test]
    fn preserves_return_some() {
        let code = block!{
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Sample(Type::Integer)),
            Statement::Return(Some(Expression::IntegerLiteral("5".to_string())))
        };
        assert_eq!(code, returnify(&code, true).unwrap());
    }

    #[test]
    fn preserves_abort() {
        let code = block!{
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Sample(Type::Integer)),
            Statement::Abort
        };
        assert_eq!(code, returnify(&code, true).unwrap());
    }

    #[test]
    fn adds_return() {
        let before = block!{
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Sample(Type::Integer))
        };
        let after = block!{
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Sample(Type::Integer)),
            Statement::Return(None)
        };
        assert_eq!(after, returnify(&before, true).unwrap());
        assert_eq!(after, returnify(&after, true).unwrap());
    }

    #[test]
    fn adds_if_return_with_branches() {
        let before = block!{
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Assign(Identifier::new_scalar("d"),
                                      Expression::Sample(Type::Integer))
                },
                block!{
                    Statement::Assign(Identifier::new_scalar("e"),
                                      Expression::Sample(Type::Integer)),
                    Statement::Return(None)
                })
        };
        let after = block!{
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Assign(Identifier::new_scalar("d"),
                                      Expression::Sample(Type::Integer)),
                    Statement::Return(None)
                },
                block!{
                    Statement::Assign(Identifier::new_scalar("e"),
                                      Expression::Sample(Type::Integer)),
                    Statement::Return(None)
                })
        };
        assert_eq!(after, returnify(&before, true).unwrap());
        assert_eq!(after, returnify(&after, true).unwrap());
    }

    #[test]
    fn adds_else_return_with_branches() {
        let before = block!{
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Assign(Identifier::new_scalar("d"),
                                      Expression::Sample(Type::Integer))
                },
                block!{
                    Statement::Assign(Identifier::new_scalar("e"),
                                      Expression::Sample(Type::Integer))
                })
        };
        let after = block!{
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Assign(Identifier::new_scalar("d"),
                                      Expression::Sample(Type::Integer)),
                    Statement::Return(None)
                },
                block!{
                    Statement::Assign(Identifier::new_scalar("e"),
                                      Expression::Sample(Type::Integer)),
                    Statement::Return(None)
                })
        };
        assert_eq!(after, returnify(&before, true).unwrap());
        assert_eq!(after, returnify(&after, true).unwrap());
    }
}
