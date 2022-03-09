use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};

pub struct Transformation<'a>(pub &'a Composition);

impl<'a> super::Transformation for Transformation<'a> {
    type Err = ();
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), ()> {
        let insts = self.0.pkgs.iter().map(|inst| {
            let mut newinst = inst.clone();
            newinst.pkg.oracles.iter_mut().for_each(|oracle| {
                oracle.code = returnify(&oracle.code);
            });
            newinst
        });
        Ok((
            Composition {
                pkgs: insts.collect(),
                ..self.0.clone()
            },
            (),
        ))
    }
}

pub fn returnify(cb: &CodeBlock) -> CodeBlock {
    match cb.0.last() {
        Some(Statement::IfThenElse(expr, ifcode, elsecode)) => {
            let mut retval = cb.0.clone();
            retval.pop();
            retval.push(Statement::IfThenElse(
                expr.clone(),
                returnify(ifcode),
                returnify(elsecode),
            ));
            CodeBlock(retval)
        }
        Some(Statement::Return(_)) | Some(Statement::Abort) => cb.clone(),
        _ => {
            let mut retval = cb.0.clone();
            retval.push(Statement::Return(None));
            CodeBlock(retval)
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
        assert_eq!(code, returnify(&code));
    }

    #[test]
    fn preserves_return_some() {
        let code = block!{
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Sample(Type::Integer)),
            Statement::Return(Some(Expression::IntegerLiteral("5".to_string())))
        };
        assert_eq!(code, returnify(&code));
    }

    #[test]
    fn preserves_abort() {
        let code = block!{
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Sample(Type::Integer)),
            Statement::Abort
        };
        assert_eq!(code, returnify(&code));
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
        assert_eq!(after, returnify(&before));
        assert_eq!(after, returnify(&after));
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
        assert_eq!(after, returnify(&before));
        assert_eq!(after, returnify(&after));
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
        assert_eq!(after, returnify(&before));
        assert_eq!(after, returnify(&after));
    }
}
