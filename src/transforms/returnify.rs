use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

#[derive(Debug, Clone)]
pub struct Error(pub String);

pub struct TransformNg;

impl<'a> super::GameTransform for TransformNg {
    type Err = Error;
    type Aux = ();

    fn transform_game(&self, game: &Composition) -> Result<(Composition, Self::Aux), Self::Err> {
        let insts: Result<Vec<_>, _> = game
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code =
                        returnify(&oracle.code, oracle.sig.tipe == Type::Empty)?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..game.clone()
            },
            (),
        ))
    }
}

use super::GameTransform;

impl super::GameInstanceTransform for TransformNg {
    type Err = Error;
    type Aux = ();

    fn transform_game_instance(
        &self,
        instance: &crate::proof::GameInstance,
    ) -> Result<(crate::proof::GameInstance, Self::Aux), Self::Err> {
        let (game, _) = <Self as GameTransform>::transform_game(&self, instance.as_game())?;
        Ok((instance.with_other_game(game), ()))
    }
}

mod old {
    use super::super::Transformation as TransformationTrait;
    use super::{returnify, Error};
    use crate::package::Composition;
    use crate::types::Type;

    pub struct Transformation<'a>(pub &'a Composition);

    impl<'a> TransformationTrait for Transformation<'a> {
        type Err = Error;
        type Aux = ();

        fn transform(&self) -> Result<(Composition, ()), Error> {
            let insts: Result<Vec<_>, _> = self
                .0
                .pkgs
                .iter()
                .map(|inst| {
                    let mut newinst = inst.clone();
                    for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                        newinst.pkg.oracles[i].code =
                            returnify(&oracle.code, oracle.sig.tipe == Type::Empty)?;
                    }
                    Ok(newinst)
                })
                .collect();
            Ok((
                Composition {
                    pkgs: insts?,
                    ..self.0.clone()
                },
                (),
            ))
        }
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
                Err(Error(
                    "Missing return at end of code block with expected return value".to_string(),
                ))
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
    use super::returnify;
    use crate::block;
    use crate::expressions::Expression;
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, Statement};
    use crate::types::Type;

    #[test]
    fn preserves_return_none() {
        let code = block! {
            Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer),
            Statement::Return(None)
        };
        assert_eq!(code, returnify(&code, true).unwrap());
    }

    #[test]
    fn preserves_return_some() {
        let code = block! {
            Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer),
            Statement::Return(Some(Expression::IntegerLiteral("5".to_string())))
        };
        assert_eq!(code, returnify(&code, true).unwrap());
    }

    #[test]
    fn preserves_abort() {
        let code = block! {
            Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer),
            Statement::Abort
        };
        assert_eq!(code, returnify(&code, true).unwrap());
    }

    #[test]
    fn adds_return() {
        let before = block! {
            Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer)
        };
        let after = block! {
            Statement::Sample(Identifier::new_scalar("d"), None, None,  Type::Integer),
            Statement::Return(None)
        };
        assert_eq!(after, returnify(&before, true).unwrap());
        assert_eq!(after, returnify(&after, true).unwrap());
    }

    #[test]
    fn adds_if_return_with_branches() {
        let before = block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer)
                },
                block!{
                    Statement::Sample(Identifier::new_scalar("e"), None, None, Type::Integer),
                    Statement::Return(None)
                })
        };
        let after = block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer),
                    Statement::Return(None)
                },
                block!{
                    Statement::Sample(Identifier::new_scalar("e"), None, None, Type::Integer),
                    Statement::Return(None)
                })
        };
        assert_eq!(after, returnify(&before, true).unwrap());
        assert_eq!(after, returnify(&after, true).unwrap());
    }

    #[test]
    fn adds_else_return_with_branches() {
        let before = block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer)
                },
                block!{
                    Statement::Sample(Identifier::new_scalar("e"), None, None, Type::Integer)
                })
        };
        let after = block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Identifier::new_scalar("a").to_expression()),
                                            &(Identifier::new_scalar("a").to_expression())]),
                block!{
                    Statement::Sample(Identifier::new_scalar("d"), None, None, Type::Integer),
                    Statement::Return(None)
                },
                block!{
                    Statement::Sample(Identifier::new_scalar("e"), None, None, Type::Integer),
                    Statement::Return(None)
                })
        };
        assert_eq!(after, returnify(&before, true).unwrap());
        assert_eq!(after, returnify(&after, true).unwrap());
    }
}
