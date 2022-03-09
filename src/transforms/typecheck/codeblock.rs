use super::errors::{ErrorLocation, TypeCheckError};
use super::expression::{get_type, typify};
use super::scope::Scope;

use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

pub struct TypedCodeBlock {
    pub expected_return_type: Type,
    pub block: CodeBlock,
}

impl TypedCodeBlock {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<TypedCodeBlock, TypeCheckError> {
        let TypedCodeBlock {
            expected_return_type: ret_type,
            block,
        } = self;
        scope.enter();

        // unpack
        let block = &block.0;
        let mut new_block = vec![];

        for (i, stmt) in block.iter().enumerate() {
            //println!("looking at {:} - {:?}", i, stmt);
            match &*stmt {
                Statement::Abort => {
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::MisplacedStatement(
                            ErrorLocation::Unknown,
                            "Abort found before end of code block!".to_string(),
                        ));
                    }

                    new_block.push(stmt.clone());
                }
                Statement::Return(Some(expr)) => {
                    let typed_expr = typify(expr, scope)?;
                    let expr_type = get_type(&typed_expr, scope)?;
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::MisplacedStatement(
                            ErrorLocation::Unknown,
                            "Return found before end of code block!".to_string(),
                        ));
                    }
                    if expr_type != *ret_type {
                        return Err(TypeCheckError::TypeMismatch(
                            ErrorLocation::Unknown,
                            format!("return type does not match when returning {:?}", expr),
                            expr_type,
                            ret_type.clone(),
                        ));
                    }
                    new_block.push(Statement::Return(Some(typed_expr)))
                }
                Statement::Return(None) => {
                    if Type::Empty != *ret_type {
                        return Err(TypeCheckError::TypeMismatch(
                            ErrorLocation::Unknown,
                            "empty return in function that returns something".to_string(),
                            Type::Empty,
                            ret_type.clone(),
                        ));
                    }

                    new_block.push(stmt.clone());
                }
                Statement::Assign(id, expr) => {
                    //println!("scope: {:?}", scope);

                    let typed_expr = typify(expr, scope)?;
                    let expr_type = get_type(&typed_expr, scope)?;
                    if let Some(id_type) = scope.lookup(id) {
                        if id_type != expr_type {
                            return Err(TypeCheckError::TypeMismatch(
                                ErrorLocation::Unknown,
                                format!(
                                    "assigning {:?} to variable {:?} of different type",
                                    expr, id
                                ),
                                expr_type,
                                id_type,
                            ));
                        }
                    } else {
                        scope.declare(id.clone(), expr_type)?;
                    }

                    new_block.push(Statement::Assign(id.clone(), typed_expr));
                }
                Statement::TableAssign(id, idx, expr) => {
                    let typed_expr = typify(expr, scope)?;
                    let typed_idx = typify(idx, scope)?;

                    let expr_type = get_type(&typed_expr, scope)?;
                    let idx_type = get_type(&typed_idx, scope)?;

                    if let Some(id_type) = scope.lookup(id) {
                        if let Type::Table(k, v) = id_type.clone() {
                            if *k != idx_type {
                                return Err(TypeCheckError::TypeMismatch(ErrorLocation::Unknown, format!(
                                    "type of expression {:?} used as index to table {:?} does not match", idx, id),
                                    idx_type,
                                    *k
                                ));
                            }
                            if *v != expr_type {
                                return Err(TypeCheckError::TypeMismatch(
                                    ErrorLocation::Unknown,
                                    "value type of the table does not match".to_string(),
                                    expr_type,
                                    *v,
                                ));
                            }
                        } else {
                            return Err(TypeCheckError::TypeMismatch(
                                ErrorLocation::Unknown,
                                "table access on non-table".to_string(),
                                id_type,
                                Type::Table(Box::new(idx_type), Box::new(expr_type)),
                            ));
                        }
                    } else {
                        return Err(TypeCheckError::UndefinedTable(
                            ErrorLocation::Unknown,
                            "assigning to undefined table".to_string(),
                            id.clone(),
                        ));
                    }

                    new_block.push(Statement::TableAssign(id.clone(), typed_idx, typed_expr));
                }
                Statement::IfThenElse(expr, ifcode, elsecode) => {
                    let typed_expr = typify(expr, scope)?;
                    let expr_type = get_type(&typed_expr, scope)?;

                    if expr_type != Type::Boolean {
                        return Err(TypeCheckError::TypeMismatch(
                            ErrorLocation::Unknown,
                            format!(
                                "expression {:?} used as condition in if-then-else is not boolean",
                                expr
                            ),
                            expr_type,
                            Type::Boolean,
                        ));
                    }

                    let typed_ifcode = TypedCodeBlock {
                        expected_return_type: ret_type.clone(),
                        block: ifcode.clone(),
                    }
                    .typecheck(scope)?;

                    let typed_elsecode = TypedCodeBlock {
                        expected_return_type: ret_type.clone(),
                        block: elsecode.clone(),
                    }
                    .typecheck(scope)?;

                    new_block.push(Statement::IfThenElse(
                        typed_expr,
                        typed_ifcode.block,
                        typed_elsecode.block,
                    ));
                }
            }
        }

        scope.leave();
        Ok(TypedCodeBlock {
            block: CodeBlock(new_block),
            expected_return_type: ret_type.clone(),
        })
    }
}

/// unit tests for typing of (typed) code blocks
/// - Should honor the expected-return-type
///     return_none_fails, return_none_succeedes, return_wrong_type_fails, return_correcyt_type_succeedes
/// - Abort should be allowed
///     return_abort_succeedes
/// - Should follow branching
///     return_first_branch_wrong, return_second_branch_wrong, return_both_branch_correct, return_one_branch_aborts_correct
/// - Should check on (table-)assign
///     assign_succeedes_exists, assign_succeedes_new, assign_fails
#[cfg(test)]
mod test {
    use super::TypedCodeBlock;
    use crate::block;
    use crate::expressions::Expression;
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, Statement};
    use crate::transforms::typecheck::{errors::TypeCheckError, scope::Scope};
    use crate::types::Type;

    #[test]
    fn return_none_fails() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Return(None)
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);

        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn return_none_succeedes() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Return(None)
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);

        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn return_wrong_type_fails() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Return(Some(Expression::StringLiteral("test".to_string())))
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);
        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn return_correcyt_type_succeedes() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Return(Some(Expression::IntegerLiteral("23".to_string())))
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);

        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn return_abort_succeedes() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Abort
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);

        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn return_first_branch_wrong() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Expression::StringLiteral("23".to_string())),
                                            &(Expression::StringLiteral("23".to_string()))]),
                block!{
                    Statement::Return(Some(Expression::StringLiteral("23".to_string())))
                },
                block!{
                    Statement::Return(Some(Expression::IntegerLiteral("23".to_string())))
                })
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);

        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn return_second_branch_wrong() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Expression::StringLiteral("23".to_string())),
                                            &(Expression::StringLiteral("23".to_string()))]),
                block!{
                    Statement::Return(Some(Expression::IntegerLiteral("23".to_string())))
                },
                block!{
                    Statement::Return(Some(Expression::StringLiteral("23".to_string())))
                })
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);

        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn return_both_branch_correct() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Expression::StringLiteral("23".to_string())),
                                            &(Expression::StringLiteral("23".to_string()))]),
                block!{
                    Statement::Return(Some(Expression::IntegerLiteral("23".to_string())))
                },
                block!{
                    Statement::Return(Some(Expression::IntegerLiteral("23".to_string())))
                })
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);
        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn return_one_branch_aborts_correct() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock {
            block: block! {
            Statement::IfThenElse(
                Expression::new_equals(vec![&(Expression::StringLiteral("23".to_string())),
                                            &(Expression::StringLiteral("23".to_string()))]),
                block!{
                    Statement::Return(Some(Expression::IntegerLiteral("23".to_string())))
                },
                block!{
                    Statement::Abort
                })
            },
            expected_return_type: Type::Integer,
        };
        let ret = code.typecheck(&mut scope);

        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn assign_fails() {
        let mut scope = Scope::new();
        scope.enter();

        scope
            .declare(Identifier::Local("test".to_string()), Type::Integer)
            .unwrap();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Assign(
                    Identifier::Local("test".to_string()),
                    Expression::StringLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);

        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn assign_succeedes_exists() {
        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(Identifier::Local("test".to_string()), Type::Integer)
            .unwrap();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Assign(Identifier::Local("test".to_string()), Expression::IntegerLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);

        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn assign_succeedes_new() {
        let mut scope = Scope::new();
        scope.enter();
        let code = TypedCodeBlock {
            block: block! {
                Statement::Assign(Identifier::Local("test".to_string()), Expression::IntegerLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);

        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn table_assign_succeedes() {
        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(
                Identifier::Local("test".to_string()),
                Type::Table(Box::new(Type::Integer), Box::new(Type::String)),
            )
            .unwrap();
        let code = TypedCodeBlock {
            block: block! {
                Statement::TableAssign(Identifier::Local("test".to_string()),
                                       Expression::IntegerLiteral("42".to_string()),
                                       Expression::StringLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);

        assert!(matches!(ret, Ok(_)), "Typecheck should succeed");
    }

    #[test]
    fn table_assign_wrong_index_type() {
        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(
                Identifier::Local("test".to_string()),
                Type::Table(Box::new(Type::Integer), Box::new(Type::String)),
            )
            .unwrap();
        let code = TypedCodeBlock {
            block: block! {
                Statement::TableAssign(Identifier::Local("test".to_string()),
                                       Expression::StringLiteral("42".to_string()),
                                       Expression::StringLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);
        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn table_assign_wrong_value() {
        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(
                Identifier::Local("test".to_string()),
                Type::Table(Box::new(Type::Integer), Box::new(Type::String)),
            )
            .unwrap();
        let code = TypedCodeBlock {
            block: block! {
                Statement::TableAssign(Identifier::Local("test".to_string()),
                                       Expression::IntegerLiteral("42".to_string()),
                                       Expression::IntegerLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);
        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn table_assign_not_table() {
        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(Identifier::Local("test".to_string()), Type::Integer)
            .unwrap();
        let code = TypedCodeBlock {
            block: block! {
                Statement::TableAssign(Identifier::Local("test".to_string()),
                                       Expression::IntegerLiteral("42".to_string()),
                                       Expression::IntegerLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);
        assert!(
            matches!(ret, Err(TypeCheckError::TypeMismatch(_, _, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }

    #[test]
    fn table_assign_undeclared() {
        let mut scope = Scope::new();
        scope.enter();
        let code = TypedCodeBlock {
            block: block! {
                Statement::TableAssign(Identifier::Local("test".to_string()),
                                       Expression::IntegerLiteral("42".to_string()),
                                       Expression::IntegerLiteral("42".to_string()))
            },
            expected_return_type: Type::Empty,
        };
        let ret = code.typecheck(&mut scope);
        assert!(
            matches!(ret, Err(TypeCheckError::UndefinedTable(_, _, _))),
            "expected to fail with a TypeCheckError::TypeMismatch"
        );
    }
}
