use super::errors::TypeCheckError;
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
                        return Err(TypeCheckError::TypeCheck(
                            "Abort found before end of code block!".to_string(),
                        ));
                    }

                    new_block.push(stmt.clone());
                }
                Statement::Return(Some(expr)) => {
                    let typed_expr = typify(expr, scope)?;
                    let expr_type = get_type(&typed_expr, scope)?;
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::TypeCheck(
                            "Return found before end of code block!".to_string(),
                        ));
                    }
                    if expr_type != *ret_type {
                        return Err(TypeCheckError::TypeCheck(format!(
                            "return type does not match: {:?} != {:?} (when returning {:?})",
                            ret_type, expr_type, expr
                        )));
                    }
                    new_block.push(Statement::Return(Some(typed_expr)))
                }
                Statement::Return(None) => {
                    if Type::Empty != *ret_type {
                        return Err(TypeCheckError::TypeCheck(format!(
                            "return type does not match: {:?} != Empty",
                            ret_type
                        )));
                    }

                    new_block.push(stmt.clone());
                }
                Statement::Assign(id, expr) => {
                    //println!("scope: {:?}", scope);

                    let typed_expr = typify(expr, scope)?;
                    let expr_type = get_type(&typed_expr, scope)?;
                    if let Some(id_type) = scope.lookup(id) {
                        if id_type != expr_type {
                            return Err(TypeCheckError::TypeCheck(format!(
                                "overwriting some value with incompatible type: {:?} <- {:?}",
                                id, expr
                            )));
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
                                return Err(TypeCheckError::TypeCheck(format!(
                                    "type of expression {:?} used as index to table {:?} does not match: expected {:?}, got {:?}", idx, id, k, idx_type)));
                            }
                            if *v != expr_type {
                                return Err(TypeCheckError::TypeCheck(
                                    "value type of the table does not match".to_string(),
                                ));
                            }
                        } else {
                            return Err(TypeCheckError::TypeCheck(
                                "table access on non-table".to_string(),
                            ));
                        }
                    } else {
                        return Err(TypeCheckError::TypeCheck(
                            "assigning to table but table does not exist (here)".to_string(),
                        ));
                    }

                    new_block.push(Statement::TableAssign(id.clone(), typed_idx, typed_expr));
                }
                Statement::IfThenElse(expr, ifcode, elsecode) => {
                    let typed_expr = typify(expr, scope)?;
                    let expr_type = get_type(&typed_expr, scope)?;

                    if expr_type != Type::Boolean {
                        return Err(TypeCheckError::TypeCheck(
                            "condition must be boolean".to_string(),
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
/// - Abort should be allowed
/// - Should follow branching
/// - Should check on (table-)assign
#[cfg(test)]
mod test {
    use super::TypedCodeBlock;
    use crate::transforms::typecheck::{errors::TypeCheckError,scope::Scope};
    use crate::expressions::Expression;
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, Statement};
    use crate::types::Type;
    use crate::block;

    #[test]
    fn return_none_fails() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock{
            block: block!{
                Statement::Return(None)
            },
            expected_return_type: Type::Integer
        };
        let ret = code.typecheck(&mut scope);
        match ret {
            Ok(_) => assert!(false, "Typecheck should fail here"),
            Err(TypeCheckError::TypeCheck(_)) => assert!(true, "Typecheck should return a TypeCheckError"),
            Err(e) => assert!(false, format!("Unexpected error type: {:?}", e)),
        }
    }

    #[test]
    fn return_none_succeedes() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock{
            block: block!{
                Statement::Return(None)
            },
            expected_return_type: Type::Empty
        };
        let ret = code.typecheck(&mut scope);
        match ret {
            Ok(_) => assert!(true, "Typecheck should succeede"),
            Err(TypeCheckError::TypeCheck(_)) => assert!(false, "Typecheck should succeede TypeCheckError"),
            Err(e) => assert!(false, format!("Unexpected error type: {:?}", e)),
        }
    }

    #[test]
    fn return_wrong_type_fails() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock{
            block: block!{
                Statement::Return(Some(Expression::StringLiteral("test".to_string())))
            },
            expected_return_type: Type::Integer
        };
        let ret = code.typecheck(&mut scope);
        match ret {
            Ok(_) => assert!(false, "Typecheck should fail here"),
            Err(TypeCheckError::TypeCheck(_)) => assert!(true, "Typecheck should return a TypeCheckError"),
            Err(e) => assert!(false, format!("Unexpected error type: {:?}", e)),
        }
    }

    #[test]
    fn return_correcyt_type_succeedes() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock{
            block: block!{
                Statement::Return(Some(Expression::IntegerLiteral("23".to_string())))
            },
            expected_return_type: Type::Integer
        };
        let ret = code.typecheck(&mut scope);
        match ret {
            Ok(_) => assert!(true, "Typecheck should succeede"),
            Err(TypeCheckError::TypeCheck(_)) => assert!(false, "Typecheck should succeede TypeCheckError"),
            Err(e) => assert!(false, format!("Unexpected error type: {:?}", e)),
        }
    }

    #[test]
    fn return_abort_succeedes() {
        let mut scope = Scope::new();
        let code = TypedCodeBlock{
            block: block!{
                Statement::Abort
            },
            expected_return_type: Type::Integer
        };
        let ret = code.typecheck(&mut scope);
        match ret {
            Ok(_) => assert!(true, "Typecheck should succeede"),
            Err(TypeCheckError::TypeCheck(_)) => assert!(false, "Typecheck should succeede TypeCheckError"),
            Err(e) => assert!(false, format!("Unexpected error type: {:?}", e)),
        }
    }
}
