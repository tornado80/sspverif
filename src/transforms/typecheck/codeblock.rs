use super::errors::TypeCheckError;
use super::expression::get_type;
use super::scope::Scope;

use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

pub struct TypedCodeBlock {
    pub expected_return_type: Type,
    pub block: CodeBlock,
}

impl TypedCodeBlock {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        let TypedCodeBlock {
            expected_return_type: ret_type,
            block,
        } = self;
        scope.enter();

        // unpack
        let block = &block.0;

        for (i, stmt) in block.iter().enumerate() {
            //println!("looking at {:} - {:?}", i, stmt);
            match &*stmt {
                Statement::Abort => {
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::TypeCheck(
                            "Abort found before end of code block!".to_string(),
                        ));
                    }
                }
                Statement::Return(Some(expr)) => {
                    let expr_type = get_type(expr, scope)?;
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
                }
                Statement::Return(None) => {
                    if Type::Empty != *ret_type {
                        return Err(TypeCheckError::TypeCheck(format!(
                            "return type does not match: {:?} != Empty",
                            ret_type
                        )));
                    }
                }
                Statement::Assign(id, expr) => {
                    //println!("scope: {:?}", scope);

                    let expr_type = get_type(expr, scope)?;
                    if let Some(id_type) = scope.lookup(id) {
                        if id_type != expr_type {
                            return Err(TypeCheckError::TypeCheck(
                                "overwriting some value with incompatible type".to_string(),
                            ));
                        }
                    } else {
                        scope.declare(id.clone(), expr_type)?;
                    }
                }
                Statement::TableAssign(id, idx, expr) => {
                    let expr_type = get_type(expr, scope)?;
                    let idx_type = get_type(idx, scope)?;
                    if let Some(id_type) = scope.lookup(id) {
                        if let Type::Table(k, v) = id_type {
                            if *k != idx_type || *v != expr_type {
                                return Err(TypeCheckError::TypeCheck(
                                    "type of the table does not match".to_string(),
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
                }
                Statement::IfThenElse(expr, ifcode, elsecode) => {
                    if get_type(expr, scope)? != Type::Boolean {
                        return Err(TypeCheckError::TypeCheck(
                            "condition must be boolean".to_string(),
                        ));
                    }
                    TypedCodeBlock {
                        expected_return_type: ret_type.clone(),
                        block: ifcode.clone(),
                    }
                    .typecheck(scope)?;

                    TypedCodeBlock {
                        expected_return_type: ret_type.clone(),
                        block: elsecode.clone(),
                    }
                    .typecheck(scope)?;
                }
            }
        }

        scope.leave();
        Ok(())
    }
}
