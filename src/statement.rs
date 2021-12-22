use crate::expressions::Expression;
use crate::types::Type;
use crate::identifier::Identifier;
use crate::scope::Scope;
use crate::errors::TypeCheckError;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Abort,
    Return(Expression),
    Assign(Identifier, Expression),
    TableAssign(Identifier, Expression, Expression), // TableAssign(T, 2+3, g^r) <== T[2+3] <-- g^r
    IfThenElse(Expression, Vec<Box<Statement>>, Vec<Box<Statement>>),
}

pub struct CodeBlock {
    pub expected_return_type: Type,
    pub block: Vec<Box<Statement>>,
}

impl CodeBlock {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        let CodeBlock{ expected_return_type: ret_type, block } = self;
        scope.enter();

        for (i, stmt) in block.into_iter().enumerate() {
            //println!("looking at {:} - {:?}", i, stmt);
            match &**stmt {
                Statement::Abort => {
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::TypeCheck(format!("Abort found before end of code block!")));
                    }
                },
                Statement::Return(expr) => {
                    let expr_type = expr.get_type(scope)?;
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::TypeCheck(format!("Return found before end of code block!")));
                    }
                    if expr_type != *ret_type {
                        return Err(TypeCheckError::TypeCheck(format!("return type does not match: {:?} != {:?}", ret_type, expr_type).to_string()))
                    }
                },
                Statement::Assign(id, expr) => {
                    //println!("scope: {:?}", scope);
                    
                    let expr_type = expr.get_type(scope)?;
                    if let Some(id_type) = scope.lookup(id) {
                        if id_type != expr_type {
                            return Err(TypeCheckError::TypeCheck("overwriting some value with incompatible type".to_string()))
                        }
                    } else {
                        scope.declare(id.clone(), expr_type)?;
                    }
                },
                Statement::TableAssign(id, idx, expr) => {
                    let expr_type = expr.get_type(scope)?;
                    let idx_type = idx.get_type(scope)?;
                    if let Some(id_type) = scope.lookup(id) {
                        if let Type::Table(k, v) = id_type {
                            if *k != idx_type || *v != expr_type {
                                return Err(TypeCheckError::TypeCheck("type of the table does not match".to_string()))
                            }
                        } else {
                            return Err(TypeCheckError::TypeCheck("table access on non-table".to_string()))
                        }
                    } else {
                        return Err(TypeCheckError::TypeCheck("assigning to table but table does not exist (here)".to_string()))
                    }
                },
                Statement::IfThenElse(expr, ifcode, elsecode) => {
                    if expr.get_type(scope)? != Type::Boolean {
                        return Err(TypeCheckError::TypeCheck("condition must be boolean".to_string()))
                    }
                    CodeBlock{
                        expected_return_type: ret_type.clone(),
                        block: ifcode.clone(),
                    }.typecheck(scope)?;

                    CodeBlock{
                        expected_return_type: ret_type.clone(),
                        block: elsecode.clone(),
                    }.typecheck(scope)?;
                }
            }
        }

        scope.leave();
        Ok(())
    }
}

#[macro_export]
macro_rules! block {
    ( $( $s:expr ),* ) => {
        {
            let mut res = Vec::new();
            $(
                res.push(Box::new($s.clone()));
            )*
                res
        }
    }
}
