use crate::expressions::Expression;
use crate::types::Type;
use crate::identifier::Identifier;
use crate::scope::Scope;
use crate::errors::TypeCheckError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub  struct CodeBlock(pub Vec<Statement>);

impl CodeBlock {
    pub fn returnify(&self) -> CodeBlock {
        match self.0.last() {
            Some(Statement::IfThenElse(expr, ifcode, elsecode)) => {
                let mut retval = self.0.clone();
                retval.pop();
                retval.push(
                    Statement::IfThenElse(
                        expr.clone(),
                        ifcode.returnify(),
                        elsecode.returnify()));
                CodeBlock(retval)
            },
            Some(Statement::Return(_)) | Some(Statement::Abort) => {
                self.clone()
            },
            _ => {
                let mut retval = self.0.clone();
                retval.push(Statement::Return(None));
                CodeBlock(retval)
            }
        }
    }
    
    pub fn treeify(&self) -> CodeBlock {
        let mut before: Vec<Statement> = vec![];
        let mut after:Vec<Statement> = vec![];
        let mut found = false;

        let mut ifcode = None;
        let mut elsecode = None;
        let mut cond = None;
        
        for elem in &self.0 {
            match &*elem {
                Statement::IfThenElse(cond_, CodeBlock(ifcode_), CodeBlock(elsecode_)) => {
                    if ! found {
                        ifcode = Some(ifcode_.clone());
                        elsecode = Some(elsecode_.clone());
                        cond = Some(cond_);
                        found = true;
                    } else {
                        after.push(elem.clone());
                    }
                }
                _ => {
                    if ! found {
                        before.push(elem.clone());
                    } else {
                        after.push(elem.clone());
                    }
                }
            }
        }

        if found {
            let mut newifcode = ifcode.unwrap();
            newifcode.append(&mut after.clone());
            let mut newelsecode = elsecode.unwrap();
            newelsecode.append(&mut after.clone());
            before.push(Statement::IfThenElse(cond.unwrap().clone(),
                                              CodeBlock(newifcode).treeify(),
                                              CodeBlock(newelsecode).treeify()));
            CodeBlock(before)
        } else {
            self.clone()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Abort,
    Return(Option<Expression>),
    Assign(Identifier, Expression),
    #[allow(dead_code)]
    TableAssign(Identifier, Expression, Expression), // TableAssign(T, 2+3, g^r) <== T[2+3] <-- g^r
    IfThenElse(Expression, CodeBlock, CodeBlock),
}


pub struct TypedCodeBlock {
    pub expected_return_type: Type,
    pub block: CodeBlock
}

impl TypedCodeBlock {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        let TypedCodeBlock{ expected_return_type: ret_type, block } = self;
        scope.enter();

        // unpack
        let block = &block.0;

        for (i, stmt) in block.iter().enumerate() {
            //println!("looking at {:} - {:?}", i, stmt);
            match &*stmt {
                Statement::Abort => {
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::TypeCheck("Abort found before end of code block!".to_string()));
                    }
                },
                Statement::Return(Some(expr)) => {
                    let expr_type = expr.get_type(scope)?;
                    if i < block.len() - 1 {
                        return Err(TypeCheckError::TypeCheck("Return found before end of code block!".to_string()));
                    }
                    if expr_type != *ret_type {
                        return Err(TypeCheckError::TypeCheck(format!("return type does not match: {:?} != {:?}", ret_type, expr_type)))
                    }
                },
                Statement::Return(None) => {
                    if Type::Empty != *ret_type {
                        return Err(TypeCheckError::TypeCheck(format!("return type does not match: {:?} != Empty", ret_type)))
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
                    TypedCodeBlock{
                        expected_return_type: ret_type.clone(),
                        block: ifcode.clone(),
                    }.typecheck(scope)?;

                    TypedCodeBlock{
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
            CodeBlock(vec![ $( $s.clone(), )* ])
        }
    }
}
