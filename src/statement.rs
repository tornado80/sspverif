use crate::expressions::Expression;
use crate::identifier::Identifier;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeBlock(pub Vec<Statement>);

impl CodeBlock {
    pub fn returnify(&self) -> CodeBlock {
        match self.0.last() {
            Some(Statement::IfThenElse(expr, ifcode, elsecode)) => {
                let mut retval = self.0.clone();
                retval.pop();
                retval.push(Statement::IfThenElse(
                    expr.clone(),
                    ifcode.returnify(),
                    elsecode.returnify(),
                ));
                CodeBlock(retval)
            }
            Some(Statement::Return(_)) | Some(Statement::Abort) => self.clone(),
            _ => {
                let mut retval = self.0.clone();
                retval.push(Statement::Return(None));
                CodeBlock(retval)
            }
        }
    }

    pub fn treeify(&self) -> CodeBlock {
        let mut before: Vec<Statement> = vec![];
        let mut after: Vec<Statement> = vec![];
        let mut found = false;

        let mut ifcode = None;
        let mut elsecode = None;
        let mut cond = None;

        for elem in &self.0 {
            match &*elem {
                Statement::IfThenElse(cond_, CodeBlock(ifcode_), CodeBlock(elsecode_)) => {
                    if !found {
                        ifcode = Some(ifcode_.clone());
                        elsecode = Some(elsecode_.clone());
                        cond = Some(cond_);
                        found = true;
                    } else {
                        after.push(elem.clone());
                    }
                }
                _ => {
                    if !found {
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
            before.push(Statement::IfThenElse(
                cond.unwrap().clone(),
                CodeBlock(newifcode).treeify(),
                CodeBlock(newelsecode).treeify(),
            ));
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

#[macro_export]
macro_rules! block {
    ( $( $s:expr ),* ) => {
        {
            CodeBlock(vec![ $( $s.clone(), )* ])
        }
    }
}
