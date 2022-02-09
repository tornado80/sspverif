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
