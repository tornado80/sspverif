use crate::expressions::Expression;
use crate::identifier::Identifier;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeBlock(pub Vec<Statement>);

impl CodeBlock {
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
