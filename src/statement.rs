use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeBlock(pub Vec<Statement>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Abort,
    Return(Option<Expression>),
    Assign(Identifier, Expression),
    TableAssign(Identifier, Expression, Expression), // TableAssign(T, 2+3, g^r) <== T[2+3] <-- g^r
    IfThenElse(Expression, CodeBlock, CodeBlock),
    Sample(Identifier, Option<Expression>, Type),
}

#[macro_export]
macro_rules! block {
    ( $( $s:expr ),* ) => {
        {
            CodeBlock(vec![ $( $s.clone(), )* ])
        }
    }
}
