use std::fmt;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

#[derive(Debug, Clone)]
pub enum ErrorLocation {
    Unknown,
}

#[derive(Debug)]
pub struct ScopeError;

#[derive(Debug, Clone)]
pub struct TypeError(pub String);

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid type")
    }
}

#[derive(Debug)]
pub enum TypeCheckError {
    MisplacedStatement(ErrorLocation, String),
    TypeMismatch(
        ErrorLocation,
        String, // message
        Type,   // found
        Type,   // expected
    ),
    UndefinedTable(ErrorLocation, String, Identifier),
    Scope(ScopeError),
    Type(TypeError),
    TypeCheck(String),
}

impl From<ScopeError> for TypeCheckError {
    fn from(error: ScopeError) -> Self {
        TypeCheckError::Scope(error)
    }
}

impl From<TypeError> for TypeCheckError {
    fn from(error: TypeError) -> Self {
        TypeCheckError::Type(error)
    }
}

pub type Result<T> = std::result::Result<T, TypeCheckError>;

pub type TypeResult = Result<Type>;
pub type ExpressionResult = Result<Expression>;
