use std::fmt;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Type {
    Empty,
    Integer,
    String,
    Boolean,
    Bits(String), // Bits strings of length ...
    Scalar(String),
    AddiGroupEl(String), // name of the group
    MultGroupEl(String), // name of the group
    List(Box<Type>),
    Set(Box<Type>),
    Tuple(Vec<Box<Type>>),
    Table((Box<Type>, Box<Type>)),
    Maybe(Box<Type>),
}


impl Type {
    pub fn new_bits(length: &str) -> Type {
        Type::Bits(length.to_string())
    }

    pub fn new_scalar(name: &str) -> Type {
        Type::Scalar(name.to_string())
    }

    pub fn new_list(t: &Type) -> Type {
        Type::List(Box::new(t.clone()))
    }

    pub fn new_set(t: &Type) -> Type {
        Type::Set(Box::new(t.clone()))
    }
}

#[derive(Debug, Clone)]
pub struct TypeError;

pub type TypeResult = std::result::Result<Type, TypeError>;

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid type")
    }
}
