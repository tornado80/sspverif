use crate::errors::TypeError;

#[allow(dead_code)]
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
    Tuple(Vec<Type>),
    Table(Box<Type>, Box<Type>),
    Maybe(Box<Type>),
    Fn(Vec<Type>, Box<Type>), // arg types, return type
    Oracle(Vec<Type>, Box<Type>), // arg types, return type
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

    pub fn new_fn(args: Vec<Type>, ret: Type) -> Type {        
        Type::Fn(args, Box::new(ret))
    }
}

pub type TypeResult = std::result::Result<Type, TypeError>;
