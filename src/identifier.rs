use crate::expressions::Expression;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Identifier {
    Scalar(String),
    State { name: String, pkgname: String },
    Params { name: String, pkgname: String },
    Local(String),
    //    Bracket(Box<Identifier>, Expression),
}

impl Identifier {
    pub fn new_scalar(name: &str) -> Identifier {
        Identifier::Scalar(name.to_string())
    }

    // TODO implement correct converter trait to identifier expression
    pub fn to_expression(&self) -> Expression {
        Expression::Identifier(self.clone())
    }

    pub fn ident(&self) -> String {
        match self {
            Identifier::Scalar(ident) => ident.clone(),
            Identifier::Local(ident) => ident.clone(),
            Identifier::State { name, .. } => name.clone(),
            Identifier::Params { name, .. } => name.clone(),
        }
    }
}
