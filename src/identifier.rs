use crate::expressions::Expression;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Identifier {
    Scalar(String),
//    Bracket(Box<Identifier>, Expression),
}

impl Identifier {
    pub fn new_scalar(name: &str) -> Identifier {
        Identifier::Scalar(name.to_string())
    }

    // TODO implement correct converter trait to identifier expression
    pub fn to_expression(&self) -> Expression {
        Expression::Identifier(Box::new(self.clone()))
    }
}
