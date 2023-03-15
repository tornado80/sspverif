use crate::expressions::Expression;

#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Identifier {
    Scalar(String),
    State {
        name: String,
        pkg_inst_name: String,
        compname: String,
    },
    Parameter {
        name_in_pkg: String,
        pkgname: String,

        name_in_comp: String,
        compname: String,

        name_in_proof: String,
    },
    Local(String),
    // TODO add parameter identifiers for each place of definition (package/game/proof)
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
            Identifier::Parameter { name_in_pkg, .. } => name_in_pkg.clone(),
        }
    }
}
