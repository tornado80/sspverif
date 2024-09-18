use crate::identifier::Identifier;

impl Identifier {
    /// returns the string used as the identifier in SMT-LIB code
    pub(crate) fn smt_identifier(&self) -> String {
        match self {
            Identifier::Generated(name, _) => format!("<{name}>"),
            other => other.ident(),
        }
    }
}
