use crate::{
    expressions::Expression, identifier::game_ident::GameConstIdentifier, types::Type,
    writers::smt::patterns::proof_constants::ConstantPattern,
};

#[derive(Clone, Debug)]
pub struct OracleArgs<'a> {
    pub oracle_name: &'a str,
    pub arg_name: &'a str,
    pub arg_type: &'a Type,
}

impl<'a> ConstantPattern for OracleArgs<'a> {
    type Sort = Type;

    fn name(&self) -> String {
        let Self {
            oracle_name,
            arg_name,
            ..
        } = self;

        format!("<arg-{oracle_name}-{arg_name}>")
    }

    fn sort(&self) -> Self::Sort {
        self.arg_type.clone()
    }
}
