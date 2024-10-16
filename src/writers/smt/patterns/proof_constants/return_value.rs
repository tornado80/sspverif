use crate::{
    types::Type,
    writers::smt::{patterns::proof_constants::ConstantPattern, sorts::SmtReturnValue},
};

pub struct ReturnValueConst<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub tipe: &'a Type,
}

impl<'a> ConstantPattern for ReturnValueConst<'a> {
    type Sort = SmtReturnValue<Type>;

    fn name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        format!("return-value-{game_inst_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn sort(&self) -> Self::Sort {
        let inner_sort = self.tipe.clone();
        SmtReturnValue { inner_sort }
    }
}
