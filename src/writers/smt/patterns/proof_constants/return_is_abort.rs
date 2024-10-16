use crate::{
    types::Type,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            proof_constants::ConstantPattern, DatastructurePattern, ReturnValue,
            ReturnValueConstructor,
        },
        sorts::SmtBool,
    },
};

#[derive(Clone, Copy, Debug)]
pub struct ReturnIsAbortConst<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub tipe: &'a Type,
}

impl<'a> ConstantPattern for ReturnIsAbortConst<'a> {
    type Sort = SmtBool;

    fn name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        format!("<return-is-abort-{game_inst_name}-{pkg_inst_name}-{oracle_name}>")
    }

    fn sort(&self) -> Self::Sort {
        SmtBool
    }
}

impl<'a> ReturnIsAbortConst<'a> {
    pub(crate) fn value(&self, return_value: impl Into<SmtExpr>) -> SmtExpr {
        let pattern = ReturnValue {
            inner_type: self.tipe,
        };

        let spec = pattern.datastructure_spec(&());

        pattern.match_expr(return_value, &spec, |con| {
            match con {
                ReturnValueConstructor::Return => false,
                ReturnValueConstructor::Abort => true,
            }
            .into()
        })
    }
}
