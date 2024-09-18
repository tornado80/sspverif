use crate::{
    split::SplitPath,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            DatastructurePattern as _, FunctionPattern, PartialReturnPattern, PartialReturnSort,
        },
    },
};

pub struct PartialOraclePattern<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub split_path: &'a SplitPath,
}

impl<'a> FunctionPattern for PartialOraclePattern<'a> {
    type ReturnSort = PartialReturnSort<'a>;

    fn function_name(&self) -> String {
        let PartialOraclePattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            split_path,
        } = self;

        let path = split_path.smt_name();
        format!("oracle-{game_inst_name}-{pkg_inst_name}-{oracle_name}-{path}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        todo!()
    }

    fn function_return_sort(&self) -> PartialReturnSort<'a> {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        let partial_return_pattern = PartialReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        };

        partial_return_pattern.sort()
    }
}
