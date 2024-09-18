use crate::{
    types::Type,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            DatastructurePattern as _, FunctionPattern, GameStatePattern, GlobalStatePattern,
            ReturnPattern, ReturnSort, VariablePattern as _,
        },
    },
};

pub const ORACLE_ARG_GAME_STATE: &str = "__global_state";
pub const ORACLE_ARG_INTERMEDIATE_STATE: &str = "__intermediate_state";

pub struct OraclePattern<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub oracle_args: &'a [(String, Type)],
}

impl<'a> FunctionPattern for OraclePattern<'a> {
    type ReturnSort = ReturnSort<'a>;

    fn function_name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;

        format!("oracle-{game_inst_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        let Self {
            game_inst_name,
            oracle_args,
            ..
        } = self;

        let game_state_pattern = GameStatePattern { game_inst_name };

        let global_state_pattern = &GlobalStatePattern;
        let mut args: Vec<(String, SmtExpr)> =
            vec![global_state_pattern.name_sort_tuple(&game_state_pattern)];

        args.extend(
            oracle_args
                .iter()
                .cloned()
                .map(|(name, tipe)| (name, tipe.into())),
        );

        args
    }

    fn function_return_sort(&self) -> ReturnSort<'a> {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;

        ReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        }
        .sort()
    }
}
