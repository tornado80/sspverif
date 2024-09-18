use crate::{
    package::OracleSig,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            DatastructurePattern as _, FunctionPattern, GameStatePattern, IntermediateStatePattern,
            PartialReturnPattern, PartialReturnSort,
        },
    },
};

use super::oracle::{ORACLE_ARG_GAME_STATE, ORACLE_ARG_INTERMEDIATE_STATE};

pub struct DispatchOraclePattern<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_sig: &'a OracleSig,
}

impl<'a> FunctionPattern for DispatchOraclePattern<'a> {
    type ReturnSort = PartialReturnSort<'a>;
    fn function_name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_sig,
        } = self;

        let oracle_name = &oracle_sig.name;
        format!("oracle-{game_inst_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        let DispatchOraclePattern {
            oracle_sig,
            game_inst_name,
            pkg_inst_name,
        } = self;

        let oracle_name = &oracle_sig.name;
        let game_state_pattern = GameStatePattern { game_inst_name };
        let intermediate_state_pattern = IntermediateStatePattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        };

        let mut args = vec![
            (
                ORACLE_ARG_GAME_STATE.to_string(),
                game_state_pattern.sort().into(),
            ),
            (
                ORACLE_ARG_INTERMEDIATE_STATE.to_string(),
                intermediate_state_pattern.sort().into(),
            ),
        ];

        args.extend(
            oracle_sig
                .args
                .iter()
                .cloned()
                .map(|(name, tipe)| (name, tipe.into())),
        );

        args
    }

    fn function_return_sort(&self) -> PartialReturnSort<'a> {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_sig,
        } = self;

        let partial_return_pattern = PartialReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name: &oracle_sig.name,
        };

        partial_return_pattern.sort()
    }
}
