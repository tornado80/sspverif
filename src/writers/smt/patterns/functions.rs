use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::patterns::ReturnPattern;
use crate::writers::smt::sorts::SmtSort;
use crate::{package::OracleSig, split::SplitPath};

use super::{
    DatastructurePattern, GameStatePattern, IntermediateStatePattern, PartialReturnPattern,
    PartialReturnSort, ReturnSort,
};

pub trait FunctionPattern {
    type ReturnSort: SmtSort;

    fn function_name(&self) -> String;
    fn function_args(&self) -> Vec<(String, SmtExpr)>;
    fn function_return_sort(&self) -> Self::ReturnSort;
}

pub const ORACLE_ARG_GAME_STATE: &str = "__global_state";
pub const ORACLE_ARG_INTERMEDIATE_STATE: &str = "__intermediate_state";

pub struct DispatchOraclePattern<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_sig: &'a OracleSig,
}

impl<'a> FunctionPattern for DispatchOraclePattern<'a> {
    type ReturnSort = PartialReturnSort<'a>;
    fn function_name(&self) -> String {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_sig,
        } = self;

        let oracle_name = &oracle_sig.name;
        format!("oracle-{game_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        let DispatchOraclePattern {
            oracle_sig,
            game_name,
            pkg_inst_name,
        } = self;

        let oracle_name = &oracle_sig.name;
        let game_state_pattern = GameStatePattern { game_name };
        let intermediate_state_pattern = IntermediateStatePattern {
            game_name,
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
            game_name,
            pkg_inst_name,
            oracle_sig,
        } = self;

        let partial_return_pattern = PartialReturnPattern {
            game_name,
            pkg_inst_name,
            oracle_name: &oracle_sig.name,
        };

        partial_return_pattern.sort()
    }
}

pub struct PartialOraclePattern<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub split_path: &'a SplitPath,
}

impl<'a> FunctionPattern for PartialOraclePattern<'a> {
    type ReturnSort = PartialReturnSort<'a>;

    fn function_name(&self) -> String {
        let PartialOraclePattern {
            game_name,
            pkg_inst_name,
            oracle_name,
            split_path,
        } = self;

        let path = split_path.smt_name();
        format!("oracle-{game_name}-{pkg_inst_name}-{oracle_name}-{path}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        todo!()
    }

    fn function_return_sort(&self) -> PartialReturnSort<'a> {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        let partial_return_pattern = PartialReturnPattern {
            game_name,
            pkg_inst_name,
            oracle_name,
        };

        partial_return_pattern.sort()
    }
}

pub struct OraclePattern<'a> {
    game_name: &'a str,
    pkg_inst_name: &'a str,
    oracle_sig: &'a OracleSig,
}

impl<'a> FunctionPattern for OraclePattern<'a> {
    type ReturnSort = ReturnSort<'a>;

    fn function_name(&self) -> String {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_sig,
        } = self;

        let oracle_name = &oracle_sig.name;
        format!("oracle-{game_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        let Self {
            oracle_sig,
            game_name,
            pkg_inst_name,
        } = self;

        let game_state_pattern = GameStatePattern { game_name };
        let intermediate_state_pattern = IntermediateStatePattern {
            game_name,
            pkg_inst_name,
            oracle_name: &oracle_sig.name,
        };

        let mut args: Vec<(_, SmtExpr)> = vec![
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

    fn function_return_sort(&self) -> ReturnSort<'a> {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_sig,
        } = self;

        ReturnPattern {
            game_name,
            pkg_inst_name,
            oracle_name: &oracle_sig.name,
        }
        .sort()
    }
}
