use crate::writers::smt::exprs::SmtExpr;
use crate::{package::OracleSig, split::SplitPath};

use super::{DatastructurePattern, DatastructurePattern2, IntermediateStatePattern};

pub enum FunctionPattern<'a> {
    Oracle {
        game_name: &'a str,
        pkg_inst_name: &'a str,
        oracle_sig: &'a OracleSig,
    },
    DispatchOracle {
        game_name: &'a str,
        pkg_inst_name: &'a str,
        oracle_sig: &'a OracleSig,
    },
    PartialOracle {
        game_name: &'a str,
        pkg_inst_name: &'a str,
        oracle_name: &'a str,
        split_path: &'a SplitPath,
    },
    RandomnessFunction,
    ParameterFunction,
}

impl<'a> FunctionPattern<'a> {
    pub const ORACLE_ARG_GAME_STATE: &str = "__global_state";
    pub const ORACLE_ARG_INTERMEDIATE_STATE: &str = "__intermediate_state";

    pub fn function_name(&self) -> String {
        match self {
            FunctionPattern::Oracle {
                game_name,
                pkg_inst_name,
                oracle_sig,
            }
            | FunctionPattern::DispatchOracle {
                game_name,
                pkg_inst_name,
                oracle_sig,
            } => {
                let oracle_name = &oracle_sig.name;
                format!("oracle-{game_name}-{pkg_inst_name}-{oracle_name}")
            }
            FunctionPattern::PartialOracle {
                game_name,
                pkg_inst_name,
                oracle_name,
                split_path,
            } => {
                let path = split_path.smt_name();
                format!("oracle-{game_name}-{pkg_inst_name}-{oracle_name}-{path}")
            }
            FunctionPattern::RandomnessFunction => todo!(),
            FunctionPattern::ParameterFunction => todo!(),
        }
    }

    pub fn function_argspec(&self) -> Vec<(String, SmtExpr)> {
        match self {
            //TODO add gamestate
            FunctionPattern::Oracle {
                oracle_sig,
                game_name,
                pkg_inst_name,
            } => {
                let game_state_pattern = DatastructurePattern::GameState { game_name };
                let intermediate_state_pattern = IntermediateStatePattern {
                    game_name,
                    pkg_inst_name,
                    oracle_name: &oracle_sig.name,
                };

                let mut args: Vec<(_, SmtExpr)> = vec![
                    (
                        Self::ORACLE_ARG_GAME_STATE.to_string(),
                        game_state_pattern.sort_name().into(),
                    ),
                    (
                        Self::ORACLE_ARG_INTERMEDIATE_STATE.to_string(),
                        intermediate_state_pattern.sort_name().into(),
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

            FunctionPattern::DispatchOracle {
                oracle_sig,
                game_name,
                pkg_inst_name,
            } => {
                let oracle_name = &oracle_sig.name;
                let game_state_pattern = DatastructurePattern::GameState { game_name };
                let intermediate_state_pattern = DatastructurePattern::IntermediateState {
                    game_name,
                    pkg_inst_name,
                    oracle_name,

                    // HACK: this is technically invalid data, but we only use
                    // it for generating the sort, which doesn't need this field,
                    // so it's fine 🔥🐶🔥
                    variant_name: "",
                };

                let mut args = vec![
                    (
                        Self::ORACLE_ARG_GAME_STATE.to_string(),
                        game_state_pattern.sort_name().into(),
                    ),
                    (
                        Self::ORACLE_ARG_INTERMEDIATE_STATE.to_string(),
                        intermediate_state_pattern.sort_name().into(),
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
            FunctionPattern::PartialOracle { .. } => todo!(),
            FunctionPattern::RandomnessFunction => todo!(),
            FunctionPattern::ParameterFunction => todo!(),
        }
    }

    pub fn function_return_sort_name(&self) -> String {
        match self {
            FunctionPattern::Oracle {
                game_name,
                pkg_inst_name,
                oracle_sig,
            } => todo!(),
            FunctionPattern::DispatchOracle {
                game_name,
                pkg_inst_name,
                oracle_sig,
            } => {
                let partial_return_pattern = DatastructurePattern::PartialReturn {
                    game_name,
                    pkg_inst_name,
                    oracle_name: &oracle_sig.name,
                };

                partial_return_pattern.sort_name()
            }
            FunctionPattern::PartialOracle {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            } => {
                let partial_return_pattern = DatastructurePattern::PartialReturn {
                    game_name,
                    pkg_inst_name,
                    oracle_name,
                };

                partial_return_pattern.sort_name()
            }
            FunctionPattern::RandomnessFunction => todo!(),
            FunctionPattern::ParameterFunction => todo!(),
        }
    }
}
