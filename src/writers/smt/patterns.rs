use crate::{package::OracleSig, split::SplitPath};

use super::exprs::SmtExpr;

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
    pub const ORACLE_ARG_GAME_STATE: &str = "__game_state";
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
                ..
            } => {
                let game_state_pattern = DatastructurePattern::GameState { game_name };

                let mut args = vec![(
                    Self::ORACLE_ARG_GAME_STATE.to_string(),
                    game_state_pattern.sort_name().into(),
                )];

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

pub enum DatastructurePattern<'a> {
    GameState {
        game_name: &'a str,
    },
    PackageState {
        game_name: &'a str,
        pkg_inst_name: &'a str,
    },
    Return {
        game_name: &'a str,
        pkg_inst_name: &'a str,
        oracle_name: &'a str,
        is_abort: bool,
    },
    IntermediateState {
        game_name: &'a str,
        pkg_inst_name: &'a str,
        oracle_name: &'a str,
        variant_name: &'a str,
    },
    PartialReturn {
        game_name: &'a str,
        pkg_inst_name: &'a str,
        oracle_name: &'a str,
    },
}

impl<'a> DatastructurePattern<'a> {
    pub const CONSTRUCTOR_INTERMEDIATE_STATE_BEGIN: &str = "begin";
    pub const CONSTRUCTOR_INTERMEDIATE_STATE_END: &str = "end";
    pub const SELECTOR_INTERMEDIATE_STATE_END_RETURN_VALUE: &str = "return_value";
    pub const SELECTOR_PARTIAL_RETURN_GAMESTATE: &str = "gamestate";
    pub const SELECTOR_PARTIAL_RETURN_INTERMEDIATESTATE: &str = "intermediate_state";

    pub fn intermediate_state_selector_local(local_name: &str) -> String {
        format!("local-{local_name}")
    }

    pub fn intermediate_state_selector_arg(local_name: &str) -> String {
        format!("arg-{local_name}")
    }

    pub fn pattern_kebab_case(&self) -> String {
        match self {
            DatastructurePattern::GameState { .. } => "game-state".to_string(),
            DatastructurePattern::PackageState { .. } => "pkg-state".to_string(),
            DatastructurePattern::Return {
                is_abort: false, ..
            } => "return".to_string(),
            DatastructurePattern::Return { is_abort: true, .. } => "abort".to_string(),
            DatastructurePattern::IntermediateState { .. } => "intermediate-state".to_string(),
            DatastructurePattern::PartialReturn { .. } => "partial-return".to_string(),
        }
    }

    pub fn pattern_camel_case(&self) -> String {
        match self {
            DatastructurePattern::GameState { .. } => "CompositionState".to_string(),
            DatastructurePattern::PackageState { .. } => "PackageState".to_string(),
            DatastructurePattern::Return { .. } => "Return".to_string(),
            DatastructurePattern::IntermediateState { .. } => "IntermediateState".to_string(),
            DatastructurePattern::PartialReturn { .. } => "PartialReturn".to_string(),
        }
    }

    pub fn constructor_name(&self) -> String {
        let pattern_kebab_case = self.pattern_kebab_case();

        match self {
            DatastructurePattern::GameState { game_name } => {
                format!("mk-{pattern_kebab_case}-{game_name}")
            }
            DatastructurePattern::PackageState {
                game_name,
                pkg_inst_name,
            } => {
                format!("mk-{pattern_kebab_case}-{game_name}-{pkg_inst_name}")
            }

            DatastructurePattern::Return {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            }
            | DatastructurePattern::PartialReturn {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            } => {
                format!("mk-{pattern_kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}")
            }

            DatastructurePattern::IntermediateState {
                game_name,
                pkg_inst_name,
                oracle_name,
                variant_name,
            } => {
                format!("mk-{pattern_kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}-{variant_name}")
            }
        }
    }

    pub fn selector_name(&self, field_name: &str) -> String {
        let pattern_kebab_case = self.pattern_kebab_case();

        match self {
            DatastructurePattern::GameState { game_name } => {
                format!("{pattern_kebab_case}-{game_name}-{field_name}")
            }
            DatastructurePattern::PackageState {
                game_name,
                pkg_inst_name,
            } => {
                format!("{pattern_kebab_case}-{game_name}-{pkg_inst_name}-{field_name}")
            }
            DatastructurePattern::Return {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            }
            | DatastructurePattern::PartialReturn {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            } => {
                format!(
                    "{pattern_kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}-{field_name}"
                )
            }

            DatastructurePattern::IntermediateState {
                game_name,
                pkg_inst_name,
                oracle_name,
                variant_name,
            } => {
                format!(
                    "{pattern_kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}-{variant_name}-{field_name}"
                )
            }
        }
    }

    pub fn sort_name(&self) -> String {
        let pattern_camel_case = self.pattern_camel_case();

        match self {
            DatastructurePattern::GameState { game_name } => {
                format!("{pattern_camel_case}-{game_name}")
            }
            DatastructurePattern::PackageState {
                game_name,
                pkg_inst_name,
            } => {
                format!("{pattern_camel_case}-{game_name}-{pkg_inst_name}")
            }
            DatastructurePattern::Return {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            }
            | DatastructurePattern::PartialReturn {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            } => {
                format!("{pattern_camel_case}-{game_name}-{pkg_inst_name}-{oracle_name}")
            }
            DatastructurePattern::IntermediateState {
                game_name,
                pkg_inst_name,
                oracle_name,
                ..
            } => {
                format!("{pattern_camel_case}-{game_name}-{pkg_inst_name}-{oracle_name}")
            }
        }
    }
}
