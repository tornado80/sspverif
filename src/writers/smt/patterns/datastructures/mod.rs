mod game_state;
mod intermediate_state;
mod partial_return;

pub use game_state::*;
pub use intermediate_state::*;
pub use partial_return::*;

use crate::writers::smt::exprs::SmtExpr;

pub trait DatastructurePattern2 {
    type Constructor;
    type Selector;
    type DeclareInfo;

    const CAMEL_CASE: &'static str;
    const KEBAB_CASE: &'static str;

    fn sort_name(&self) -> String;
    fn constructor_name(&self, cons: &Self::Constructor) -> String;
    fn selector_name(&self, sel: &Self::Selector) -> String;
    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr;

    fn declare_datatype(&self, info: &Self::DeclareInfo) -> SmtExpr;
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

    pub fn intermediate_state_selector_loopvar(var_name: &str) -> String {
        format!("loopvar-{var_name}")
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
