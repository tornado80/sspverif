mod game_state;
mod intermediate_state;
mod partial_return;
mod pkg_state;

pub use game_state::*;
pub use intermediate_state::*;
pub use partial_return::*;
pub use pkg_state::*;

use crate::writers::smt::{
    declare::declare_datatype,
    exprs::SmtExpr,
    partials::{SmtMatch, SmtMatchCase},
};

pub trait DatastructurePattern2<'a> {
    type Constructor;
    type Selector: Eq;
    type DeclareInfo;

    const CAMEL_CASE: &'static str;
    const KEBAB_CASE: &'static str;

    fn sort_name(&self) -> String;
    fn constructor_name(&self, cons: &Self::Constructor) -> String;
    fn selector_name(&self, sel: &Self::Selector) -> String;
    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr;

    fn datastructure_spec(&self, info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self>;

    fn declare_datatype(&self, spec: &DatastructureSpec<'a, Self>) -> SmtExpr {
        let DatastructureSpec(constructors) = spec;
        let constructors = constructors.iter().map(|(con, sels)| {
            (
                self.constructor_name(con),
                sels.iter()
                    .map(|sel| (self.selector_name(sel), self.selector_sort(sel)))
                    .collect(),
            )
        });

        declare_datatype(&self.sort_name(), constructors)
    }

    fn access<S: Into<SmtExpr>>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        selector: &Self::Selector,
        structure: S,
    ) -> Option<SmtExpr> {
        spec.0.iter().find(|(_con, sels)| sels.contains(selector))?;

        Some((self.selector_name(selector), structure).into())
    }

    fn update<S: Into<SmtExpr>, V: Into<SmtExpr>>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        selector: &Self::Selector,
        structure: S,
        new_value: V,
    ) -> Option<SmtExpr> {
        let (constructor, selectors) =
            spec.0.iter().find(|(_con, sels)| sels.contains(selector))?;

        let structure: SmtExpr = structure.into();
        let new_value: SmtExpr = new_value.into();

        let mut call: Vec<SmtExpr> = vec![self.constructor_name(constructor).into()];

        call.extend(selectors.iter().map(|cur_sel| {
            if cur_sel == selector {
                new_value.clone()
            } else {
                (self.selector_name(cur_sel), structure.clone()).into()
            }
        }));

        Some(call.into())
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String;

    fn match_expr<E, F>(&self, expr: E, spec: &DatastructureSpec<'a, Self>, f: F) -> SmtExpr
    where
        E: Clone + std::fmt::Debug + Into<SmtExpr>,
        F: Fn(&Self::Constructor) -> SmtExpr,
    {
        SmtMatch {
            expr,
            cases: spec
                .0
                .iter()
                .map(|(con, sels)| -> SmtMatchCase<_> {
                    SmtMatchCase {
                        constructor: self.constructor_name(con),
                        args: sels.iter().map(|sel| self.matchfield_name(sel)).collect(),
                        body: f(con),
                    }
                })
                .collect(),
        }
        .into()
    }
}

pub struct DatastructureSpec<'a, P: DatastructurePattern2<'a> + ?Sized>(
    pub Vec<(P::Constructor, Vec<P::Selector>)>,
);

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
