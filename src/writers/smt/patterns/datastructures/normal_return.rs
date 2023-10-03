use super::{DatastructurePattern, DatastructureSpec};
use crate::types::Type;
use crate::writers::smt::{exprs::SmtExpr, sorts::SmtPlainSort};

pub struct ReturnPattern<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub return_type: &'a Type,
}

pub struct ReturnSort<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub return_type: &'a Type,
}

use crate::impl_Into_for_PlainSort;
impl_Into_for_PlainSort!('a, ReturnSort<'a>);

impl<'a> SmtPlainSort for ReturnSort<'a> {
    fn sort_name(&self) -> String {
        let camel_case = ReturnPattern::CAMEL_CASE;
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;

        format!("{camel_case}-{game_name}-{pkg_inst_name}-{oracle_name}")
    }
}

#[derive(PartialEq, Eq)]
pub struct PartialReturnConstructor;

#[derive(PartialEq, Eq)]
pub enum PartialReturnSelector {
    GameState,
    ReturnValueOrAbort,
}

impl<'a> DatastructurePattern<'a> for ReturnPattern<'a> {
    type Constructor = PartialReturnConstructor;
    type Selector = PartialReturnSelector;
    type DeclareInfo = ();
    type Sort = ReturnSort<'a>;

    const CAMEL_CASE: &'static str = "Return";
    const KEBAB_CASE: &'static str = "return";

    fn sort(&self) -> ReturnSort<'a> {
        let ReturnPattern {
            game_name,
            pkg_inst_name,
            oracle_name,
            return_type,
        } = self;
        ReturnSort {
            game_name,
            pkg_inst_name,
            oracle_name,
            return_type,
        }
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;

        format!("mk-{kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;

        let field_name = match sel {
            PartialReturnSelector::GameState => "game-state",
            PartialReturnSelector::ReturnValueOrAbort => "return-value-or-abort",
        };

        format!("{kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}-{field_name}")
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let field_name = match sel {
            PartialReturnSelector::GameState => "game-state",
            PartialReturnSelector::ReturnValueOrAbort => "return-value-or-abort",
        };

        format!("match-{field_name}")
    }

    fn datastructure_spec(&self, _info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        DatastructureSpec(vec![(
            PartialReturnConstructor,
            vec![
                PartialReturnSelector::GameState,
                PartialReturnSelector::ReturnValueOrAbort,
            ],
        )])
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        let Self {
            game_name,
            return_type,
            ..
        } = self;

        let game_state_pattern = super::game_state::GameStatePattern { game_name };

        match sel {
            PartialReturnSelector::GameState => game_state_pattern.sort().sort_name().into(),
            PartialReturnSelector::ReturnValueOrAbort => ("ReturnValue", *return_type).into(),
        }
    }
}
