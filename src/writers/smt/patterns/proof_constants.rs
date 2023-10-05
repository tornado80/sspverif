use crate::{
    types::Type,
    writers::smt::{declare, exprs::SmtExpr, sorts::SmtSort},
};

use super::{datastructures, DatastructurePattern, GameStatePattern};

trait ConstantPattern {
    type Sort: SmtSort;

    fn name(&self) -> String;
    fn sort(&self) -> Self::Sort;

    fn declare(&self) -> SmtExpr {
        declare::declare_const(self.name(), self.sort())
    }
}

pub struct GameState<'a> {
    pub game_inst_name: &'a str,
    pub game_name: &'a str,
    pub variant: &'a str,
}

impl<'a> ConstantPattern for GameState<'a> {
    type Sort = datastructures::GameStateSort<'a>;

    fn name(&self) -> String {
        let Self {
            game_inst_name,
            variant,
            ..
        } = self;

        format!("game-state-{game_inst_name}-{variant}")
    }

    fn sort(&self) -> Self::Sort {
        GameStatePattern {
            game_name: self.game_name,
        }
        .sort()
    }
}

pub struct OracleArgs<'a> {
    pub pkg_name: &'a str,
    pub oracle_name: &'a str,
    pub arg_name: &'a str,
    pub arg_type: &'a Type,
}

impl<'a> ConstantPattern for OracleArgs<'a> {
    type Sort = Type;

    fn name(&self) -> String {
        let Self {
            pkg_name,
            oracle_name,
            arg_name,
            ..
        } = self;

        format!("arg-{pkg_name}-{oracle_name}-{arg_name}")
    }

    fn sort(&self) -> Self::Sort {
        self.arg_type.clone()
    }
}

/*
 * layers:
 * - just want to use the name
 * - want to put the arg in a function (need type)
 * - want to know which args a funtion has (with types)
 *
 * difference to datastructures: each can be declared on its own
 *
 *
 *
 */
