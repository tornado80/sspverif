use datastructures::{IntermediateStatePattern, ReturnPattern};

use crate::{
    types::Type,
    writers::smt::{
        declare,
        exprs::SmtExpr,
        sorts::{SmtReturnValue, SmtSort},
    },
};

use super::{
    datastructures, DatastructurePattern, GameStatePattern, IntermediateStateSort,
    PartialReturnPattern, PartialReturnSort, ReturnSort,
};

pub trait ConstantPattern {
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

#[derive(Clone, Debug)]
pub struct OracleArgs<'a> {
    pub oracle_name: &'a str,
    pub arg_name: &'a str,
    pub arg_type: &'a Type, // TODO maybe this shouldn't be here?
}

impl<'a> ConstantPattern for OracleArgs<'a> {
    type Sort = Type;

    fn name(&self) -> String {
        let Self {
            oracle_name,
            arg_name,
            ..
        } = self;

        format!("arg-{oracle_name}-{arg_name}")
    }

    fn sort(&self) -> Self::Sort {
        self.arg_type.clone()
    }
}

pub struct ReturnConst<'a> {
    pub game_inst_name: &'a str,
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
}

impl<'a> ConstantPattern for ReturnConst<'a> {
    type Sort = ReturnSort<'a>;

    fn name(&self) -> String {
        let Self {
            game_inst_name,
            oracle_name,
            ..
        } = self;

        format!("return-{game_inst_name}-{oracle_name}")
    }

    fn sort(&self) -> Self::Sort {
        ReturnPattern {
            game_name: self.game_name,
            pkg_inst_name: self.pkg_inst_name,
            oracle_name: self.oracle_name,
        }
        .sort()
    }
}

pub struct PartialReturnConst<'a> {
    pub game_inst_name: &'a str,
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
}

impl<'a> ConstantPattern for PartialReturnConst<'a> {
    type Sort = PartialReturnSort<'a>;

    fn name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        format!("partial-return-{game_inst_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn sort(&self) -> Self::Sort {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;

        PartialReturnPattern {
            game_name,
            pkg_inst_name,
            oracle_name,
        }
        .sort()
    }
}

pub struct IntermediateStateConst<'a> {
    pub game_inst_name: &'a str,
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub variant: &'a str,
}

impl<'a> ConstantPattern for IntermediateStateConst<'a> {
    type Sort = IntermediateStateSort<'a>;

    fn name(&self) -> String {
        let Self {
            game_inst_name,
            oracle_name,
            variant,
            ..
        } = self;

        format!("intermediate-state-{game_inst_name}-{oracle_name}-{variant}")
    }

    fn sort(&self) -> Self::Sort {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;

        IntermediateStatePattern {
            game_name,
            pkg_inst_name,
            oracle_name,
        }
        .sort()
    }
}

pub struct ReturnValueConst<'a> {
    pub game_inst_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
    pub tipe: &'a Type,
}

impl<'a> ConstantPattern for ReturnValueConst<'a> {
    type Sort = SmtReturnValue<Type>;

    fn name(&self) -> String {
        let Self {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        format!("return-value-{game_inst_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn sort(&self) -> Self::Sort {
        let inner_sort = self.tipe.clone();
        SmtReturnValue { inner_sort }
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
