use std::fmt::Display;

use crate::writers::smt::declare;
use crate::writers::smt::exprs::SmtExpr;
use crate::writers::smt::sorts::SmtSort;

mod game_consts;
mod game_state;
mod value_arg;

pub use game_consts::*;
pub use game_state::*;

#[derive(Debug, Clone, Copy)]
pub enum OldNewVariant {
    Old,
    New,
}

impl Display for OldNewVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OldNewVariant::Old => write!(f, "old"),
            OldNewVariant::New => write!(f, "new"),
        }
    }
}

pub trait OracleArgPattern {
    type Sort: SmtSort;
    type Variant;

    fn global_const_name(&self, game_inst_name: &str, variant: &Self::Variant) -> String;
    fn local_arg_name(&self) -> String;
    fn sort(&self) -> Self::Sort;

    fn declare(&self, game_inst_name: &str, variant: &Self::Variant) -> SmtExpr {
        declare::declare_const(self.global_const_name(game_inst_name, variant), self.sort())
    }
}

pub trait OldNewOracleArgPattern: OracleArgPattern<Variant = OldNewVariant> {
    fn old_global_const_name(&self, game_inst_name: &str) -> String {
        self.global_const_name(game_inst_name, &OldNewVariant::Old)
    }

    fn new_global_const_name(&self, game_inst_name: &str) -> String {
        self.global_const_name(game_inst_name, &OldNewVariant::New)
    }

    fn declare_old(&self, game_inst_name: &str) -> SmtExpr {
        self.declare(game_inst_name, &OldNewVariant::Old)
    }

    fn declare_new(&self, game_inst_name: &str) -> SmtExpr {
        self.declare(game_inst_name, &OldNewVariant::New)
    }
}

pub trait UnitOracleArgPattern: OracleArgPattern<Variant = ()> {
    fn unit_global_const_name(&self, game_inst_name: &str) -> String {
        <Self as OracleArgPattern>::global_const_name(self, game_inst_name, &())
    }

    fn unit_declare(&self, game_inst_name: &str) -> SmtExpr {
        <Self as OracleArgPattern>::declare(self, game_inst_name, &())
    }
}

impl<T: OracleArgPattern<Variant = OldNewVariant>> OldNewOracleArgPattern for T {}
impl<T: OracleArgPattern<Variant = ()>> UnitOracleArgPattern for T {}
