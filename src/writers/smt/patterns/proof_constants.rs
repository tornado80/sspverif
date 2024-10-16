use crate::writers::smt::{
    declare,
    exprs::{SmtAssert, SmtEq2, SmtExpr},
    sorts::SmtSort,
};

mod oracle_args;

mod return_is_abort;
mod return_normal;
mod return_partial;
mod return_value;

mod state_intermediate;

pub(crate) use oracle_args::*;
pub(crate) use return_is_abort::*;
pub(crate) use return_normal::*;
pub(crate) use return_partial::*;
pub(crate) use return_value::*;
pub(crate) use state_intermediate::*;

pub trait ConstantPattern {
    type Sort: SmtSort;

    fn name(&self) -> String;
    fn sort(&self) -> Self::Sort;

    fn declare(&self) -> SmtExpr {
        declare::declare_const(self.name(), self.sort())
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
