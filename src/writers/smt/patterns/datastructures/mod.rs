mod game_state;
mod intermediate_state;
mod partial_return;
mod pkg_state;

use std::iter::FromIterator;

pub use game_state::*;
pub use intermediate_state::*;
pub use partial_return::*;
pub use pkg_state::*;

use crate::writers::smt::{
    declare::declare_datatype,
    exprs::SmtExpr,
    partials::{SmtMatch, SmtMatchCase},
    sorts::SmtPlainSort,
};

pub trait DatastructurePattern<'a> {
    type Sort: SmtPlainSort;
    type Constructor: Eq;
    type Selector: Eq;
    type DeclareInfo;

    const CAMEL_CASE: &'static str;
    const KEBAB_CASE: &'static str;

    fn sort(&self) -> Self::Sort;
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

        declare_datatype(&self.sort().sort_name(), constructors)
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

    fn call_constructor<F>(
        &self,
        spec: &DatastructureSpec<'a, Self>,
        con: &Self::Constructor,
        f: F,
    ) -> Option<SmtExpr>
    where
        F: Fn(&Self::Selector) -> SmtExpr,
    {
        let (con, sels) = spec.0.iter().find(|(cur_con, _sels)| con == cur_con)?;

        // smt-lib doesn't like parens around constructors without any fields/selectors
        if sels.is_empty() {
            return Some(self.constructor_name(con).into());
        }

        Some(SmtExpr::List(Vec::from_iter(
            vec![self.constructor_name(con).into()]
                .into_iter()
                .chain(sels.iter().map(f)),
        )))
    }
}

pub struct DatastructureSpec<'a, P: DatastructurePattern<'a> + ?Sized>(
    pub Vec<(P::Constructor, Vec<P::Selector>)>,
);
