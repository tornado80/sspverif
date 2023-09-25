use crate::{package::Package, types::Type};

use super::{DatastructurePattern2, DatastructureSpec};

pub struct PackageStatePattern<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
}

#[derive(PartialEq, Eq)]
pub struct PackageStateSelector<'a> {
    pub name: &'a str,
    pub tipe: &'a Type,
}

impl<'a> DatastructurePattern2<'a> for PackageStatePattern<'a> {
    type Constructor = ();

    type Selector = PackageStateSelector<'a>;

    type DeclareInfo = Package;

    const CAMEL_CASE: &'static str = "State";

    const KEBAB_CASE: &'static str = "state";

    fn sort_name(&self) -> String {
        let camel_case = Self::CAMEL_CASE;
        let Self {
            game_name,
            pkg_inst_name,
        } = self;

        format!("{camel_case}_{game_name}_{pkg_inst_name}")
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            pkg_inst_name,
        } = self;

        format!("mk-{kebab_case}-{game_name}-{pkg_inst_name}")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            pkg_inst_name,
        } = self;
        let PackageStateSelector {
            name: field_name, ..
        } = sel;

        format!("{kebab_case}-{game_name}-{pkg_inst_name}-{field_name}")
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let PackageStateSelector {
            name: field_name, ..
        } = sel;

        format!("matchfield-{field_name}")
    }

    fn selector_sort(&self, sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
        let PackageStateSelector { tipe, .. } = sel;
        (*tipe).into()
    }

    fn datastructure_spec(&self, pkg: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let selectors = pkg
            .state
            .iter()
            .map(|(name, tipe)| PackageStateSelector { name, tipe });

        DatastructureSpec(vec![((), selectors.collect())])
    }
}
