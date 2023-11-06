use crate::{package::Package, types::Type, writers::smt::sorts::SmtPlainSort};

use super::{DatastructurePattern, DatastructureSpec};

pub struct PackageStatePattern<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
}

#[derive(PartialEq, Eq)]
pub struct PackageStateSelector<'a> {
    pub name: &'a str,
    pub tipe: &'a Type,
}

pub struct PackageStateSort<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
}

use crate::impl_Into_for_PlainSort;
impl_Into_for_PlainSort!('a, PackageStateSort<'a>);

impl<'a> SmtPlainSort for PackageStateSort<'a> {
    fn sort_name(&self) -> String {
        let camel_case = PackageStatePattern::CAMEL_CASE;
        let Self {
            game_name,
            pkg_inst_name,
        } = self;

        format!("{camel_case}_{game_name}_{pkg_inst_name}")
    }
}

impl<'a> DatastructurePattern<'a> for PackageStatePattern<'a> {
    type Constructor = ();
    type Selector = PackageStateSelector<'a>;
    type DeclareInfo = Package;
    type Sort = PackageStateSort<'a>;

    const CAMEL_CASE: &'static str = "State";

    const KEBAB_CASE: &'static str = "state";

    fn sort(&self) -> PackageStateSort<'a> {
        let PackageStatePattern {
            game_name,
            pkg_inst_name,
        } = self;
        PackageStateSort {
            game_name,
            pkg_inst_name,
        }
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
            .map(|(name, tipe, _file_pos)| PackageStateSelector { name, tipe });

        DatastructureSpec(vec![((), selectors.collect())])
    }
}
