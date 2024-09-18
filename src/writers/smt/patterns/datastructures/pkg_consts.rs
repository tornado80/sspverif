use crate::{
    impl_Into_for_PlainSort,
    package::Package,
    types::Type,
    writers::smt::{
        patterns::{DatastructurePattern, DatastructureSpec},
        sorts::SmtPlainSort,
    },
};

pub struct PackageConstsPattern<'a> {
    pub pkg_name: &'a str,
}

#[derive(PartialEq, Eq)]
pub struct PackageConstsSelector<'a> {
    name: &'a str,
    ty: &'a Type,
}

pub struct PackageConstsDeclareInfo<'a> {
    pub(crate) pkg: &'a Package,
}

pub struct PackageConstsSort<'a> {
    pub pkg_name: &'a str,
}

impl<'a> SmtPlainSort for PackageConstsSort<'a> {
    fn sort_name(&self) -> String {
        let pkg_name = self.pkg_name;
        format!("<PackageConsts-{pkg_name}>")
    }
}

impl_Into_for_PlainSort!('a, PackageConstsSort<'a>);

impl<'a> DatastructurePattern<'a> for PackageConstsPattern<'a> {
    type Sort = PackageConstsSort<'a>;

    type Constructor = ();

    type Selector = PackageConstsSelector<'a>;

    type DeclareInfo = PackageConstsDeclareInfo<'a>;

    const CAMEL_CASE: &'static str = "PackageConsts";

    const KEBAB_CASE: &'static str = "pkg-consts";

    fn sort(&self) -> Self::Sort {
        PackageConstsSort {
            pkg_name: self.pkg_name,
        }
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self { pkg_name } = self;

        format!("mk-{kebab_case}-{pkg_name}")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let const_name = sel.name;
        let Self { pkg_name } = self;

        format!("{kebab_case}-{pkg_name}-{const_name}")
    }

    fn selector_sort(&self, sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
        sel.ty.into()
    }

    fn datastructure_spec(&self, info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let fields = info
            .pkg
            .params
            .iter()
            // function parameters are just declared as smtlib functions globally, so we don't
            // want them to be part of this datatype. This way we also stay compatible with
            // solvers that don't support higher-order functions.
            .filter(|(_name, ty, _)| !matches!(ty, crate::types::Type::Fn(_, _)))
            .map(|(name, ty, _)| PackageConstsSelector { name, ty })
            .collect();

        DatastructureSpec(vec![((), fields)])
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let const_name = sel.name;
        format!("<match-{const_name}>")
    }
}
