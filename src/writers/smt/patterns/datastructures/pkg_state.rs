use crate::{
    package::Package,
    types::Type,
    writers::smt::{
        exprs::{smt_to_string, SmtExpr},
        sorts::SmtPlainSort,
    },
};

use super::{DatastructurePattern, DatastructureSpec};

pub struct PackageStatePattern<'a> {
    pub pkg_name: &'a str,
    pub params: Vec<SmtExpr>,
}

impl<'a> PackageStatePattern<'a> {
    fn name(&self) -> String {
        let pkg_name = &self.pkg_name;

        if self.params.is_empty() {
            pkg_name.to_string()
        } else {
            let encoded_params = encode_smt_exprs(&self.params);
            format!("{pkg_name}-{encoded_params}")
        }
    }
}

#[derive(PartialEq, Eq)]
pub struct PackageStateSelector<'a> {
    pub name: &'a str,
    pub ty: &'a Type,
}

pub struct PackageStateSort<'a> {
    pub pkg_name: &'a str,
    pub encoded_params: String,
}

use crate::impl_Into_for_PlainSort;
impl_Into_for_PlainSort!('a, PackageStateSort<'a>);

impl<'a> SmtPlainSort for PackageStateSort<'a> {
    fn sort_name(&self) -> String {
        let camel_case = PackageStatePattern::CAMEL_CASE;
        let Self {
            pkg_name,
            encoded_params,
        } = self;

        format!("<{camel_case}_{pkg_name}_{encoded_params}>")
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
        let PackageStatePattern { pkg_name, params } = self;
        PackageStateSort {
            pkg_name,
            encoded_params: encode_smt_exprs(&params),
        }
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self { pkg_name, params } = self;
        let encoded_params = encode_smt_exprs(&params);

        format!("<mk-{kebab_case}-{pkg_name}-{encoded_params}>")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self { pkg_name, params } = self;
        let encoded_params = encode_smt_exprs(&params);

        let PackageStateSelector {
            name: field_name, ..
        } = sel;

        format!("<{kebab_case}-{pkg_name}-{encoded_params}-{field_name}>")
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let PackageStateSelector {
            name: field_name, ..
        } = sel;

        format!("<match-{field_name}>")
    }

    fn selector_sort(&self, sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
        let PackageStateSelector { ty: tipe, .. } = sel;
        (*tipe).into()
    }

    fn datastructure_spec(&self, pkg: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let selectors = pkg
            .state
            .iter()
            .map(|(name, tipe, _file_pos)| PackageStateSelector { name, ty: tipe });

        DatastructureSpec(vec![((), selectors.collect())])
    }
}

fn encode_smt_exprs(exprs: &[SmtExpr]) -> String {
    let initial = "<$".to_string();
    let mut inner = exprs.iter().fold(initial, |mut acc, expr| {
        acc.push_str(&encode_smt_expr(expr));
        acc
    });
    inner.push_str("$>");
    inner
}

fn encode_smt_expr(expr: &SmtExpr) -> String {
    match expr {
        SmtExpr::Comment(_) => "".to_string(),
        SmtExpr::Atom(atom) => format!("<!{atom}!>"),
        SmtExpr::List(exprs) => encode_smt_exprs(exprs),
    }
}
