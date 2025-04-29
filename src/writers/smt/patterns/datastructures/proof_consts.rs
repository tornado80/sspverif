use crate::{
    proof::Proof,
    types::Type,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{DatastructurePattern, DatastructureSpec},
    },
};

#[derive(Debug, Clone)]
pub struct ProofConstsPattern<'a> {
    pub proof_name: &'a str,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ProofConstsSelector<'a> {
    pub(crate) name: &'a str,
    pub(crate) ty: &'a Type,
}

impl<'a> DatastructurePattern<'a> for ProofConstsPattern<'a> {
    type Constructor = ();

    type Selector = ProofConstsSelector<'a>;

    type DeclareInfo = Proof<'a>;

    const CAMEL_CASE: &'static str = "ProofConsts";

    const KEBAB_CASE: &'static str = "proof-consts";

    fn sort_name(&self) -> String {
        let camel_case = Self::CAMEL_CASE;
        let proof_name = self.proof_name;
        format!("<{camel_case}_{proof_name}>")
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let proof_name = self.proof_name;
        format!("mk-{kebab_case}-{proof_name}")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let const_name = sel.name;
        let proof_name = self.proof_name;

        format!("{kebab_case}-{proof_name}-{const_name}")
    }

    fn selector_sort(&self, sel: &Self::Selector) -> SmtExpr {
        sel.ty.into()
    }

    fn datastructure_spec(&self, info: &'a Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let fields = info
            .consts
            .iter()
            // function parameters are just declared as smtlib functions globally, so we don't
            // want them to be part of this datatype. This way we also stay compatible with
            // solvers that don't support higher-order functions.
            .filter(|(_name, ty)| !matches!(ty, crate::types::Type::Fn(_, _)))
            .map(|(name, ty)| ProofConstsSelector { name, ty })
            .collect();

        DatastructureSpec(vec![((), fields)])
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let const_name = sel.name;
        format!("<match-{const_name}>")
    }
}
