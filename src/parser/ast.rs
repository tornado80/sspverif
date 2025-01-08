use pest::{iterators::Pair, Span};

use super::Rule;

#[derive(Clone, Debug)]
pub(crate) struct PackageName<'a>(Pair<'a, Rule>);

#[derive(Clone, Debug)]
pub(crate) struct PackageInstanceName<'a>(Pair<'a, Rule>);

#[derive(Clone, Debug)]
pub(crate) struct GameName<'a>(Pair<'a, Rule>);

#[derive(Clone, Debug)]
pub(crate) struct GameInstanceName<'a>(Pair<'a, Rule>);

#[derive(Clone, Debug)]
pub(crate) struct ProofName<'a>(Pair<'a, Rule>);

#[derive(Clone, Debug)]
pub(crate) struct AssumptionName<'a>(Pair<'a, Rule>);

macro_rules! impl_ast {
    ($struct:ty) => {
        impl<'a> $struct {
            pub fn new(ast: Pair<'a, $crate::parser::Rule>) -> Self {
                Self(ast)
            }
        }

        impl<'a> $crate::parser::ast::Identifier<'a> for $struct {
            fn as_str(&self) -> &'a str {
                self.0.as_str()
            }

            fn as_span(&self) -> Span<'a> {
                self.0.as_span()
            }

            fn as_pair(&self) -> &Pair<'a, Rule> {
                &self.0
            }
        }

        impl<'a> From<Pair<'a, $crate::parser::Rule>> for $struct {
            fn from(ast: Pair<'a, $crate::parser::Rule>) -> Self {
                Self::new(ast)
            }
        }
    };
}

impl_ast!(PackageName<'a>);
impl_ast!(PackageInstanceName<'a>);
impl_ast!(GameName<'a>);
impl_ast!(GameInstanceName<'a>);
impl_ast!(ProofName<'a>);
impl_ast!(AssumptionName<'a>);

pub(crate) trait Identifier<'a>:
    From<Pair<'a, crate::parser::Rule>> + std::fmt::Debug
{
    fn as_str(&self) -> &'a str;
    fn as_span(&self) -> Span<'a>;
    fn as_pair(&self) -> &Pair<'a, Rule>;
}
