use crate::{
    split::{SplitPath, SplitType},
    transforms::split_partial::{SplitInfo, SplitInfoEntry},
    types::Type,
    writers::smt::{declare::declare_datatype, exprs::SmtExpr},
};

use super::DatastructurePattern2;

pub struct IntermediateStatePattern<'a> {
    pub game_name: &'a str,
    pub pkg_inst_name: &'a str,
    pub oracle_name: &'a str,
}

pub enum IntermediateStateConstructor<'a> {
    Begin,
    End,
    OracleState(&'a SplitPath),
}

pub enum IntermediateStateSelector<'a> {
    Arg(&'a SplitPath, &'a str),
    LoopVar(&'a SplitPath, &'a str),
    Local(&'a SplitPath, &'a str),
    Child(&'a SplitPath),
    Return,
}

impl SplitPath {
    pub(crate) fn loopvar_selectors<'a>(&'a self) -> Vec<(&'a str, IntermediateStateSelector<'a>)> {
        let mut out = vec![];
        for elem in self.path() {
            if let SplitType::ForStep(loopvar, _, _) = elem.split_type() {
                let name = loopvar.ident_ref();
                out.push((name, IntermediateStateSelector::LoopVar(self, name)));
            }
        }

        out
    }
}

impl SplitInfoEntry {
    fn selectors(&self, game_name: &str) -> Vec<(String, SmtExpr)> {
        let path = self.path();
        let mut out = vec![];

        let pattern = IntermediateStatePattern {
            game_name,
            pkg_inst_name: self.pkg_inst_name(),
            oracle_name: &self.original_sig().name,
        };

        // loopvars
        for elem in path.path() {
            if let SplitType::ForStep(loopvar, _, _) = elem.split_type() {
                let ident = loopvar.ident();
                let sel = IntermediateStateSelector::LoopVar(path, &ident);
                let name = pattern.selector_name(&sel);
                let tipe = Type::Integer;

                out.push((name, tipe.into()))
            }
        }

        // args
        for (arg_name, arg_type) in &self.original_sig().args {
            let sel = IntermediateStateSelector::Arg(path, arg_name);
            let name = pattern.selector_name(&sel);

            out.push((name, arg_type.into()));
        }

        // locals
        for (local_name, local_type) in self.locals() {
            let sel = IntermediateStateSelector::Local(path, local_name);
            let name = pattern.selector_name(&sel);

            out.push((name, local_type.into()));
        }

        // child
        // the following line was copied from old code, not sure how correct it is
        let has_child = matches!(self.path().split_type(), Some(SplitType::Invoc(_)));
        if has_child {
            let sel = IntermediateStateSelector::Child(self.path());
            let name = pattern.selector_name(&sel);

            out.push((name, pattern.sort_name().into()))
        }

        out
    }
}

impl<'a> DatastructurePattern2 for IntermediateStatePattern<'a> {
    type Constructor = IntermediateStateConstructor<'a>;
    type Selector = IntermediateStateSelector<'a>;
    type DeclareInfo = SplitInfo;

    const CAMEL_CASE: &'static str = "IntermediateState";

    const KEBAB_CASE: &'static str = "intermediate-state";

    fn sort_name(&self) -> String {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
            ..
        } = self;
        let camel_case = Self::CAMEL_CASE;

        format!("{camel_case}-{game_name}-{pkg_inst_name}-{oracle_name}")
    }

    fn constructor_name(&self, cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
        } = self;
        let variant_name = match cons {
            IntermediateStateConstructor::Begin => "begin".to_string(),
            IntermediateStateConstructor::End => "end".to_string(),
            IntermediateStateConstructor::OracleState(path) => path.smt_name(),
        };

        format!("mk-{kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}-{variant_name}")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let Self {
            game_name,
            pkg_inst_name,
            oracle_name,
        } = self;

        let kebab_case = Self::KEBAB_CASE;
        let field_name = match sel {
            IntermediateStateSelector::Arg(path, name) => format!("{}-arg-{name}", path.smt_name()),
            IntermediateStateSelector::LoopVar(path, name) => {
                format!("{}-loopvar-{name}", path.smt_name())
            }
            IntermediateStateSelector::Local(path, name) => {
                format!("{}-local-{name}", path.smt_name())
            }
            IntermediateStateSelector::Child(path) => format!("{}-child", path.smt_name()),
            IntermediateStateSelector::Return => format!("end-return"),
        };

        format!("{kebab_case}-{game_name}-{pkg_inst_name}-{oracle_name}-{field_name}")
    }

    fn declare_datatype(&self, info: &Self::DeclareInfo) -> SmtExpr {
        let filter_fn = |entry: &&SplitInfoEntry| {
            entry.original_sig().name == self.oracle_name
                && entry.pkg_inst_name() == self.pkg_inst_name
        };

        let entries: Vec<_> = info.iter().filter(&filter_fn).collect();
        let return_type = entries[0].original_sig().tipe.clone();

        let mut constructors = vec![
            (
                self.constructor_name(&IntermediateStateConstructor::Begin),
                vec![],
            ),
            (
                self.constructor_name(&IntermediateStateConstructor::End),
                vec![(
                    self.selector_name(&IntermediateStateSelector::Return),
                    return_type.into(),
                )],
            ),
        ];

        for entry in entries {
            constructors.push((
                self.constructor_name(&IntermediateStateConstructor::OracleState(entry.path())),
                entry.selectors(&self.game_name),
            ))
        }

        declare_datatype(&self.sort_name(), constructors.into_iter())
    }
}
