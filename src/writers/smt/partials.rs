use std::collections::HashMap;

use crate::split::{InvocTargetData, SplitPath, SplitType};
use crate::transforms::split_partial::SplitInfo;
use crate::{package::OracleSig, types::Type};

use super::contexts::PackageInstanceContext;
use super::exprs::{SmtAnd, SmtEq2, SmtIte};
use super::{declare::declare_datatype, exprs::SmtExpr};

fn intermediate_state_piece_sort_name(
    game_name: &str,
    pkg_inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("IntermediateState_{game_name}_{pkg_inst_name}-{oracle_name}")
}

fn intermediate_state_piece_constructor_end_name(
    game_name: &str,
    pkg_inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("mk-intermediate-state-{game_name}-{pkg_inst_name}-{oracle_name}-end")
}

fn intermediate_state_piece_constructor_name(
    game_name: &str,
    pkg_inst_name: &str,
    oracle_name: &str,
    path_str: &str,
) -> String {
    format!("mk-intermediate-state-{game_name}-{pkg_inst_name}-{oracle_name}-{path_str}")
}

fn intermediate_state_piece_selector_child_name(
    game_name: &str,
    pkg_inst_name: &str,
    oracle_name: &str,
    path_str: &str,
) -> String {
    format!("intermediate-state-{game_name}-{pkg_inst_name}-{oracle_name}-{path_str}-child")
}

fn intermediate_state_piece_selector_arg_name(
    game_name: &str,
    pkg_inst_name: &str,
    oracle_name: &str,
    path_str: &str,
    arg_name: &str,
) -> String {
    format!(
        "intermediate-state-{game_name}-{pkg_inst_name}-{oracle_name}-{path_str}-arg-{arg_name}"
    )
}

fn intermediate_state_piece_selector_local_name(
    game_name: &str,
    pkg_inst_name: &str,
    oracle_name: &str,
    path_str: &str,
    local_name: &str,
) -> String {
    format!("intermediate-state-{game_name}-{pkg_inst_name}-{oracle_name}-{path_str}-local-{local_name}")
}

// these are just the arg-x part, withpout the full oracle and package instance and game name up front

fn intermediate_state_piece_selector_child_match_name() -> String {
    format!("match-child")
}

fn intermediate_state_piece_selector_arg_match_name(arg_name: &str) -> String {
    format!("match-arg-{arg_name}")
}

fn intermediate_state_piece_selector_local_match_name(local_name: &str) -> String {
    format!("match-local-{local_name}")
}

fn partial_function_arg_intermediate_state_name() -> String {
    format!("partial-arg:intermediate-state")
}

#[derive(Debug, Clone)]
struct DatatypeDefinition {
    pub sort_name: String,
    pub constructors: Vec<(String, Vec<(String, SmtExpr)>)>,
}

#[derive(Debug, Clone)]
pub(crate) struct PartialsDatatype {
    pub pkg_inst_name: String,
    pub real_oracle_sig: OracleSig,
    pub partial_steps: Vec<PartialStep>,
}

#[derive(Debug, Clone)]
pub(crate) struct PartialStep {
    path: SplitPath,
    locals: Vec<(String, Type)>,
}

#[derive(Debug, Clone)]
pub(crate) struct OracleSplitInfo {
    oracle_sig: OracleSig,
    parts: Vec<(String, OraclePartSplitInfo)>,
}

#[derive(Debug, Clone)]
pub(crate) struct OraclePartSplitInfo {
    partial_oracle_sig: OracleSig,
    locals: Vec<(String, Type)>,
    invocation_target: Option<SmtExpr>,
}

pub(crate) fn into_partial_dtypes(splits: &SplitInfo) -> Vec<PartialsDatatype> {
    let mut map: HashMap<_, Vec<_>> = HashMap::new();

    for entry in splits {
        map.entry(entry.original_sig()).or_default().push(entry);
    }

    let mut out = vec![];

    for (real_oracle_sig, entries) in map {
        let partials_dt = PartialsDatatype {
            pkg_inst_name: entries[0].pkg_inst_name().to_string(),
            real_oracle_sig: real_oracle_sig.clone(),
            partial_steps: entries
                .iter()
                .map(|entry| PartialStep {
                    path: entry.path().clone(),
                    locals: entry.locals().clone(),
                })
                .collect(),
        };
        out.push(partials_dt);
    }

    out
}

impl PartialStep {
    fn has_child(&self) -> bool {
        matches!(self.path.split_type(), Some(SplitType::Invoc(_)))
    }

    fn child_sort(&self, game_name: &str) -> Option<String> {
        if let Some(SplitType::Invoc(target_data)) = self.path.split_type() {
            let InvocTargetData {
                pkg_inst_name,
                oracle_name,
            } = target_data;

            Some(intermediate_state_piece_sort_name(
                game_name,
                pkg_inst_name,
                oracle_name,
            ))
        } else {
            None
        }
    }
}

enum SelectorType {
    Arg,
    Local,
    Child,
}

trait NameMapper {
    type Constructor;
    type Selector;

    fn map(&self, data: &PartialsDatatype) -> Vec<(Self::Constructor, Vec<Self::Selector>)> {
        data.partial_steps
            .iter()
            .map(|partial| {
                let constructor = self.constructor(&partial.path);
                let mut selectors = vec![];

                for (arg_name, arg_type) in &data.real_oracle_sig.args {
                    selectors.push(self.arg(&partial.path, arg_type.into(), &arg_name))
                }
                for (local_name, local_type) in &partial.locals {
                    selectors.push(self.local(&partial.path, local_type.into(), &local_name))
                }

                if partial.has_child() {
                    selectors.push(self.child(&partial.path))
                }

                (constructor, selectors)
            })
            .chain(vec![(self.end(), vec![])].into_iter())
            .collect()
    }

    fn arg(&self, path: &SplitPath, sort: SmtExpr, arg_name: &str) -> Self::Selector;
    fn local(&self, path: &SplitPath, sort: SmtExpr, local_name: &str) -> Self::Selector;
    fn child(&self, path: &SplitPath) -> Self::Selector;
    fn end(&self) -> Self::Constructor;
    fn constructor(&self, path: &SplitPath) -> Self::Constructor;
}

struct DeclareDatatypeNameMapper<'a> {
    game_name: &'a str,
    pkg_inst_name: &'a str,
    oracle_name: &'a str,
}

impl<'a> NameMapper for DeclareDatatypeNameMapper<'a> {
    type Constructor = String;
    type Selector = (String, SmtExpr);

    fn arg(&self, path: &SplitPath, sort: SmtExpr, arg_name: &str) -> Self::Selector {
        let path_str = path.smt_name();
        (
            intermediate_state_piece_selector_arg_name(
                self.game_name,
                self.pkg_inst_name,
                self.oracle_name,
                &path_str,
                arg_name,
            ),
            sort,
        )
    }

    fn local(&self, path: &SplitPath, sort: SmtExpr, local_name: &str) -> Self::Selector {
        let path_str = path.smt_name();
        (
            intermediate_state_piece_selector_local_name(
                self.game_name,
                self.pkg_inst_name,
                self.oracle_name,
                &path_str,
                local_name,
            ),
            sort,
        )
    }

    fn child(&self, path: &SplitPath) -> Self::Selector {
        let name = intermediate_state_piece_selector_child_name(
            self.game_name,
            self.pkg_inst_name,
            self.oracle_name,
            &path.smt_name(),
        );
        let sort = intermediate_state_piece_sort_name(
            &self.game_name,
            &self.pkg_inst_name,
            &self.oracle_name,
        );
        (name, sort.into())
    }

    fn end(&self) -> Self::Constructor {
        intermediate_state_piece_constructor_end_name(
            self.game_name,
            self.pkg_inst_name,
            self.oracle_name,
        )
    }

    fn constructor(&self, path: &SplitPath) -> Self::Constructor {
        let path_str = path.smt_name();
        intermediate_state_piece_constructor_name(
            self.game_name,
            self.pkg_inst_name,
            self.oracle_name,
            &path_str,
        )
    }
}

struct MatchBlockMapper<'a> {
    game_name: &'a str,
    pkg_inst_name: &'a str,
    oracle_name: &'a str,
}

impl<'a> NameMapper for MatchBlockMapper<'a> {
    type Constructor = (String, Option<String>);
    type Selector = String;

    fn arg(&self, path: &SplitPath, sort: SmtExpr, arg_name: &str) -> Self::Selector {
        intermediate_state_piece_selector_arg_match_name(arg_name)
    }

    fn local(&self, path: &SplitPath, sort: SmtExpr, local_name: &str) -> Self::Selector {
        intermediate_state_piece_selector_local_match_name(local_name)
    }

    fn child(&self, path: &SplitPath) -> Self::Selector {
        intermediate_state_piece_selector_child_match_name()
    }

    fn constructor(&self, path: &SplitPath) -> Self::Constructor {
        let path_str = path.smt_name();
        let constructor_name = intermediate_state_piece_constructor_name(
            self.game_name,
            self.pkg_inst_name,
            self.oracle_name,
            &path_str,
        );

        let target_oracle_name = super::names::oracle_function_name(
            self.game_name,
            self.pkg_inst_name,
            &path.smt_name(),
        );

        (constructor_name, Some(target_oracle_name))
    }

    fn end(&self) -> Self::Constructor {
        let constructor_name = intermediate_state_piece_constructor_end_name(
            self.game_name,
            self.pkg_inst_name,
            self.oracle_name,
        );

        (constructor_name, None)
    }
}

/*
 *
 * [
 *   (Foo [ bar baz boo])
 *   (Bar [ foo bla blubb])
 * ]
 *
 * (match expr (  ( /pattern/   /body/ )*  )   )
 *             -----------------------------
 *             ^^^
 *
 * we want /pattern/ and /body/
 *
 * and /pattern/ is a constructor
 *
 *
 *
 * How //do// we know what to put into the block?
 *
 * - call the correct oracle
 * - how do we generate the function name of the correct oracle?
 *
 * */

use super::patterns::*;

struct SmtDefineFunction<B: Into<SmtExpr>> {
    name: String,
    args: Vec<(String, SmtExpr)>,
    ret_sort: SmtExpr,
    body: B,
}

impl<B: Into<SmtExpr>> Into<SmtExpr> for SmtDefineFunction<B> {
    fn into(self) -> SmtExpr {
        (
            "define-fun",
            self.name,
            {
                let args: Vec<_> = self
                    .args
                    .into_iter()
                    .map(|arg_spec| arg_spec.into())
                    .collect();

                SmtExpr::List(args)
            },
            self.ret_sort,
            self.body,
        )
            .into()
    }
}

impl<'a> PackageInstanceContext<'a> {
    pub(crate) fn smt_declare_intermediate_state(&self, datatype: &PartialsDatatype) -> SmtExpr {
        let game_ctx = self.game_ctx();
        let game_name = &game_ctx.game().name;
        let pkg_inst_name = &self.pkg_inst_name();
        let oracle_name = &datatype.real_oracle_sig.name;

        let sort_name = intermediate_state_piece_sort_name(game_name, pkg_inst_name, oracle_name);

        let intermediate_state_begin_pattern = DatastructurePattern::IntermediateState {
            game_name,
            pkg_inst_name,
            oracle_name,
            variant_name: DatastructurePattern::CONSTRUCTOR_INTERMEDIATE_STATE_BEGIN,
        };

        let intermediate_state_end_pattern = DatastructurePattern::IntermediateState {
            game_name,
            pkg_inst_name,
            oracle_name,
            variant_name: DatastructurePattern::CONSTRUCTOR_INTERMEDIATE_STATE_END,
        };

        let last_step = datatype.partial_steps.last().unwrap();
        // path x oracle name x pkg_inst_ctx -> oracle_def
        let return_pattern = DatastructurePattern::Return {
            game_name,
            pkg_inst_name,
            oracle_name,
            is_abort: false,
        };

        let constructors = DeclareDatatypeNameMapper {
            game_name,
            pkg_inst_name,
            oracle_name,
        }
        .map(&datatype);

        let begin_constructor = (intermediate_state_begin_pattern.constructor_name(), vec![]);
        let end_constructor = (
            intermediate_state_end_pattern.constructor_name(),
            vec![(
                intermediate_state_end_pattern.selector_name(
                    DatastructurePattern::SELECTOR_INTERMEDIATE_STATE_END_RETURN_VALUE,
                ),
                return_pattern.sort_name().into(),
            )],
        );

        declare_datatype(
            &sort_name,
            constructors
                .into_iter()
                .chain(vec![begin_constructor, end_constructor].into_iter()),
        )
    }

    fn check_args_are_honest<B: Into<SmtExpr>>(&self, args: &[(String, Type)], body: B) -> SmtExpr {
        if args.is_empty() {
            return body.into();
        }

        SmtIte {
            cond: SmtAnd(
                args.into_iter()
                    .map(|(arg_name, _)| {
                        let lhs = arg_name.clone(); // this is just a local variable
                        let rhs = intermediate_state_piece_selector_arg_match_name(&arg_name);
                        SmtEq2 { lhs, rhs }.into()
                    })
                    .collect(),
            ),
            then: body,
            els: "TODO check_args_are_honest instantiate an error here",
        }
        .into()
    }

    pub(crate) fn smt_declare_oracle_dispatch_function(
        &self,
        datatype: &PartialsDatatype,
    ) -> SmtExpr {
        let game_ctx = self.game_ctx();
        let game_name = &game_ctx.game().name;
        let pkg_inst_name = &self.pkg_inst_name();
        let oracle_name = &datatype.real_oracle_sig.name;
        let name_mapper = MatchBlockMapper {
            game_name,
            pkg_inst_name,
            oracle_name,
        };

        let function_pattern = FunctionPattern::DispatchOracle {
            game_name,
            pkg_inst_name,
            oracle_sig: &datatype.real_oracle_sig,
        };

        let mut cases: Vec<SmtMatchCase<_>> = vec![];

        for ((cons, fun), sels) in &name_mapper.map(datatype) {
            let dispatch_call = if let Some(oracle_fun_name) = fun {
                let mut call: Vec<SmtExpr> = vec![oracle_fun_name.clone().into()];
                call.extend(sels.clone().into_iter().map(|x| x.into()));
                SmtExpr::List(call)
            } else {
                // create new return
                // keep everything as-is
                // TODO we need a new return type that also contains the partial state
                SmtExpr::Atom("src/writers/smt/partials.rs: -- search for kdsfjlsdjf -- TODO add partial return".to_string())
            };

            let oracle_args = &datatype.real_oracle_sig.args;

            let case = SmtMatchCase {
                constructor: cons.clone(),
                args: sels.clone(),
                body: self.check_args_are_honest(oracle_args, dispatch_call),
            };

            cases.push(case);
        }

        SmtDefineFunction {
            name: function_pattern.function_name(),
            args: function_pattern.function_argspec(),
            ret_sort: function_pattern.function_return_sort_name().into(),
            body: SmtMatch {
                expr: partial_function_arg_intermediate_state_name(),
                cases,
            },
        }
        .into()
    }
}

#[derive(Debug, Clone)]
struct SmtMatch<E, B>
where
    E: Into<SmtExpr> + std::fmt::Debug + Clone,
    B: Into<SmtExpr> + std::fmt::Debug + Clone,
{
    expr: E,
    cases: Vec<SmtMatchCase<B>>,
}

impl<E, B> From<SmtMatch<E, B>> for SmtExpr
where
    E: Into<SmtExpr> + std::fmt::Debug + Clone,
    B: Into<SmtExpr> + std::fmt::Debug + Clone,
{
    fn from(value: SmtMatch<E, B>) -> SmtExpr {
        let cases = value
            .cases
            .into_iter()
            .map(|case| {
                let mut pattern = vec![case.constructor.into()];
                pattern.extend(case.args.into_iter().map(|s| s.into()));

                SmtExpr::List(vec![SmtExpr::List(pattern), case.body.into()])
            })
            .collect();

        return ("match", value.expr, SmtExpr::List(cases)).into();
    }
}

#[derive(Debug, Clone)]
struct SmtMatchCase<B>
where
    B: Into<SmtExpr> + std::fmt::Debug + Clone,
{
    constructor: String,
    args: Vec<String>,
    body: B,
}
