use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, OracleDef, OracleSig, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::transforms::samplify::SampleInfo;
use crate::transforms::split_partial::{SplitInfo, SplitInfoEntry, SplitType};
use crate::types::Type;

use crate::writers::smt::exprs::{smt_to_string, SmtExpr, SmtIte, SmtLet};

use super::contexts::{GameContext, GlobalContext, OracleContext, PackageInstanceContext};
use super::exprs::{SmtAs, SmtEq2};
use super::{names, sorts};

pub struct CompositionSmtWriter<'a> {
    pub comp: &'a Composition,

    sample_info: &'a SampleInfo,
    split_info: &'a SplitInfo,
}

impl<'a> CompositionSmtWriter<'a> {
    pub fn new(
        comp: &'a Composition,
        sample_info: &'a SampleInfo,
        split_info: &'a SplitInfo,
    ) -> CompositionSmtWriter<'a> {
        CompositionSmtWriter {
            comp,
            sample_info,
            split_info,
        }
    }

    fn get_game_context(&self) -> GameContext<'a> {
        GameContext::new(self.comp)
    }

    fn get_package_instance_context(&self, inst_name: &str) -> Option<PackageInstanceContext<'a>> {
        self.get_game_context().pkg_inst_ctx_by_name(inst_name)
    }

    fn get_oracle_context(&self, inst_name: &str, oracle_name: &str) -> Option<OracleContext<'a>> {
        self.get_package_instance_context(inst_name)?
            .oracle_ctx_by_name(oracle_name)
    }

    fn get_randomness(&self, sample_id: usize) -> Option<SmtExpr> {
        let game_context = self.get_game_context();
        let gamestate = (
            "select",
            names::var_globalstate_name(),
            names::var_state_length_name(),
        );

        game_context.smt_access_gamestate_rand(self.sample_info, gamestate, sample_id)
    }

    // builds a single (declare-datatype ...) expression for package instance `inst`
    fn smt_pkg_state(&self, inst: &PackageInstance) -> SmtExpr {
        self.get_package_instance_context(&inst.name)
            .expect(&format!(
                "game {} does not contain package instance with name {}",
                self.comp.name, &inst.name
            ))
            .smt_declare_pkgstate()
    }

    // build the (declare-datatype ...) expressions for all package states and the joint composition state
    pub fn smt_composition_state(&self) -> Vec<SmtExpr> {
        // 1. each package in composition
        let mut states: Vec<SmtExpr> = self
            .comp
            .pkgs
            .clone()
            .iter()
            .map(|pkg| self.smt_pkg_state(pkg))
            .collect();

        states.push(
            self.get_game_context()
                .smt_declare_gamestate(self.sample_info),
        );

        states
    }

    pub fn smt_sort_return(&self, inst_name: &str, oracle_name: &str) -> SmtExpr {
        names::return_sort_name(&self.comp.name, inst_name, oracle_name).into()
    }

    pub fn smt_sort_composition_state(&self) -> SmtExpr {
        names::gamestate_sort_name(&self.comp.name).into()
    }

    fn smt_pkg_return(&self, inst: &PackageInstance) -> Vec<SmtExpr> {
        let pkg_inst_ctx = self.get_package_instance_context(&inst.name).unwrap();

        inst.get_oracle_sigs()
            .iter()
            .map(|osig| {
                pkg_inst_ctx
                    .oracle_ctx_by_name(&osig.name)
                    .unwrap()
                    .smt_declare_return()
            })
            .collect()
    }

    pub fn smt_composition_return(&self) -> Vec<SmtExpr> {
        self.comp
            .pkgs
            .clone()
            .iter()
            .flat_map(|inst| self.smt_pkg_return(inst))
            .collect()
    }

    fn code_smt_helper(
        &self,
        block: CodeBlock,
        odef: &OracleDef,
        inst: &PackageInstance,
    ) -> SmtExpr {
        let PackageInstance {
            name: inst_name, ..
        } = inst;
        let OracleDef {
            is_split,
            sig:
                OracleSig {
                    tipe: oracle_return_tipe,
                    name: oracle_name,
                    ..
                },
            ..
        } = odef;

        let game_context = self.get_game_context();
        let oracle_context = self.get_oracle_context(&inst.name, &oracle_name).unwrap();

        let game_name = &game_context.game().name;
        let pkg_inst_name = oracle_context.pkg_inst_ctx().pkg_inst_name();
        let oracle_name = &oracle_context.oracle_def().sig.name;

        let mut result = None;

        let split_info_entry = self.split_info.iter().find(|entry| {
            entry.pkg_inst_name() == pkg_inst_name && entry.oracle_name() == oracle_name
        });
        if *is_split {
            println!("xxxxxx");
            println!("game name: {game_name}");
            println!("split_info: {:#?}", self.split_info);
        }

        assert_eq!(
            *is_split,
            split_info_entry.is_some(),
            "is_split != split_info_entry.is_some. \n\t pkg_inst_name:{pkg_inst_name} \n\t oracle_name:{oracle_name}",
        );

        for stmt in block.0.iter().rev() {
            result = Some(match stmt {
                Statement::IfThenElse(cond, ifcode, elsecode) => SmtIte {
                    cond: cond.clone(),
                    then: self.code_smt_helper(ifcode.clone(), odef, inst),
                    els: self.code_smt_helper(elsecode.clone(), odef, inst),
                }
                .into(),
                Statement::For(_, _, _, _) => unreachable!("found a for statement in the smt writer stage. this should have been eliminated by now and can't be handled here. {}.{}({}).{}", self.comp.name, inst_name, inst.pkg.name, oracle_name),
                Statement::Return(None) => {
                    // (mk-return-{name} statevarname expr)
                    let var_gamestates = names::var_globalstate_name();
                    let old_gamestate = GlobalContext::smt_latest_gamestate();
                    let var_selfstate = names::var_selfstate_name();
                    let new_gamestate = game_context
                        .smt_update_gamestate_pkgstate(
                            old_gamestate,
                            self.sample_info,
                            &inst.name,
                            var_selfstate,
                        )
                        .unwrap();


                    /* TODO: for parent we need to do one of the following things:
                     *
                     * Claim by Christoph: same as below but we *need*
                     * to ignore for/if: it should be possible to
                     * *write* variables that already exist outside
                     * (so we can't discard updates from within the
                     * loop)
                     * 
                     * i <- 3
                     * for ...
                     *   i <- 5
                     * i // should be 5
                     *
                     * and while *local* variables from within the
                     * loops should be gone, the typechecker should
                     * have made sure no unallowerd access happens.
                     *
                     * Jan's clean solution would be to *copy* the new
                     * values selectively and indeed have a separate
                     * scope for for/if/..
                     *
                     **********************************************
                     * Old understanding
                     *
                     * - if we *invoke* an oracle we need to put our
                     *   *current*, updated state in the parent and
                     *   create an *empty* intermediate state for the
                     *   child
                     *
                     * - if we *return* from an oracle we need to
                     *   discard the current intermediate state and
                     *   restore parent
                     *
                     * - same for entering/leaving for loops (though
                     *   not an empty new state) -- should match the
                     *   type checker and maybe also be added to the
                     *   (user facing) documentation
                     *   Detection: (else)next is a ForStep/.. and
                     *              shares parent with the current
                     *              state
                     *
                     * - what about ifs?
                     */

                    let new_gamestate = if let Some(entry) = split_info_entry {
                        // We are in a partial function!
                        //
                        // what now?
                        // -> construct next partial state!
                        //    what is the next parent?
                        //    enter function: push!
                        //    leave function: pop!
                        //    else:           copy!
                        //
                        // complications:
                        // - next or elsenext?
                        // - what if we leave multiple functions at once?
                        //   - this can't happen: after an invoc there definitely is a plain block
                        //     with a return statement
                        //     - TODO: partial_split transform: make sure there the is a return if
                        //             invoc is last statement
                        // - we also can't leave and enter at the same time
                        //
                        // so: same as determine_next, but return actual smt expression for the
                        // next partial state?
                        // - find common prefix path
                        // - pop path until common prefix
                        //   - match popped path element
                        //     - plain: skip
                        //     - ifcond:
                        //     - ifbranch
                        //     - elsebranch
                        //     - invoc
                        //     - forstep
                        // - go down to next
                        //







                        if let Some(next_path) = entry.next() {
                            let (_, parent) = entry.path().basename();
                            if next_path.has_prefix(&parent) {
                                if matches!(next_path.path()[parent.len()].split_type(),
                                            SplitType::ForStep(_,_,_)) {
                                    // We are about to enter a for loop!
                                    // parent is current intermediate state
                                }
                            }


                            /*
                             * problem: `parent` is an empty string, but should
                             * be the smt expression of the parent intermediate state
                             *
                             * possible outputs:
                             * - our parent (we stay at current level)
                             * - our grandparent (we move up the stack )
                             * - 
                             *
                             * /forstep -- parent: /
                             * /invoc:foo/forstepi123/plain -- parent invoc:foo
                             * /invoc:foo/plain -- 
                             *
                             * ---
                             *
                             * what do we use the stack for?
                             *
                             * - Christoph's claim:
                             *   "the stack is only used for oracle invocations"
                             *
                             * - Jan's intuition:
                             *   "at every step between partial functions, we "
                             * 
                             *
                             * */
                            let parent = match next_path.split_type().unwrap() {
                                SplitType::Plain => "",
                                SplitType::Invoc => todo!(),
                                SplitType::ForStep(_, _, _) => todo!(),
                                SplitType::IfCondition(_) => todo!(),
                                SplitType::IfBranch => todo!(),
                                SplitType::ElseBranch => todo!(),
                            };

                            let new_intermediate_state =
                                oracle_context
                                .smt_construct_next_intermediate_state(self.split_info, parent).unwrap();
                            let new_gamestate =
                                game_context
                                .smt_update_gamestate_intermediate_state(new_gamestate, self.sample_info, new_intermediate_state).unwrap();
                            new_gamestate
                        } else {
                            new_gamestate
                        }
                    }  else {
                        new_gamestate
                    };

                    let some_empty = ("mk-some", "mk-empty");
                    let var_state_len = names::var_state_length_name();
                    let body = oracle_context.smt_construct_return(
                        var_gamestates,
                        var_state_len,
                        some_empty,
                        "false",
                    );

                    game_context.smt_push_global_gamestate(new_gamestate, body)
                }
                Statement::Return(Some(expr)) => {
                    // (mk-return-{name} statevarname expr)

                    let var_gamestates = names::var_globalstate_name();
                    let old_gamestate = GlobalContext::smt_latest_gamestate();
                    let var_selfstate = names::var_selfstate_name();
                    let new_gamestate = game_context
                        .smt_update_gamestate_pkgstate(
                            old_gamestate,
                            self.sample_info,
                            &inst.name,
                            var_selfstate,
                        )
                        .unwrap();

                    let var_state_len = names::var_state_length_name();
                    let body = oracle_context.smt_construct_return(
                        var_gamestates,
                        var_state_len,
                        Expression::Some(Box::new(expr.clone())),
                        "false",
                    );

                    game_context.smt_push_global_gamestate(new_gamestate, body)
                }
                Statement::Abort => {
                    // mk-abort-{name}

                    let var_gamestates = names::var_globalstate_name();
                    let old_gamestate = GlobalContext::smt_latest_gamestate();
                    let var_selfstate = names::var_selfstate_name();
                    let var_state_len = names::var_state_length_name();

                    let new_gamestate = game_context
                        .smt_update_gamestate_pkgstate(
                            old_gamestate,
                            self.sample_info,
                            &inst.name,
                            var_selfstate,
                        )
                        .unwrap();

                    let none = Expression::None(oracle_return_tipe.clone());
                    let body = oracle_context.smt_construct_return(
                        var_gamestates,
                        var_state_len,
                        none,
                        "true",
                    );

                    game_context.smt_push_global_gamestate(new_gamestate, body)
                }
                // TODO actually use the type that we sample to know how far to advance the randomness tape
                Statement::Sample(ident, opt_idx, sample_id, tipe) => {
                    /*
                     *   1. get counter
                     *   2. assign ident
                     *   3. overwrite state
                     *   4. continue
                     *
                     * let
                     *   ident = sample(ctr)
                     *   __global = mk-compositionState ( mk-randomndess-state (ctr + 1) ... )
                     *
                     *
                     * ,
                     *   let (ident = rand(access(counter)) (
                     *       // TODO update this to the new context-based helpers structure
                     *       comp_helper.smt_set(counter, counter+1, body)
                     * ))
                     * )
                     *
                     */
                    let sample_id = sample_id.expect("found a None sample_id");

                    // ctr is the current "i-th sampling for sample id sample_id"
                    let ctr = self.get_randomness(sample_id).unwrap_or_else(|| {
                        let max_known_sample_id = self.sample_info.count;
                        panic!(
                            "found sample id {} that exceeds highest expected {}",
                            sample_id, max_known_sample_id
                        )
                    });

                    let rand_fn_name = names::fn_sample_rand_name(&self.comp.name, tipe);

                    let rand_val: SmtExpr =
                        (rand_fn_name, format!("{sample_id}"), ctr.clone()).into();

                    let new_val = if let Some(idx) = opt_idx {
                        (
                            "store",
                            ident.to_expression(),
                            idx.clone(),
                            rand_val.clone(),
                        )
                            .into()
                    } else {
                        rand_val
                    };

                    let bindings = vec![(ident.ident(), new_val)]
                        .into_iter()
                        .filter(|(x, _)| x != "_")
                        .collect();

                    let cur_gamestate = GlobalContext::smt_latest_gamestate();
                    let new_gamestate = game_context
                        .smt_increment_gamestate_rand(cur_gamestate, self.sample_info, sample_id)
                        .unwrap();

                    SmtLet {
                        bindings,
                        body: game_context
                            .smt_overwrite_latest_global_gamestate(new_gamestate, result.unwrap()),
                    }
                    .into()
                }
                Statement::Parse(idents, expr) => {
                    let bindings = idents
                        .iter()
                        .filter(|ident| ident.ident() != "_")
                        .enumerate()
                        .map(|(i, ident)| {
                            let ident = if let Identifier::Local(ident) = ident {
                                ident
                            } else {
                                unreachable!()
                            };

                            (ident.clone(), (format!("el{}", i + 1), expr.clone()).into())
                        })
                        .collect();

                    SmtLet {
                        bindings,
                        body: result.unwrap(),
                    }
                    .into()
                }
                Statement::InvokeOracle {
                    target_inst_name: None,
                    ..
                } => {
                    panic!("found an unresolved oracle invocation: {:#?}", stmt);
                }
                Statement::InvokeOracle { tipe: None, .. } => {
                    panic!("found an unresolved oracle invocation: {:#?}", stmt);
                }
                Statement::InvokeOracle {
                    id,
                    opt_idx,
                    name,
                    args,
                    target_inst_name: Some(target),
                    tipe: Some(_),
                } => {
                    println!("target:{target}, oraclename:{name:?}, game_name:{:?}", self.get_game_context().game().name);
                    println!("taget:{:?}",self.get_package_instance_context(target).unwrap().pkg_inst_name());
                    println!("taget:{:?}",
                             self.get_package_instance_context(target).unwrap().pkg_inst().pkg.oracles.iter().map(|OracleDef{sig,..}| sig.name.clone()).collect::<Vec<_>>());
                    let called_oracle_context = self.get_oracle_context(target, name).unwrap();
                    let this_oracle_context =
                        self.get_oracle_context(&inst.name, oracle_name).unwrap();

                    let game_context = self.get_game_context();
                    let then_body = game_context.smt_push_global_gamestate(
                        game_context
                            .smt_update_gamestate_pkgstate(
                                GlobalContext::smt_latest_gamestate(),
                                self.sample_info,
                                &inst.name,
                                names::var_selfstate_name(),
                            )
                            .unwrap(),
                        this_oracle_context.smt_construct_abort(
                            names::var_globalstate_name(),
                            names::var_state_length_name(),
                        ),
                    );

                    let let_bindings = vec![
                        (
                            names::var_globalstate_name(),
                            called_oracle_context.smt_access_return_state(names::var_ret_name()),
                        )
                            .into(),
                        (
                            names::var_state_length_name(),
                            called_oracle_context
                                .smt_access_return_state_length(names::var_ret_name()),
                        )
                            .into(),
                    ];

                    let smt_expr = SmtLet {
                        bindings: vec![(names::var_ret_name(), {
                            let mut cmdline = vec![
                                names::oracle_function_name(&self.comp.name, target, name).into(),
                                names::var_globalstate_name().into(),
                                names::var_state_length_name().into(),
                            ];

                            for arg in args {
                                cmdline.push(arg.clone().into())
                            }

                            SmtExpr::List(cmdline)
                        })],
                        body: SmtIte {
                            cond: called_oracle_context
                                .smt_access_return_is_abort(names::var_ret_name()),
                            then: SmtLet {
                                bindings: let_bindings.clone(),
                                body: then_body,
                            },
                            els: SmtLet {
                                bindings: {
                                    let mut bindings = let_bindings.clone();

                                    if id.ident() != "_" {
                                        bindings.push((
                                            id.ident(),
                                            SmtExpr::List(vec![
                                                SmtExpr::Atom("maybe-get".into()),
                                                called_oracle_context
                                                    .smt_access_return_value(names::var_ret_name()),
                                            ]),
                                        ));
                                    }

                                    bindings
                                },
                                body: result.unwrap(),
                            },
                        },
                    };

                    if opt_idx.is_some() {
                        (
                            "store",
                            id.to_expression(),
                            opt_idx.clone().unwrap(),
                            smt_expr,
                        )
                            .into()
                    } else {
                        smt_expr.into()
                    }
                }
                Statement::Assign(ident, opt_idx, expr) => {
                    let inst_context = self.get_package_instance_context(&inst.name).unwrap();
                    let oracle_context = self.get_oracle_context(&inst.name, oracle_name).unwrap();

                    let (t, inner) = if let Expression::Typed(t, i) = expr {
                        (t.clone(), *i.clone())
                    } else {
                        unreachable!("we expect that this is typed")
                    };

                    //eprintln!(r#"DEBUG code_smt_helper Assign {expr:?} to identifier {ident:?}")"#);

                    // first build the unwrap expression, if we have to
                    let outexpr = if let Expression::Unwrap(inner) = &inner {
                        ("maybe-get", *inner.clone()).into()
                    } else {
                        expr.clone().into() // TODO maybe this should be inner??
                    };

                    // then build the table store smt expression, in case we have to
                    let outexpr = if let Some(idx) = opt_idx {
                        let oldvalue = match &ident {
                            &Identifier::State {
                                name,
                                ..
                            } => {
                                //assert_eq!(pkgname, inst_name, "failed assertion: in an oracle in instance {inst_name} I found a state identifier with {pkgname}. I assumed these would always be equal.");
                                inst_context
                                    .smt_access_pkgstate(names::var_selfstate_name(), name)
                                    .unwrap()
                            }
                            Identifier::Local(_) => ident.to_expression().into(),
                            _ => {
                                unreachable!("")
                            }
                        };

                        ("store", oldvalue, idx.clone(), outexpr).into()
                    } else {
                        outexpr
                    };

                    // build the actual smt assignment
                    let smtout = match ident {
                        Identifier::State {
                            name,
                            ..
                        } => {
                            //assert_eq!(pkgname, inst_name, "failed assertion: in an oracle in instance {inst_name} I found a state identifier with {pkgname}. I assumed these would always be equal.");
                            SmtLet {
                                bindings: vec![(
                                    names::var_selfstate_name(),
                                    inst_context
                                        .smt_update_pkgstate(
                                            names::var_selfstate_name(),
                                            name,
                                            outexpr,
                                        )
                                        .unwrap()
                                        .into(),
                                )],
                                body: result.unwrap(),
                            }
                        }

                        Identifier::Local(name) => SmtLet {
                            bindings: vec![(name.clone(), outexpr)]
                                .into_iter()
                                .filter(|(name, _)| name != "_:")
                                .collect(),
                            body: result.unwrap(),
                        },

                        _ => {
                            unreachable!("can't assign to {:#?}", ident)
                        }
                    };

                    // if it's an unwrap, also wrap it with the unwrap check.
                    // TODO: are we sure we don't want to deconstruct `inner` here?
                    // it seems impossible to me that expr ever matches here,
                    // because above we make sure it's an Expression::Typed.
                    if let Expression::Unwrap(inner) = inner {
                        SmtIte {
                            cond: SmtEq2 {
                                lhs: *inner.clone(),
                                rhs: SmtAs {
                                    name: "mk-none".into(),
                                    tipe: Type::Maybe(Box::new(t)),
                                },
                            },
                            then: oracle_context.smt_construct_abort(
                                names::var_globalstate_name(),
                                names::var_state_length_name(),
                            ),
                            els: smtout,
                        }
                        .into()
                    } else {
                        smtout.into()
                    }
                }
            });
        }
        result.unwrap()
    }

    fn smt_next_gamestate<S: Into<SmtExpr>>(
        oracle_ctx: &OracleContext,
        entry: &SplitInfoEntry,
        ret_stmt: &Statement,
        old_gamestate: S,
    ) {
        let oracle_name = &oracle_ctx.oracle_def().sig.name;
        let pkg_inst_name = oracle_ctx.pkg_inst_ctx().pkg_inst_name();

        let mut cur_path = entry.path();

        // we need to figure out the gamestates for both next and elsenext

        let shared_prefix_next = entry
            .next()
            .map(|next| cur_path.longest_shared_prefix(next));

        let shared_prefix_elsenext = entry
            .elsenext()
            .map(|next| cur_path.longest_shared_prefix(next));

        let shared_prefix_next = match shared_prefix_next {
            None => return oracle_ctx.smt_access_intermeditate_parent(old_gamestate),
            Some(x) => x,
        };

        // We are in a partial function!
        //
        // what now?
        // -> construct next partial state!
        //    what is the next parent?
        //    enter function: push!
        //    leave function: pop!
        //    else:           copy!
        //
        // complications:
        // - next or elsenext?
        // - what if we leave multiple functions at once?
        //   - this can't happen: after an invoc there definitely is a plain block
        //     with a return statement
        //     - TODO: partial_split transform: make sure there the is a return if
        //             invoc is last statement
        // - we also can't leave and enter at the same time
        //
        // so: same as determine_next, but return actual smt expression for the
        // next partial state?
        // - find common prefix path
        // - pop path until common prefix
        //   - match popped path element
        //     - plain: skip
        //     - ifcond:
        //     - ifbranch
        //     - elsebranch
        //     - invoc
        //     - forstep
        // - go down to next
        //
    }

    /* example
        (define-fun
            stored_key_equals_k
            ((state_all State_composition) (k Key))
            Return_stored-key-equals-k
            (let
                (state_key (state-composition-key state_all))
                (mk-stored-key-equals-k
                    state-all
                    (=
                        (state-key-k state_key)
                        k
                    )
                )
            )
        )
    */

    fn smt_define_oracle_fn(&self, inst: &PackageInstance, def: &OracleDef) -> SmtExpr {
        let code = &def.code;
        let mut args = vec![
            (
                names::var_globalstate_name(),
                sorts::Array {
                    key: crate::types::Type::Integer,
                    value: names::gamestate_sort_name(&self.comp.name),
                },
            )
                .into(),
            (names::var_state_length_name(), crate::types::Type::Integer).into(),
        ];

        let rest_args = def.sig.args.iter().cloned().map(|arg| arg.into());
        args.extend(rest_args);

        let game_name = &self.comp.name;
        let inst_name = &inst.name;
        let oracle_name = &def.sig.name;

        let game_context = GameContext::new(&self.comp);

        let partial_state = game_context.smt_access_gamestate_intermediate_state((
            "select",
            names::var_globalstate_name(),
            names::var_state_length_name(),
        ));

        (
            "define-fun",
            names::oracle_function_name(game_name, inst_name, oracle_name),
            SmtExpr::List(args.clone()),
            names::return_sort_name(game_name, inst_name, oracle_name),
            SmtLet {
                bindings: def
                    .sig
                    .partial_vars
                    .iter()
                    .map(|(name, _type)| {
                        (
                            name.clone(),
                            (
                                names::intermediate_state_selector_local(
                                    game_name,
                                    oracle_name,
                                    name,
                                ),
                                partial_state.clone(),
                            )
                                .into(),
                        )
                    })
                    .chain(vec![(
                        names::var_selfstate_name(),
                        game_context
                            .smt_access_gamestate_pkgstate(
                                (
                                    "select",
                                    names::var_globalstate_name(),
                                    names::var_state_length_name(),
                                ),
                                inst_name,
                            )
                            .unwrap(),
                    )])
                    .collect(),
                body: self.code_smt_helper(code.clone(), &def, inst),
            },
        )
            .into()
    }

    fn smt_pkg_code(&self, inst: &PackageInstance) -> Vec<SmtExpr> {
        inst.pkg
            .oracles
            .iter()
            .map(|def| self.smt_define_oracle_fn(inst, def))
            .collect()
    }

    fn smt_composition_code(&self) -> Vec<SmtExpr> {
        let comment = vec![SmtExpr::Comment(format!(
            "Composition of {}\n",
            self.comp.name
        ))];
        let ordered_pkgs = self.comp.ordered_pkgs();
        let code = ordered_pkgs.iter().flat_map(|inst| self.smt_pkg_code(inst));

        comment.into_iter().chain(code).collect()
    }

    fn smt_composition_paramfuncs(&self) -> Vec<SmtExpr> {
        let fns = self
            .comp
            .consts
            .iter()
            .filter(|(_, tipe)| matches!(tipe, Type::Fn(_, _)));
        let comp_name = &self.comp.name;

        let mut funcs = vec![];

        for (name, tipe) in fns {
            let (arg_types, ret_type) = if let Type::Fn(arg_types, ret_type) = tipe {
                (arg_types, ret_type)
            } else {
                unreachable!()
            };

            let arg_types: SmtExpr = arg_types
                .iter()
                .map(|tipe| tipe.clone().into())
                .collect::<Vec<SmtExpr>>()
                .into();

            funcs.push(
                (
                    "declare-fun",
                    format!("__func-{comp_name}-{name}"),
                    arg_types,
                    (**ret_type).clone(),
                )
                    .into(),
            )
        }
        funcs.sort();
        funcs
    }

    fn smt_composition_randomness(&mut self) -> Vec<SmtExpr> {
        let mut result: Vec<_> = self
            .sample_info
            .tipes
            .iter()
            .map(|tipe| {
                let tipeexpr: SmtExpr = tipe.clone().into();

                (
                    "declare-fun",
                    format!(
                        "__sample-rand-{}-{}",
                        self.comp.name,
                        smt_to_string(tipeexpr.clone())
                    ),
                    (SmtExpr::Atom("Int".into()), SmtExpr::Atom("Int".into())),
                    tipeexpr,
                )
                    .into()
            })
            .collect();
        result.sort();
        result
    }

    pub fn smt_composition_all(&mut self) -> Vec<SmtExpr> {
        let rand = self.smt_composition_randomness();
        let paramfuncs = self.smt_composition_paramfuncs();
        let state = self.smt_composition_state();
        let ret = self.smt_composition_return();
        let code = self.smt_composition_code();

        rand.into_iter()
            .chain(paramfuncs.into_iter())
            .chain(state.into_iter())
            .chain(ret.into_iter())
            .chain(code.into_iter())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt::Write;
    use std::string::FromUtf8Error;
    use thiserror::Error;

    #[derive(Error, Debug)]
    enum TestError {
        #[error("Error parsing the utf8: {0}")]
        Utf8DecodeError(#[from] FromUtf8Error),
        #[error("Error Writing: {0}")]
        WriteError(#[from] std::io::Error),
    }

    type TestResult = std::result::Result<(), TestError>;

    #[test]
    fn test_smtlet() -> TestResult {
        let l = SmtLet {
            bindings: vec![(
                "x".into(),
                Expression::IntegerLiteral(String::from("42")).into(),
            )],
            body: SmtExpr::Atom(String::from("x")),
        };

        let out: SmtExpr = l.into();
        let mut str = String::new();

        write!(&mut str, "{out}").unwrap();

        assert_eq!(str, "(let ((x 42)\n)\n x)\n");

        Ok(())
    }
}
