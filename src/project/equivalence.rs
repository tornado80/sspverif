use crate::package::{Composition, Export};
use crate::proof::{Proof, Resolver, SliceResolver};
use crate::transforms::proof_transforms::EquivalenceTransform;
use crate::transforms::samplify::SampleInfo;
use crate::transforms::split_partial::SplitInfo;
use crate::transforms::ProofTransform;
use crate::util::prover_process::{Communicator, ProverResponse};
use crate::writers::smt::contexts::{GameContext, GenericOracleContext};
use crate::writers::smt::exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtImplies, SmtNot};
use crate::writers::smt::writer::CompositionSmtWriter;
use crate::writers::smt::{contexts, declare};
use crate::{hacks, types};
use crate::{
    project::error::{Error, Result},
    types::Type,
};

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Write};
use std::fs::File;
use std::iter::FromIterator;

//use serde_derive::{Deserialize, Serialize};

use super::load::ProofTreeSpec;

use crate::proof::Equivalence;

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProverThingyState {
    EmitBaseDeclarations,
    EmitGameInstances,
    EmitConstantDeclarations,
    EmitInvariants(usize),
    EmitLemmaAssert(usize, usize),
    Done,
}

#[derive(Debug, Clone)]
struct ProverThingyOutput {
    output_type: ProverThingyOutputType,
    smt: Vec<SmtExpr>,
    expect: Option<ProverResponse>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProverThingyOutputType {
    BaseDeclarations,
    Games,
    ConstantDeclarations,
    Invariants { file_names: Vec<String> },
    LemmaAssert { lemma_name: String, is_last: bool },
    End,
}

struct ProverThingy<'a> {
    state: ProverThingyState,
    eq: &'a Equivalence,
    proof: &'a Proof,
    types: &'a [Type],
    sample_info_left: &'a SampleInfo,
    sample_info_right: &'a SampleInfo,
    split_info_left: &'a SplitInfo,
    split_info_right: &'a SplitInfo,
}

impl<'a> ProverThingy<'a> {
    pub fn new(
        eq: &'a Equivalence,
        proof: &'a Proof,
        types: &'a [Type],
        sample_info_left: &'a SampleInfo,
        sample_info_right: &'a SampleInfo,
        split_info_left: &'a SplitInfo,
        split_info_right: &'a SplitInfo,
    ) -> ProverThingy<'a> {
        ProverThingy {
            state: ProverThingyState::EmitBaseDeclarations,
            eq,
            proof,
            types,
            sample_info_left,
            sample_info_right,
            split_info_left,
            split_info_right,
        }
    }

    pub fn next(&mut self, resp: Option<ProverResponse>) -> Result<ProverThingyOutput> {
        //eprintln!("called next.");
        //eprintln!("  state: {:?}", self.state);
        let resp = match &self.state {
            ProverThingyState::EmitBaseDeclarations => {
                let resp = self.emit_base_declarations();
                self.state = ProverThingyState::EmitGameInstances;
                /* used to be partial information but we don't need that here anymore */
                resp
            }
            ProverThingyState::EmitGameInstances => {
                let resp = self.emit_game_definitions();
                self.state = ProverThingyState::EmitConstantDeclarations;
                resp
            }
            ProverThingyState::EmitConstantDeclarations => {
                let resp = self.emit_constant_declarations();
                self.state = ProverThingyState::EmitInvariants(0);
                resp
            }
            ProverThingyState::EmitInvariants(oracle_offs) => {
                if self.eq.get_invariants(*oracle_offs).is_some() {
                    let resp = self.emit_invariant();
                    self.state = ProverThingyState::EmitLemmaAssert(*oracle_offs, 0);
                    resp
                } else {
                    unreachable!();
                }
            }
            ProverThingyState::EmitLemmaAssert(oracle_offs, offs) => {
                let mut resp = self.emit_lemma_assert();
                let trees = self.eq.trees();

                let (oracle_name, proof_tree_records) = &trees[*oracle_offs];
                let lemma_name = proof_tree_records[*offs].lemma_name();
                eprintln!("checking lemma {lemma_name} for oracle {oracle_name}...");

                self.state = match proof_tree_records.get(offs + 1) {
                    Some(_) => ProverThingyState::EmitLemmaAssert(*oracle_offs, offs + 1),
                    None => match trees.get(oracle_offs + 1) {
                        Some(_) => ProverThingyState::EmitInvariants(oracle_offs + 1),
                        None => ProverThingyState::Done,
                    },
                };

                resp
            }
            ProverThingyState::Done => ProverThingyOutput {
                output_type: ProverThingyOutputType::End,
                smt: vec![],
                expect: None,
            },
        };

        Ok(resp)
    }

    fn emit_base_declarations(&self) -> ProverThingyOutput {
        let mut base_declarations: Vec<SmtExpr> = vec![("set-logic", "ALL").into()];

        for tipe in self.types {
            if let Type::Bits(id) = &tipe {
                base_declarations.extend(hacks::BitsDeclaration(id.to_string()).into_iter());
            }
        }

        base_declarations.extend(hacks::MaybeDeclaration.into_iter());
        base_declarations.extend(hacks::TuplesDeclaration(1..32).into_iter());
        base_declarations.extend(hacks::EmptyDeclaration.into_iter());

        ProverThingyOutput {
            output_type: ProverThingyOutputType::BaseDeclarations,
            smt: base_declarations,
            expect: None,
        }
    }

    fn emit_game_definitions(&self) -> ProverThingyOutput {
        let instance_resolver = SliceResolver(self.proof.instances());
        let left = instance_resolver.resolve(&self.eq.left_name()).unwrap();
        let right = instance_resolver.resolve(&self.eq.right_name()).unwrap();

        let mut left_writer = CompositionSmtWriter::new(
            left.as_game(),
            &self.sample_info_left,
            &self.split_info_left,
        );
        let mut right_writer = CompositionSmtWriter::new(
            right.as_game(),
            &self.sample_info_right,
            &self.split_info_right,
        );
        // write left game code
        let mut out = left_writer.smt_composition_all();
        // write right game code
        let right_out = right_writer.smt_composition_all();

        out.extend(right_out.into_iter());

        ProverThingyOutput {
            output_type: ProverThingyOutputType::Games,
            smt: out,
            expect: None,
        }
    }

    // fn emit_split_enum(&self) -> ProverThingyOutput {
    //     let instance_resolver = SliceResolver(self.proof.instances());
    //     let left = instance_resolver.resolve(&self.eq.left_name()).unwrap();
    //     let right = instance_resolver.resolve(&self.eq.right_name()).unwrap();
    //
    //     let gctx_left = contexts::GameContext::new(left.as_game());
    //     let gctx_right = contexts::GameContext::new(right.as_game());
    //
    //     let mut out = vec![];
    //     out.append(&mut gctx_left.smt_declare_intermediate_state_enum(self.split_info_left));
    //     out.append(&mut gctx_right.smt_declare_intermediate_state_enum(self.split_info_right));
    //
    //     ProverThingyOutput {
    //         output_type: ProverThingyOutputType::Partials,
    //         smt: out,
    //         expect: None,
    //     }
    // }

    fn emit_constant_declarations(&self) -> ProverThingyOutput {
        let instance_resolver = SliceResolver(self.proof.instances());
        let left = instance_resolver.resolve(&self.eq.left_name()).unwrap();
        let right = instance_resolver.resolve(&self.eq.right_name()).unwrap();

        let gctx_left = contexts::GameContext::new(left.as_game());
        let gctx_right = contexts::GameContext::new(right.as_game());

        let mut out = Vec::new();

        // write declaration of left (old) state constant
        let decl_state_left =
            declare::declare_const("state-left".to_string(), gctx_left.smt_sort_gamestates());

        // write declaration of right (old) state constant
        let decl_state_right =
            declare::declare_const("state-right".to_string(), gctx_right.smt_sort_gamestates());

        out.push(decl_state_left);
        out.push(decl_state_right);

        // write declarations of state lengths
        let state_length_left_old = "state-length-left-old";
        let state_length_left_new = "state-length-left-new";
        let state_length_right_old = "state-length-right-old";
        let state_length_right_new = "state-length-right-new";
        let state_lengths = &[
            state_length_left_old,
            state_length_left_new,
            state_length_right_old,
            state_length_right_new,
        ];

        for state_length in state_lengths {
            let decl_state_length =
                declare::declare_const(state_length.to_string(), types::Type::Integer);
            out.push(decl_state_length);
        }

        // write declarations of arguments for the exports in left
        for Export(_, sig) in &left.as_game().exports {
            if let Some(orcl_ctx) = gctx_left.exported_oracle_ctx_by_name(&sig.name) {
                for (arg_name, arg_type) in &sig.args {
                    out.push(declare::declare_const(
                        orcl_ctx.smt_arg_name(arg_name),
                        arg_type,
                    ));
                }
            }

            if let Some(orcl_ctx) = gctx_left.exported_split_oracle_ctx_by_name(&sig.name) {
                for (arg_name, arg_type) in &sig.args {
                    out.push(declare::declare_const(
                        orcl_ctx.smt_arg_name(arg_name),
                        arg_type,
                    ));
                }
            }
        }

        // write declarations of arguments for the split of the right.
        // these have to be added separately, and have already been added through left's loop
        for Export(_, sig) in &right.as_game().exports {
            if let Some(orcl_ctx) = gctx_right.exported_split_oracle_ctx_by_name(&sig.name) {
                for (arg_name, arg_type) in &sig.args {
                    out.push(declare::declare_const(
                        orcl_ctx.smt_arg_name(arg_name),
                        arg_type,
                    ));
                }
            }
        }

        for (decl_ret, constrain) in build_returns(&left.as_game(), Side::Left) {
            out.push(decl_ret);
            out.push(constrain);
        }

        for (decl_ret, constrain) in build_returns(&right.as_game(), Side::Right) {
            out.push(decl_ret);
            out.push(constrain);
        }

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(&self.sample_info_left, left.as_game(), Side::Left)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(&self.sample_info_right, right.as_game(), Side::Right)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        ProverThingyOutput {
            output_type: ProverThingyOutputType::ConstantDeclarations,
            smt: out,
            expect: None,
        }
    }

    fn emit_invariant(&self) -> ProverThingyOutput {
        let offs = match &self.state {
            ProverThingyState::EmitInvariants(offs) => *offs,
            _ => unreachable!(),
        };

        let file_names = self.eq.get_invariants(offs).unwrap().to_vec();

        ProverThingyOutput {
            output_type: ProverThingyOutputType::Invariants { file_names },
            smt: vec![],
            expect: Some(ProverResponse::Sat),
        }
    }

    fn emit_lemma_assert(&self) -> ProverThingyOutput {
        let left = self.left_game();
        let right = self.right_game();

        let (oracle_offs, lemma_offs) = match &self.state {
            ProverThingyState::EmitLemmaAssert(oracle_offs, lemma_offs) => {
                (*oracle_offs, *lemma_offs)
            }
            _ => unreachable!(),
        };

        let trees = self.eq.trees();
        let (oracle_name, oracle_lemmas) = &trees[oracle_offs];
        let lemma = &oracle_lemmas[lemma_offs];

        let is_last = lemma_offs == oracle_lemmas.len() - 1;

        let lemma_name = lemma.lemma_name();
        let deps = lemma.dependencies();

        let gctx_left = GameContext::new(&left);
        let gctx_right = GameContext::new(&right);

        // the oracle definition
        let sig = left
            .exports
            .iter()
            .find(|Export(_, sig)| &sig.name == oracle_name)
            .map(|Export(inst_idx, _)| {
                left.pkgs[*inst_idx]
                    .pkg
                    .oracles
                    .iter()
                    .find(|odef| &odef.sig.name == oracle_name)
                    .map(|odef| odef.sig.clone())
            })
            .flatten()
            .unwrap();

        let args: Vec<_> = sig
            .args
            .iter()
            .map(|(arg_name, _)| format!("arg-{oracle_name}-{arg_name}"))
            .collect();

        // find the package instance which is marked as exporting
        // the oracle of this name, both left and right.
        let left_return_name = left
            .exports
            .iter()
            .find(|Export(_, sig)| &sig.name == oracle_name)
            .map(|Export(inst_idx, _)| {
                let inst_name = &left.pkgs[*inst_idx].name;
                format!("return-left-{inst_name}-{oracle_name}")
            })
            .unwrap();

        let right_return_name = right
            .exports
            .iter()
            .find(|Export(_, sig)| &sig.name == oracle_name)
            .map(|Export(inst_idx, _)| {
                let inst_name = &right.pkgs[*inst_idx].name;
                format!("return-right-{inst_name}-{oracle_name}")
            })
            .unwrap();

        // this helper builds an smt expression that calls the
        // function with the given name with the old states,
        // return values and the respective arguments.
        // We expect that function to return a boolean, which makes
        // it a relation.
        let build_lemma_call = |name: String| {
            let mut tmp: Vec<SmtExpr> = vec![
                name.into(),
                "state-left".into(),
                "state-right".into(),
                "state-length-left-old".into(),
                "state-length-right-old".into(),
                left_return_name.clone().into(),
                right_return_name.clone().into(),
            ];

            for arg in args {
                tmp.push(arg.clone().into());
            }

            SmtExpr::List(tmp)
        };

        let octx_left = gctx_left.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let inst_name_left = octx_left.pkg_inst_ctx().pkg_inst_name();

        let octx_right = gctx_right.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let inst_name_right = octx_right.pkg_inst_ctx().pkg_inst_name();

        let left_return_name = format!("return-left-{inst_name_left}-{oracle_name}");
        let state_length_left_new = octx_left.smt_access_return_state_length(left_return_name);

        let right_return_name = format!("return-right-{inst_name_right}-{oracle_name}");
        let state_length_right_new = octx_right.smt_access_return_state_length(right_return_name);

        let mut dependencies_code: Vec<SmtExpr> = vec![
            format!("randomness-mapping-{oracle_name}").into(),
            ("=", "state-length-left-new", state_length_left_new).into(),
            ("=", "state-length-right-new", state_length_right_new).into(),
            build_lemma_call.clone()(format!("invariant-{oracle_name}")),
        ];

        for dep_name in deps {
            dependencies_code.push(build_lemma_call.clone()(dep_name.clone()))
        }

        let code: SmtExpr = crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
            SmtAnd(dependencies_code),
            build_lemma_call(lemma_name.to_string()),
        )))
        .into();

        //epilogue.push((oracle_name, lemma_name, code));

        ProverThingyOutput {
            output_type: ProverThingyOutputType::LemmaAssert {
                lemma_name: lemma_name.to_string(),
                is_last,
            },
            smt: vec![code],
            expect: Some(ProverResponse::Unsat),
        }
    }

    fn left_game(&self) -> Composition {
        let left = self.eq.left_name();
        let insts = SliceResolver(self.proof.instances());
        let left_game_inst = insts.resolve(left).unwrap();
        left_game_inst.as_game().clone()
    }

    fn right_game(&self) -> Composition {
        let right = self.eq.right_name();
        let insts = SliceResolver(self.proof.instances());
        let right_game_inst = insts.resolve(right).unwrap();
        right_game_inst.as_game().clone()
    }
}

pub fn verify(eq: &Equivalence, proof: &Proof, transcript_file: File) -> Result<()> {
    let (proof, auxs) = EquivalenceTransform.transform_proof(proof)?;
    let aux_resolver = SliceResolver(&auxs);
    let (_, (_, types_left, sample_info_left, split_info_left)) =
        aux_resolver.resolve(eq.left_name()).unwrap();
    let (_, (_, types_right, sample_info_right, split_info_right)) =
        aux_resolver.resolve(eq.right_name()).unwrap();
    let types: Vec<_> = types_left.union(types_right).cloned().collect();

    let mut prover = Communicator::new_cvc5_with_transcript(transcript_file)?;
    let mut thingy = ProverThingy::new(
        eq,
        &proof,
        &types,
        sample_info_left,
        sample_info_right,
        split_info_left,
        split_info_right,
    );
    let mut resp = None;

    let mut i = 0;

    println!("====================");

    loop {
        i = i + 1;
        let out = thingy.next(resp)?;

        // eprintln!("call returned.");
        // eprintln!("  type: {:?}", out.output_type);

        let ProverThingyOutput {
            smt: smt_exprs,
            expect,
            output_type,
        } = out;

        match &output_type {
            ProverThingyOutputType::End => return Ok(()),
            ProverThingyOutputType::Invariants { file_names } => {
                write!(prover, "(push 1)").unwrap();
                for file_name in file_names {
                    let file_contents = std::fs::read_to_string(file_name)?;
                    write!(prover, "{file_contents}").unwrap();
                }
            }
            ProverThingyOutputType::LemmaAssert { .. } => write!(prover, "(push 1)").unwrap(),
            _ => {}
        }

        for smt_expr in smt_exprs {
            println!("sending: {smt_expr}");
            write!(prover, "{smt_expr}").expect(&format!("error writing expression {smt_expr}"));
            std::thread::sleep(std::time::Duration::from_millis(1));
        }

        std::thread::sleep(std::time::Duration::from_millis(100));

        resp = if let Some(expected) = expect {
            write!(prover, ";;;i: {i}\n").unwrap();
            let resp: ProverResponse = prover.check_sat()?;
            if resp != expected {
                let model = prover.get_model()?;
                return Err(Error::ProofCheck(format!("expected prover result {expected}, got {resp} at output type {output_type:?}. model: {model:?}")));
            }

            Some(expected)
        } else {
            None
        };

        match &output_type {
            ProverThingyOutputType::End => writeln!(prover, "(pop 1) ; for end; i: {i}").unwrap(),
            ProverThingyOutputType::LemmaAssert {
                lemma_name,
                is_last,
            } => {
                writeln!(prover, "(pop 1) ; for lemma; i: {i}").unwrap();
                if *is_last {
                    writeln!(prover, "(pop 1) ; for last lemma; i: {i}").unwrap();
                }
            }
            _ => {}
        }
    }
}

// ResolvedEquivalence contains the composisitions/games and the invariant data,
// whereas the pure Equivalence just contains the names and file paths.
// TODO: explore if we can keep references to the games in the project hashmap
pub struct ResolvedEquivalence {
    pub left: Composition,
    pub right: Composition,
    pub invariant: String,
    pub trees: HashMap<String, ProofTreeSpec>,

    pub left_decl_smt_file: std::fs::File,
    pub right_decl_smt_file: std::fs::File,
    pub base_decl_smt_file: std::fs::File,
    pub const_decl_smt_file: std::fs::File,
    pub epilogue_smt_file: std::fs::File,
    pub joined_smt_file: std::fs::File,
}

fn expect_sat(comm: &mut Communicator) -> Result<()> {
    match comm.check_sat()? {
        ProverResponse::Sat => Ok(()),
        resp => Err(Error::UnexpectedProverResponseError(
            resp,
            ProverResponse::Sat,
        )),
    }
}

fn expect_unsat(comm: &mut Communicator) -> Result<()> {
    match comm.check_sat()? {
        ProverResponse::Unsat => Ok(()),
        resp => Err(Error::UnexpectedProverResponseError(
            resp,
            ProverResponse::Unsat,
        )),
    }
}

// This function gets the parameter names that both have and checks that
// both use the same types.
// The invariant should be used to make assertions on equality or other
// relations between the two.
//
// TODO figure out if there is a better mechanism we could use here
fn check_matching_parameters(left: &Composition, right: &Composition) -> Result<()> {
    use std::collections::hash_map::RandomState;

    // populate tables name -> type
    let left_params: HashMap<_, _, RandomState> =
        HashMap::from_iter(left.consts.clone().into_iter());
    let right_params: HashMap<_, _, RandomState> =
        HashMap::from_iter(right.consts.clone().into_iter());

    // prepare sets of names
    let left_params_set = HashSet::<_, RandomState>::from_iter(left_params.keys());
    let right_params_set = HashSet::<_, RandomState>::from_iter(right_params.keys());
    let common_params = left_params_set.intersection(&right_params_set);

    // check that the common params have the same type
    for param in common_params {
        if left_params[*param] != right_params[*param] {
            return Err(Error::CompositionParamMismatch(
                left.name.clone(),
                right.name.clone(),
                (*param).clone(),
            ));
        }
    }

    Ok(())
}

fn build_returns(game: &Composition, game_side: Side) -> Vec<(SmtExpr, SmtExpr)> {
    let gctx = contexts::GameContext::new(game);

    // write declarations of right return constants and constrain them
    game.exports
        .iter()
        .map(|Export(inst_idx, sig)| {
            let oracle_name = &sig.name;
            let game_name = &game.name;
            let octx = gctx.exported_oracle_ctx_by_name(&sig.name).expect(&format!(
                "error looking up exported oracle with name {oracle_name} in game {game_name}"
            ));
            let inst_name = &game.pkgs[*inst_idx].name;
            let oracle_name = &sig.name;
            let return_name = format!("return-{game_side}-{inst_name}-{oracle_name}");

            let decl_return = declare::declare_const(return_name.clone(), octx.smt_sort_return());

            let args = sig
                .args
                .iter()
                .map(|(arg_name, _)| octx.smt_arg_name(arg_name));

            let invok = octx
                .smt_invoke_oracle(
                    format!("state-{game_side}"),
                    format!("state-length-{game_side}-old"),
                    args,
                )
                .unwrap();

            let constrain_return: SmtExpr = SmtAssert(SmtEq2 {
                lhs: return_name,
                rhs: invok,
            })
            .into();

            (decl_return, constrain_return)
        })
        .collect()
}

fn build_rands(
    sample_info: &SampleInfo,
    game: &Composition,
    game_side: Side,
) -> Vec<(SmtExpr, SmtExpr, SmtExpr, SmtExpr)> {
    let gctx = contexts::GameContext::new(game);

    sample_info
        .positions
        .iter()
        .map(|sample_item| {
            let sample_id = sample_item.sample_id;
            let tipe = &sample_item.tipe;

            let states = format!("state-{game_side}");
            let states_len = format!("state-length-{game_side}-old");
            let state = ("select", states, states_len);

            let randctr_name = format!("randctr-{game_side}-{sample_id}");
            let randval_name = format!("randval-{game_side}-{sample_id}");

            let decl_randctr = declare::declare_const(randctr_name.clone(), Type::Integer);
            let decl_randval = declare::declare_const(randval_name.clone(), tipe);

            // pull randomness counter for given sample_id out of the gamestate
            let randctr = gctx
                .smt_access_gamestate_rand(sample_info, state, sample_id)
                .unwrap();

            let constrain_randctr: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randctr_name.as_str(),
                rhs: randctr.clone(),
            })
            .into();

            // apply respective randomness function (based on type) to the given counter
            let randval = gctx.smt_eval_randfn(sample_id, ("+", 0, randctr_name.as_str()), tipe);

            let constrain_randval: SmtExpr = SmtAssert(SmtEq2 {
                lhs: randval_name,
                rhs: randval,
            })
            .into();

            (
                decl_randctr,
                constrain_randctr,
                decl_randval,
                constrain_randval,
            )
        })
        .collect()
}

enum Side {
    Left,
    Right,
}

impl Display for Side {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Side::Left => write!(f, "left"),
            Side::Right => write!(f, "right"),
        }
    }
}
