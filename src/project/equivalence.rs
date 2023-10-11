use crate::hacks;
use crate::package::{Composition, Export, OracleSig, SplitExport};
use crate::proof::{Claim, ClaimType, GameInstance, Proof, Resolver, SliceResolver};
use crate::split::{SplitOracleSig, SplitPath};
use crate::transforms::proof_transforms::EquivalenceTransform;
use crate::transforms::samplify::SampleInfo;
use crate::transforms::split_partial::SplitInfoEntry;
use crate::transforms::ProofTransform;
use crate::util::prover_process::{Communicator, ProverResponse};
use crate::writers::smt::contexts::{GameContext, GenericOracleContext};
use crate::writers::smt::exprs::{SmtAnd, SmtAssert, SmtEq2, SmtExpr, SmtImplies, SmtNot};
use crate::writers::smt::partials::into_partial_dtypes;
use crate::writers::smt::writer::CompositionSmtWriter;
use crate::writers::smt::{contexts, declare};
use crate::{
    project::error::{Error, Result},
    types::Type,
};

use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Write};
use std::fs::File;
use std::iter::FromIterator;

use super::load::ProofTreeSpec;

use crate::proof::Equivalence;

pub fn verify(eq: &Equivalence, proof: &Proof, transcript_file: File) -> Result<()> {
    let (proof, auxs) = EquivalenceTransform.transform_proof(proof)?;

    let eqctx = EquivalenceContext {
        eq,
        proof: &proof,
        auxs: &auxs,
    };

    let mut prover = Communicator::new_cvc5_with_transcript(transcript_file)?;

    std::thread::sleep(std::time::Duration::from_millis(20));

    eqctx.emit_base_declarations(&mut prover)?;
    eqctx.emit_game_definitions(&mut prover)?;
    eqctx.emit_constant_declarations(&mut prover)?;

    for oracle_sig in eqctx.oracle_sequence() {
        println!("verify: oracle:{oracle_sig:?}");
        write!(prover, "(push 1)").unwrap();
        eqctx.emit_invariant(&mut prover, &oracle_sig.name)?;

        for claim in eqctx.eq.proof_tree_by_oracle_name(&oracle_sig.name) {
            write!(prover, "(push 1)").unwrap();
            eqctx.emit_claim_assert(&mut prover, &oracle_sig.name, &claim)?;
            match prover.check_sat()? {
                ProverResponse::Sat => {
                    let lemma_name = claim.name();
                    let model = prover.get_model()?;
                    return Err(Error::ProofCheck(format!(
                        "lemma {lemma_name}: expected unsat, got sat. model: {model}"
                    )));
                }
                ProverResponse::Unknown => {
                    let lemma_name = claim.name();
                    return Err(Error::ProofCheck(format!(
                        "lemma {lemma_name}: expected unsat, got unknown"
                    )));
                }
                _ => {}
            }
            write!(prover, "(pop 1)").unwrap();
        }

        write!(prover, "(pop 1)").unwrap();
    }

    for split_oracle_sig in eqctx.split_oracle_sequence() {
        println!("verify: split oracle:{split_oracle_sig:?}");
        write!(prover, "(push 1)").unwrap();
        eqctx.emit_invariant(&mut prover, &split_oracle_sig.name)?;

        for claim in eqctx.eq.proof_tree_by_oracle_name(&split_oracle_sig.name) {
            write!(prover, "(push 1)").unwrap();
            eqctx.emit_split_claim_assert(
                &mut prover,
                &split_oracle_sig.name,
                &split_oracle_sig.path,
                &claim,
            )?;
            match prover.check_sat()? {
                ProverResponse::Sat => {
                    let lemma_name = claim.name();
                    let model = prover.get_model()?;
                    return Err(Error::ProofCheck(format!(
                        "lemma {lemma_name}: expected unsat, got sat. model: {model}"
                    )));
                }
                ProverResponse::Unknown => {
                    let lemma_name = claim.name();
                    return Err(Error::ProofCheck(format!(
                        "lemma {lemma_name}: expected unsat, got unknown"
                    )));
                }
                _ => {}
            }
            write!(prover, "(pop 1)").unwrap();
        }

        write!(prover, "(pop 1)").unwrap();
    }

    Ok(())
}

struct EquivalenceContext<'a> {
    eq: &'a Equivalence,
    proof: &'a Proof,
    auxs: &'a <EquivalenceTransform as ProofTransform>::Aux,
}

impl<'a> EquivalenceContext<'a> {
    fn emit_base_declarations(&self, comm: &mut Communicator) -> Result<()> {
        let mut base_declarations: Vec<SmtExpr> = vec![("set-logic", "ALL").into()];

        println!("types {:?}", self.types());

        for tipe in self.types() {
            if let Type::Bits(id) = &tipe {
                base_declarations.extend(hacks::BitsDeclaration(id.to_string()).into_iter());
            }
        }

        base_declarations.extend(hacks::MaybeDeclaration.into_iter());
        base_declarations.extend(hacks::TuplesDeclaration(1..32).into_iter());
        base_declarations.extend(hacks::EmptyDeclaration.into_iter());
        base_declarations.push(hacks::ReturnValueDeclaration.into());

        for decl in base_declarations {
            comm.write_smt(decl)?
        }

        Ok(())
    }

    fn emit_game_definitions(&self, comm: &mut Communicator) -> Result<()> {
        let instance_resolver = SliceResolver(self.proof.instances());
        let left = instance_resolver.resolve(&self.eq.left_name()).unwrap();
        let right = instance_resolver.resolve(&self.eq.right_name()).unwrap();

        let mut left_writer =
            CompositionSmtWriter::new(left.game(), self.sample_info_left(), self.split_info_left());
        let mut right_writer = CompositionSmtWriter::new(
            right.game(),
            self.sample_info_right(),
            self.split_info_right(),
        );

        let mut out = vec![];

        out.append(&mut left_writer.smt_composition_all());
        out.append(&mut right_writer.smt_composition_all());

        for decl in out {
            comm.write_smt(decl)?
        }

        Ok(())
    }

    fn emit_constant_declarations(&self, comm: &mut Communicator) -> Result<()> {
        /*
         *
         * things being declared here:
         * - nonsplit oracle args
         * - for $game_inst in left, right
         *   - old game state $game_inst
         *   - new game state $game_inst
         *   - randomness counters $game_inst
         *   - randomness values $game_inst
         *   - for oracle in game.non-split-exports
         *     - return $game_inst $oracle
         *   - for oracle in game.split-exports
         *     - partial return $game_inst $oracle
         *     - split oracle args
         *
         * things being constrained here:
         * - for $game_inst in left, right
         *   - rand_ctr_$i = get_rand(game_state, $i)
         *   - rand_val_$i = rand_$game_inst($i, rand_ctr_$i)
         *   - for $oracle in $game_inst.non-split-exports
         *     - return = $oracle(state, args...)
         *     - new_game_state_$game_inst = get-state(return)
         *       - wait, maybe this should only be in the procondition of the claim statements
         *   - for $oracle in $game_inst.non-split-exports
         *     - partial return = $oracle(state, args...)
         *
         * Jan's thoughts on the design of the next iteration of this:
         *
         * What can go wrong here?
         *
         *   Underconstraining
         *
         *     The solver would give us a sat where we expect an unsat and we can
         *     use the model to see which constraint is missing. Until that is done, we can't prove
         *     anything but that is not that big of a deal. So I guess this is an easily debuggable
         *     completeness problem.
         *
         *   Overconstraining
         *
         *     We might add too many constraints, which would lead to the solver
         *     reporting unsat where it should return sat. This would break soundness, in ways that
         *     are not easily debuggable.
         *
         *   I feel like soundness is more important than completeness!
         *
         * What can we do to prevent that? (TODO)
         *
         *   Testing
         *
         *     I suppose the best way to guard against this is to have test cases with proofs
         *     that are expected to not go through and make sure that this is actually the case.
         *
         *   Clear Documentation/Spec
         *
         *     Making explicit the model we have of the system helps both
         *     with catching logic bugs (because in order to vet the logic you can read the docs)
         *     and implementation bugs (because you can compare the implementation against the spec).
         *
         * When do we apply the constraints?
         *
         *   Option A: Immediately after declaring
         *
         *     This doesn't work for e.g. the "new state", as that would be constrained in
         *     contradictory ways. My current heuristic is that if the value is the output of a
         *     function and there are several potential functions that it could be the output of,
         *     then it won't work.
         *
         *       Can we maybe avoid that issue by not "overloading" constants? Use constants as
         *       the output of one particular thing? What are other instances of constants that are
         *       constrained differently depending on the call?
         *
         *         Other instances: I was going to say PartialReturn, but not only by "real" oracle
         *         but also by split oracle, but I don' think that is true since because of the
         *         dispatch function. So maybe it's just Return and PartialReturn, by "real" oracle?
         *
         *         We could avoid that by not having a single "new state" constant, but one per
         *         oracle. That might be a tad inconvenient though? Or we just bind the convenient
         *         names using let, either in the lemma/relation/invariant or in the glue code
         *         calling it. This would mean we don't even need the constants and don't need to
         *         constrain them. Sounds like there is less chance of confusion, too!
         *
         *   Option B: First declare all constants, then constrain
         *
         *     Seems difficult to keep track of the constraints we still need to do.
         *
         * So to me it seems the best way is to
         *
         * 1.  declare foundational constants ("old state", "function arguments")
         * 2.  declare constants that conceptually are outputs of a known function taking
         *     foundational constants ("return per oracle") and immediately constrain them
         * 3.  only bind convenience values in (let ..) blocks close to the code using them.
         *     This can be done manually in the user code, or in the glue code calling the user
         *     code.
         *
         *       I think there is a discussion to be had here, though. If we go with the let-bind
         *       approache, we can't make the randomness mapping a bunch of asserts. It needs to be
         *       an expression that evaluates to a bool. Is the user fine with that?
         *
         *       I think this can affect model readability (for a human) in one of two ways:
         *
         *         Possible Impact A: There a fewer global constants, and all the values are in the
         *         specific part of the gamestate. It is more tidy and it is easy to find what you
         *         are looking for.
         *
         *         Possibe Impact B: Instead of having a global constant rand-Real-1-4 as a constant
         *         in the model, you have to sift through the game state structs to find the
         *         correct one to see the value, which makes it more difficult.
         *
         *         I wonder which of these would be stronger, and believe it depends on the habits and
         *         preferences of the user.
         *
         * Which leaves us to specify (and give reasons for) our list of constants and constraints.
         * Afterwards, we also make a list of constants constraints we chose not to include here.
         *
         *   Foundational Constants: Old Gamestate, Old Intermediate State and Arguments
         *
         *     These are only used as inputs to the oracle functions. There is nothing we can tie
         *     them to, we can only constrain them in lemmas, etc.
         *
         *   Function Outputs: Return, PartialReturn
         *
         *     These can be directly computed from the above. They should simply be constrained.
         *
         *   Convenience Values: New Gamestate, New Intermediate State, IsAbort, Return Value,
         *                       Randomness Counters, Random Values
         *
         *     These fall in two categories:
         *
         *     1.  Values where a convenient name would not be globally unique (e.g. new state, is abort)
         *
         *           Here I think using (let ..) bindings really is the best way to handle the
         *           ambiguity.
         *
         *     2.  Values that have unique names, but are rarely needed and are just copied from the
         *         gamestate (e.g. randomness)
         *
         *           Here I am not sure - From a "purity" standpoint it feels nice to me, but I see how
         *           that is not a very strong argument, so we may just declare and constrain them globally.
         *
         */

        let instance_resolver = SliceResolver(self.proof.instances());
        let left_game_inst_name = self.eq.left_name();
        let right_game_inst_name = self.eq.right_name();

        let left = instance_resolver.resolve(self.eq.left_name()).unwrap();
        let right = instance_resolver.resolve(self.eq.right_name()).unwrap();

        let gctx_left = contexts::GameContext::new(left.game());
        let gctx_right = contexts::GameContext::new(right.game());

        let mut out = Vec::new();

        /////// old state constants

        let decl_state_left = declare::declare_const(
            format!("state-{left_game_inst_name}"),
            gctx_left.smt_sort_gamestate(),
        );
        let decl_state_right = declare::declare_const(
            format!("state-{right_game_inst_name}"),
            gctx_right.smt_sort_gamestate(),
        );

        out.push(decl_state_left);
        out.push(decl_state_right);

        /////// arguments for non-split and split oracles

        let left_partial_datatypes = into_partial_dtypes(self.split_info_left());
        let right_partial_datatypes = into_partial_dtypes(self.split_info_right());

        // write declarations of arguments for the exports in left
        for Export(_, sig) in &left.game().exports {
            if let Some(orcl_ctx) = gctx_left.exported_oracle_ctx_by_name(&sig.name) {
                for (arg_name, arg_type) in &sig.args {
                    out.push(declare::declare_const(
                        orcl_ctx.smt_arg_name(arg_name),
                        arg_type,
                    ));
                }
            }

            if let Some(partial_dtype) = left_partial_datatypes
                .iter()
                .find(|dtype| dtype.real_oracle_sig.name == sig.name)
            {
                let orcl_ctx = gctx_left
                    .exported_split_oracle_ctx_by_name(&sig.name, &partial_dtype)
                    .unwrap();
                for (arg_name, arg_type) in &sig.args {
                    out.push(declare::declare_const(
                        orcl_ctx.smt_arg_name(arg_name),
                        arg_type,
                    ));
                }
            }
        }

        // write declarations of arguments for the split oracles of the right.
        // the non-split ones are shared between games and have already been
        // added for the loop above.
        for Export(_, sig) in &right.game().exports {
            if let Some(partial_dtype) = right_partial_datatypes
                .iter()
                .find(|dtype| dtype.real_oracle_sig.name == sig.name)
            {
                let orcl_ctx = gctx_right
                    .exported_split_oracle_ctx_by_name(&sig.name, &partial_dtype)
                    .unwrap();
                for (arg_name, arg_type) in &sig.args {
                    out.push(declare::declare_const(
                        orcl_ctx.smt_arg_name(arg_name),
                        arg_type,
                    ));
                }
            }
        }

        ////// return values

        for (decl_ret, constrain) in build_returns(&left.game(), Side::Left) {
            out.push(decl_ret);
            out.push(constrain);
        }

        for (decl_ret, constrain) in build_returns(&right.game(), Side::Right) {
            out.push(decl_ret);
            out.push(constrain);
        }

        /////// randomess counters

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(self.sample_info_left(), left, Side::Left)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        for (decl_ctr, assert_ctr, decl_val, assert_val) in
            build_rands(self.sample_info_right(), right, Side::Right)
        {
            out.push(decl_ctr);
            out.push(assert_ctr);
            out.push(decl_val);
            out.push(assert_val);
        }

        ///// write expressions

        for expr in out {
            comm.write_smt(expr)?
        }

        Ok(())
    }

    fn emit_invariant(&self, comm: &mut Communicator, oracle_name: &str) -> Result<()> {
        for file_name in self.eq.invariants_by_oracle_name(oracle_name) {
            println!("reading file {file_name}");
            let file_contents = std::fs::read_to_string(&file_name)?;
            println!("read file {file_name}");
            write!(comm, "{file_contents}").unwrap();
            println!("wrote contents of file {file_name}");

            if comm.check_sat()? != ProverResponse::Sat {
                return Err(Error::ProofCheck(
                    "unsat after reading invariant file".to_string(),
                ));
            }
        }

        Ok(())
    }

    fn emit_split_claim_assert(
        &self,
        comm: &mut Communicator,
        oracle_name: &str,
        path: &SplitPath,
        claim: &Claim,
    ) -> Result<()> {
        todo!()
    }

    fn emit_claim_assert(
        &self,
        comm: &mut Communicator,
        oracle_name: &str,
        claim: &Claim,
    ) -> Result<()> {
        let gctx_left = self.left_game_ctx();
        let gctx_right = self.right_game_ctx();

        let lemma_name = claim.name();

        // the oracle definition
        let sig = gctx_left
            .game()
            .exports
            .iter()
            .find(|Export(_, sig)| &sig.name == oracle_name)
            .map(|Export(inst_idx, _)| {
                gctx_left.game().pkgs[*inst_idx]
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
        let left_return_name = gctx_left
            .game()
            .exports
            .iter()
            .find(|Export(_, sig)| &sig.name == oracle_name)
            .map(|Export(inst_idx, _)| {
                let inst_name = &gctx_left.game().pkgs[*inst_idx].name;
                format!("return-left-{inst_name}-{oracle_name}")
            })
            .unwrap();

        let right_return_name = gctx_right
            .game()
            .exports
            .iter()
            .find(|Export(_, sig)| &sig.name == oracle_name)
            .map(|Export(inst_idx, _)| {
                let inst_name = &gctx_right.game().pkgs[*inst_idx].name;
                format!("return-right-{inst_name}-{oracle_name}")
            })
            .unwrap();

        // this helper builds an smt expression that calls the
        // function with the given name with the old states,
        // return values and the respective arguments.
        // We expect that function to return a boolean, which makes
        // it a relation.
        let build_lemma_call = |name: &str| {
            let mut tmp: Vec<SmtExpr> = vec![
                name.into(),
                "state-left".into(),
                "state-right".into(),
                left_return_name.clone().into(),
                right_return_name.clone().into(),
            ];

            for arg in args {
                tmp.push(arg.clone().into());
            }

            SmtExpr::List(tmp)
        };

        let build_relation_call =
            |name: &str| -> SmtExpr { (name, "state-left-new", "state-right-new").into() };

        let build_invariant_old_call =
            |name: &str| -> SmtExpr { (name, "state-left-old", "state-right-old").into() };

        let build_invariant_new_call =
            |name: &str| -> SmtExpr { (name, "state-left-new", "state-right-new").into() };

        let octx_left = gctx_left.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let inst_name_left = octx_left.pkg_inst_ctx().pkg_inst_name();

        let octx_right = gctx_right.exported_oracle_ctx_by_name(oracle_name).unwrap();
        let inst_name_right = octx_right.pkg_inst_ctx().pkg_inst_name();

        let dep_calls: Vec<_> = claim
            .dependencies()
            .iter()
            .map(|dep_name| {
                let claim_type = ClaimType::guess_from_name(dep_name);
                match claim_type {
                    ClaimType::Lemma => build_lemma_call.clone()(&dep_name),
                    ClaimType::Relation => build_relation_call.clone()(&dep_name),
                    ClaimType::Invariant => unreachable!(),
                }
            })
            .collect();

        let postcond_call = match claim.tipe {
            ClaimType::Lemma => build_lemma_call.clone()(&claim.name),
            ClaimType::Relation => build_relation_call.clone()(&claim.name),
            ClaimType::Invariant => build_invariant_new_call.clone()(&claim.name),
        };

        let mut dependencies_code: Vec<SmtExpr> = vec![
            format!("randomness-mapping-{oracle_name}").into(),
            build_invariant_old_call.clone()("invariant-{oracle_name}"),
        ];

        for dep in dep_calls {
            dependencies_code.push(dep)
        }

        comm.write_smt(crate::writers::smt::exprs::SmtAssert(SmtNot(SmtImplies(
            SmtAnd(dependencies_code),
            postcond_call,
        ))))?;

        Ok(())
    }

    fn types(&self) -> Vec<Type> {
        let aux_resolver = SliceResolver(&self.auxs);
        let (_, (_, types_left, _, _)) = aux_resolver.resolve(self.eq.left_name()).unwrap();
        let (_, (_, types_right, _, _)) = aux_resolver.resolve(self.eq.right_name()).unwrap();
        types_left.union(types_right).cloned().collect()
    }

    fn left_game_ctx(&self) -> GameContext<'a> {
        let game_inst_name = self.eq.left_name();
        let game_inst = SliceResolver(self.proof.instances())
            .resolve(game_inst_name)
            .unwrap();
        let game = game_inst.game();
        GameContext::new(game)
    }

    fn right_game_ctx(&self) -> GameContext<'a> {
        let game_inst_name = self.eq.right_name();
        let game_inst = SliceResolver(self.proof.instances())
            .resolve(game_inst_name)
            .unwrap();
        let game = game_inst.game();
        GameContext::new(game)
    }

    fn sample_info_left(&self) -> &'a SampleInfo {
        let aux_resolver = SliceResolver(&self.auxs);
        let (_, (_, _, sample_info, _)) = aux_resolver.resolve(self.eq.left_name()).unwrap();
        sample_info
    }

    fn sample_info_right(&self) -> &'a SampleInfo {
        let aux_resolver = SliceResolver(&self.auxs);
        let (_, (_, _, sample_info, _)) = aux_resolver.resolve(self.eq.right_name()).unwrap();
        sample_info
    }

    fn split_info_left(&self) -> &'a Vec<SplitInfoEntry> {
        let aux_resolver = SliceResolver(&self.auxs);
        let (_, (_, _, _, split_info)) = aux_resolver.resolve(self.eq.left_name()).unwrap();
        split_info
    }

    fn split_info_right(&self) -> &'a Vec<SplitInfoEntry> {
        let aux_resolver = SliceResolver(&self.auxs);
        let (_, (_, _, _, split_info)) = aux_resolver.resolve(self.eq.right_name()).unwrap();
        split_info
    }

    fn oracle_sequence(&self) -> Vec<&'a OracleSig> {
        let game_inst = SliceResolver(self.proof.instances())
            .resolve(self.eq.left_name())
            .unwrap();

        println!("oracle sequence: {:?}", game_inst.game().exports);

        game_inst
            .game()
            .exports
            .iter()
            .map(|Export(_, oracle_sig)| oracle_sig)
            .collect()
    }

    fn split_oracle_sequence(&self) -> Vec<&'a SplitOracleSig> {
        let game_inst = SliceResolver(self.proof.instances())
            .resolve(self.eq.left_name())
            .unwrap();

        println!("oracle sequence: {:?}", game_inst.game().exports);

        game_inst
            .game()
            .split_exports
            .iter()
            .map(|SplitExport(_, split_oracle_sig)| split_oracle_sig)
            .collect()
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
                .smt_invoke_oracle(format!("state-{game_side}"), args)
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
    game_inst: &GameInstance,
    game_side: Side,
) -> Vec<(SmtExpr, SmtExpr, SmtExpr, SmtExpr)> {
    let gctx = contexts::GameContext::new(game_inst.game());

    sample_info
        .positions
        .iter()
        .map(|sample_item| {
            let sample_id = sample_item.sample_id;
            let tipe = &sample_item.tipe;
            let game_inst_name = game_inst.name();
            let game = game_inst.game();

            let state = format!("state-{game_inst_name}");

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
