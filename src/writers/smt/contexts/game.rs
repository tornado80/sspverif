use crate::{
    package::{Composition, Export},
    transforms::samplify::SampleInfo,
    types::Type,
    writers::smt::{
        exprs::{SmtExpr, SmtLet},
        names,
        patterns::{
            DatastructurePattern2, GameStateDeclareInfo, GameStatePattern, GameStateSelector,
        },
    },
};

use super::{GameContext, OracleContext, PackageInstanceContext, SplitOracleContext};

impl<'a> GameContext<'a> {
    pub fn new(game: &'a Composition) -> Self {
        Self { game }
    }

    pub fn game(&self) -> &'a Composition {
        &self.game
    }

    pub fn pkg_inst_ctx_by_name(&self, inst_name: &str) -> Option<PackageInstanceContext<'a>> {
        self.game
            .pkgs // we only want a single package, no sorting needed
            .iter()
            .position(|pkg| pkg.name == inst_name)
            .map(|inst_offs| PackageInstanceContext {
                game_ctx: self.clone(),
                inst_offs,
            })
    }

    pub fn pkg_inst_ctx_by_offs(&self, inst_offs: usize) -> Option<PackageInstanceContext<'a>> {
        if inst_offs >= self.game.pkgs.len() {
            return None;
        }

        Some(PackageInstanceContext {
            game_ctx: self.clone(),
            inst_offs,
        })
    }

    pub fn exported_oracle_ctx_by_name(&self, oracle_name: &str) -> Option<OracleContext<'a>> {
        let Export(inst_offs, _) = *self
            .game
            .exports
            .iter()
            .find(|Export(_inst_offs, osig)| osig.name == oracle_name)?;

        let inst_ctx = PackageInstanceContext {
            game_ctx: self.clone(),
            inst_offs,
        };

        inst_ctx.oracle_ctx_by_name(oracle_name)
    }

    pub fn exported_split_oracle_ctx_by_name(
        &self,
        oracle_name: &str,
    ) -> Option<SplitOracleContext<'a>> {
        let Export(inst_offs, _) = *self
            .game
            .exports
            .iter()
            .find(|Export(_inst_offs, osig)| osig.name == oracle_name)?;

        let inst_ctx = PackageInstanceContext {
            game_ctx: self.clone(),
            inst_offs,
        };

        inst_ctx.split_oracle_ctx_by_name(oracle_name)
    }

    fn consts_except_fns(&self) -> Vec<&'a (String, Type)> {
        self.game
            .consts
            .iter()
            .filter(|(_, tipe)| !matches!(tipe, crate::types::Type::Fn(_, _)))
            .collect()
    }

    pub fn smt_sort_gamestate(&self) -> SmtExpr {
        let game_name: &str = &self.game.name;
        names::gamestate_sort_name(game_name).into()
    }

    pub fn smt_sort_gamestates(&self) -> SmtExpr {
        let game_name: &str = &self.game.name;
        let gamestate = names::gamestate_sort_name(game_name);

        ("Array", "Int", gamestate).into()
    }

    pub fn smt_push_global_gamestate<S: Into<SmtExpr>, B: Into<SmtExpr>>(
        &self,
        new_state: S,
        body: B,
    ) -> SmtExpr {
        self.smt_overwrite_latest_global_gamestate(new_state, body)
    }

    pub fn smt_overwrite_latest_global_gamestate<S: Into<SmtExpr>, B: Into<SmtExpr>>(
        &self,
        new_state: S,
        body: B,
    ) -> SmtExpr {
        SmtLet {
            bindings: vec![(names::var_globalstate_name(), new_state.into())],
            body,
        }
        .into()
    }

    pub(crate) fn smt_declare_gamestate(&self, sample_info: &SampleInfo) -> SmtExpr {
        let game_state_pattern = GameStatePattern {
            game_name: &self.game.name,
        };
        let declare_info = GameStateDeclareInfo {
            game: self.game(),
            sample_info: &sample_info,
        };

        let spec = game_state_pattern.datastructure_spec(&declare_info);
        game_state_pattern.declare_datatype(&spec)
    }

    pub fn smt_access_gamestate_pkgstate<S: Into<SmtExpr>>(
        &self,
        state: S,
        inst_name: &str,
    ) -> Option<SmtExpr> {
        // if the requested package state does not exists, return none
        self.pkg_inst_ctx_by_name(inst_name)?;

        let game_name = &self.game.name;

        Some(
            (
                names::gamestate_selector_pkgstate_name(game_name, inst_name),
                state,
            )
                .into(),
        )
    }

    fn game_state_pattern(&self) -> GameStatePattern {
        let game_name = &self.game().name;
        GameStatePattern { game_name }
    }

    fn game_state_declare_info(&self, sample_info: &'a SampleInfo) -> GameStateDeclareInfo {
        let game = self.game();
        GameStateDeclareInfo { game, sample_info }
    }

    pub fn smt_update_gamestate_pkgstate<S, V>(
        &self,
        gamestate: S,
        sample_info: &SampleInfo,
        target_name: &str,
        new_pkgstate: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let game_state_pattern = self.game_state_pattern();
        let declare_info = self.game_state_declare_info(sample_info);
        let spec = game_state_pattern.datastructure_spec(&declare_info);

        let pkgstate_selector = GameStateSelector::PackageInstance {
            pkg_inst_name: target_name,
        };

        return game_state_pattern.update(&spec, &pkgstate_selector, gamestate, new_pkgstate);
    }

    fn param_type(&self, param_name: &str) -> Option<&'a Type> {
        self.game
            .consts
            .iter()
            .find(|(name, _tipe)| name == param_name)
            .map(|(_name, tipe)| tipe)
    }

    pub fn smt_access_gamestate_const<S: Into<SmtExpr>>(
        &self,
        state: S,
        param_name: &str,
        sample_info: &SampleInfo,
    ) -> Option<SmtExpr> {
        let game_state_pattern = self.game_state_pattern();
        let declare_info = self.game_state_declare_info(sample_info);
        let spec = game_state_pattern.datastructure_spec(&declare_info);

        let tipe = self.param_type(param_name)?;
        let const_selector = GameStateSelector::Const {
            const_name: param_name,
            tipe,
        };

        return game_state_pattern.access(&spec, &const_selector, state);
    }

    pub fn smt_access_gamestate_rand<S: Into<SmtExpr>>(
        &self,
        sample_info: &SampleInfo,
        state: S,
        sample_id: usize,
    ) -> Option<SmtExpr> {
        let game_state_pattern = self.game_state_pattern();
        let declare_info = self.game_state_declare_info(sample_info);
        let spec = game_state_pattern.datastructure_spec(&declare_info);

        let rand_selector = GameStateSelector::Randomness { sample_id };

        return game_state_pattern.access(&spec, &rand_selector, state);
    }

    pub fn smt_update_gamestate_rand<S, V>(
        &self,
        state: S,
        sample_info: &SampleInfo,
        sample_id: usize,
        new_value: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let game_state_pattern = self.game_state_pattern();
        let declare_info = self.game_state_declare_info(sample_info);
        let spec = game_state_pattern.datastructure_spec(&declare_info);

        let rand_selector = GameStateSelector::Randomness { sample_id };

        return game_state_pattern.update(&spec, &rand_selector, state, new_value);
    }

    // NOTE: This function could be implemented a bit more efficient. If the prover struggles, we could do that.
    // the more efficient implementation would look more like smt_update_gamestate_rand, but instead of new_value it would use (+ 1 old_value)
    // that way we don't query the old state twice
    // actually I don't think it makes a big difference, and also I don't think this function will be used anyway
    pub fn smt_increment_gamestate_rand<S>(
        &self,
        state: S,
        sample_info: &SampleInfo,
        target_sample_id: usize,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
    {
        let old_value =
            self.smt_access_gamestate_rand(sample_info, state.clone(), target_sample_id)?;
        let new_value = ("+", 1, old_value);
        self.smt_update_gamestate_rand(state, sample_info, target_sample_id, new_value)
    }

    pub fn smt_eval_randfn<CTR: Into<SmtExpr>>(
        &self,
        sample_id: usize,
        ctr: CTR,
        tipe: &Type,
    ) -> SmtExpr {
        let rand_fn_name = names::fn_sample_rand_name(&self.game.name, tipe);
        (rand_fn_name, sample_id, ctr).into()
    }
}
