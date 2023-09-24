use crate::{
    package::{Composition, Export},
    transforms::samplify::SampleInfo,
    types::Type,
    writers::smt::{
        exprs::{SmtExpr, SmtLet},
        names,
        patterns::{DatastructurePattern2, GameStateDeclareInfo, GameStatePattern},
    },
};

use super::{GameContext, OracleContext, PackageInstanceContext, SplitOracleContext};

impl<'a> GameContext<'a> {
    pub fn new(game: &'a Composition) -> Self {
        Self { game }
    }

    pub fn game(&self) -> &Composition {
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

        game_state_pattern.declare_datatype(&declare_info)
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

    pub fn smt_update_gamestate_intermediate_state<S, I>(
        &self,
        gamestate: S,
        sample_info: &SampleInfo,
        new_intermediate_state: I,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        I: Clone + Into<SmtExpr>,
    {
        let game_name: &str = &self.game.name;

        let fncall_count =
            1 + self.game.pkgs.len() + self.consts_except_fns().len() + sample_info.count + 1;

        let mut fncall = Vec::with_capacity(fncall_count);
        fncall.push(names::gamestate_constructor_name(game_name).into());

        for pkg_inst in &self.game.pkgs {
            fncall.push(self.smt_access_gamestate_pkgstate(gamestate.clone(), &pkg_inst.name)?);
        }

        for (param_name, _type) in self.consts_except_fns() {
            fncall.push(self.smt_access_gamestate_const(gamestate.clone(), param_name)?);
        }

        for sample_id in 0..sample_info.count {
            fncall.push(self.smt_access_gamestate_rand(
                sample_info,
                gamestate.clone(),
                sample_id,
            )?);
        }

        fncall.push(new_intermediate_state.into());

        Some(SmtExpr::List(fncall))
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
        let game_name: &str = &self.game.name;
        let mut found = false;

        let pkgstate_fields = self.game.pkgs.iter().map(|inst| {
            let inst_name = &inst.name;

            if inst_name == target_name {
                found = true;
                new_pkgstate.clone().into()
            } else {
                self.smt_access_gamestate_pkgstate(gamestate.clone(), inst_name)
                    .unwrap()
            }
        });

        let const_fields = self
            .consts_except_fns()
            .into_iter()
            .map(|(param_name, _tipe)| {
                self.smt_access_gamestate_const(gamestate.clone(), param_name)
                    .unwrap()
            });

        let rand_fields = (0..sample_info.count).map(|sample_id| {
            self.smt_access_gamestate_rand(sample_info, gamestate.clone(), sample_id)
                .unwrap()
        });

        let fields = pkgstate_fields.chain(const_fields).chain(rand_fields);

        let mut fncall = vec![names::gamestate_constructor_name(game_name).into()];
        fncall.extend(fields);

        if !found {
            return None;
        }

        Some(SmtExpr::List(fncall))
    }

    pub fn smt_access_gamestate_const<S: Into<SmtExpr>>(
        &self,
        state: S,
        param_name: &str,
    ) -> Option<SmtExpr> {
        // if the requested constant does not exists, return none
        self.game
            .consts
            .iter()
            .position(|(name, _)| name == param_name)?;

        let game_name = &self.game.name;

        Some(
            (
                names::gamestate_selector_param_name(game_name, param_name),
                state,
            )
                .into(),
        )
    }

    pub fn smt_access_gamestate_rand<S: Into<SmtExpr>>(
        &self,
        sample_info: &SampleInfo,
        state: S,
        sample_id: usize,
    ) -> Option<SmtExpr> {
        // if the requested sample_id does not exists, return none
        if sample_id >= sample_info.count {
            return None;
        }

        let game_name = &self.game.name;

        Some(
            (
                names::gamestate_selector_rand_name(game_name, sample_id),
                state,
            )
                .into(),
        )
    }

    pub fn smt_update_gamestate_rand<S, V>(
        &self,
        state: S,
        sample_info: &SampleInfo,
        target_sample_id: usize,
        new_value: V,
    ) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let game_name: &str = &self.game.name;
        let mut found = false;

        let pkgstate_fields = self.game.pkgs.iter().map(|inst| {
            let inst_name = &inst.name;

            self.smt_access_gamestate_pkgstate(state.clone(), inst_name)
                .unwrap()
        });

        let const_fields = self
            .consts_except_fns()
            .into_iter()
            .map(|(param_name, _tipe)| {
                self.smt_access_gamestate_const(state.clone(), param_name)
                    .unwrap()
            });

        let rand_fields = (0..sample_info.count).map(|sample_id| {
            if sample_id == target_sample_id {
                found = true;
                new_value.clone().into()
            } else {
                self.smt_access_gamestate_rand(sample_info, state.clone(), sample_id)
                    .unwrap()
            }
        });

        let fields = pkgstate_fields.chain(const_fields).chain(rand_fields);

        let mut fncall = vec![names::gamestate_constructor_name(game_name).into()];
        fncall.extend(fields);

        if !found {
            return None;
        }

        Some(SmtExpr::List(fncall))
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
