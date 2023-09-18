use crate::package::PackageInstance;
use crate::split::SplitPath;

use super::super::exprs::SmtExpr;
use super::super::{declare, names};

use super::{GameContext, OracleContext, PackageInstanceContext, SplitOracleContext};

impl<'a> PackageInstanceContext<'a> {
    pub fn game_ctx(&self) -> GameContext {
        self.game_ctx.clone()
    }

    pub fn split_oracle_ctx_by_name(&self, oracle_name: &str) -> Option<SplitOracleContext<'a>> {
        let inst_offs = self.inst_offs;
        let inst = &self.game_ctx.game.pkgs[inst_offs];
        let split_oracle_offs = inst
            .pkg
            .split_oracles
            .iter()
            .position(|odef| odef.sig.name == oracle_name)?;

        Some(SplitOracleContext {
            game_ctx: self.game_ctx.clone(),
            inst_offs,
            split_oracle_offs,
        })
    }

    pub fn oracle_ctx_by_name(&self, oracle_name: &str) -> Option<OracleContext<'a>> {
        let inst_offs = self.inst_offs;
        let inst = &self.game_ctx.game.pkgs[inst_offs];
        let oracle_offs = inst
            .pkg
            .oracles
            .iter()
            .position(|odef| odef.sig.name == oracle_name)?;

        Some(OracleContext {
            game_ctx: self.game_ctx.clone(),
            inst_offs,
            oracle_offs,
        })
    }

    pub fn split_oracle_ctx_by_name_and_path(
        &self,
        oracle_name: &str,
        oracle_path: &SplitPath,
    ) -> Option<SplitOracleContext<'a>> {
        let inst_offs = self.inst_offs;
        let inst = &self.game_ctx.game.pkgs[inst_offs];
        let split_oracle_offs = inst
            .pkg
            .split_oracles
            .iter()
            .position(|odef| odef.sig.name == oracle_name && &odef.sig.path == oracle_path)?;

        Some(SplitOracleContext {
            game_ctx: self.game_ctx.clone(),
            inst_offs,
            split_oracle_offs,
        })
    }

    pub fn oracle_ctx_by_oracle_offs(&self, oracle_offs: usize) -> Option<OracleContext<'a>> {
        let oracle_count = self.game_ctx.game.pkgs[self.inst_offs].pkg.oracles.len();
        if oracle_offs >= oracle_count {
            return None;
        }

        let game_ctx = self.game_ctx.clone();
        let inst_offs = self.inst_offs;

        Some(OracleContext {
            game_ctx,
            inst_offs,
            oracle_offs,
        })
    }

    pub fn pkg_inst_name(&self) -> &'a str {
        &self.game_ctx.game.pkgs[self.inst_offs].name
    }

    pub fn pkg_inst(&self) -> &'a PackageInstance {
        &self.game_ctx.game.pkgs[self.inst_offs]
    }

    pub fn smt_sorts_return(&self) -> Vec<SmtExpr> {
        let oracle_count = self.game_ctx.game.pkgs[self.inst_offs].pkg.oracles.len();

        (0..oracle_count)
            .map(|i| {
                let octx = self.oracle_ctx_by_oracle_offs(i).unwrap();
                octx.smt_sort_return()
            })
            .collect()
    }

    pub fn smt_declare_pkgstate(&self) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];

        let game_name = &game.name;
        let inst_name = &inst.name;

        let fields = inst.pkg.state.iter().cloned().map(|(name, tipe)| {
            (
                names::pkgstate_selector_name(game_name, inst_name, &name),
                tipe.into(),
            )
        });

        // let fields = fields.chain(
        //     vec![(
        //         names::pkgstate_selector_intermediate_name(game_name, inst_name),
        //         names::intermediate_package_instance_state_sort_name(game_name, inst_name).into(),
        //     )]
        //     .into_iter(),
        // );

        declare::declare_single_constructor_datatype(
            &names::pkgstate_sort_name(game_name, inst_name),
            &names::pkgstate_constructor_name(game_name, inst_name),
            fields,
        )
    }

    pub fn smt_access_pkgstate<S: Into<SmtExpr>>(
        &self,
        state: S,
        field_name: &str,
    ) -> Option<SmtExpr> {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];

        let game_name = &game.name;
        let inst_name = &inst.name;

        // return none if no field with that name exists
        inst.pkg
            .state
            .iter()
            .find(|(name, _tipe)| name == field_name)?;

        let access = (
            names::pkgstate_selector_name(game_name, inst_name, field_name),
            state,
        )
            .into();

        Some(access)
    }

    pub fn smt_update_pkgstate<S, V>(&self, state: S, field_name: &str, value: V) -> Option<SmtExpr>
    where
        S: Clone + Into<SmtExpr>,
        V: Clone + Into<SmtExpr>,
    {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];

        let game_name = &game.name;
        let inst_name = &inst.name;

        let mut found = false;

        // an iterator that returns either a selector on the current state
        // or the provided value, effectively updating the target field
        let args: Vec<SmtExpr> = inst
            .pkg
            .state
            .iter()
            .map(|(name, _tipe)| {
                if name == field_name {
                    found = true;
                    value.clone().into()
                } else {
                    // we can unwrap here because this only returns none
                    // if the field doesn't exist, which can't happen here
                    // because we iterate over the fields.
                    self.smt_access_pkgstate(state.clone(), name).unwrap()
                }
            })
            .collect();

        if !found {
            return None;
        }

        let mut constructor_fncall =
            vec![names::pkgstate_constructor_name(game_name, inst_name).into()];
        constructor_fncall.extend(args);
        // constructor_fncall.push(
        //     names::intermediate_package_instance_state_no_constructor_name(game_name, inst_name)
        //         .into(),
        // );

        Some(SmtExpr::List(constructor_fncall))
    }

    // we need a type that has all the oracle intermediate states as as sumtype sort
    /*
    pub fn smt_declare_intermediate_oraclestates(&self) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];

        let game_name = &game.name;
        let inst_name = &inst.name;

        let mut fields = vec![(
            names::intermediate_package_instance_state_no_constructor_name(game_name, inst_name),
            vec![],
        )];

        for i in 0..inst.pkg.oracles.len() {
            let octx = self.oracle_ctx_by_oracle_offs(i).unwrap();
            let oracle_name = &octx.oracle_def().sig.name;
            let oracle_sort_name =
                names::intermediate_oracle_state_sort_name(game_name, inst_name, oracle_name);
            let oracle_const_name = names::intermediate_package_instance_state_constructor_name(
                game_name,
                inst_name,
                oracle_name,
            );

            let oracle_sel_name = names::intermediate_package_instance_state_selector_name(
                game_name,
                inst_name,
                oracle_name,
            );

            fields.push((
                oracle_const_name,
                vec![(oracle_sel_name, oracle_sort_name.into())],
            ));
        }

        let sort_name = names::intermediate_package_instance_state_sort_name(game_name, inst_name);

        declare::declare_datatype(&sort_name, fields.into_iter())
    }
    */

    // we need to add that sort to the oracle state
}
