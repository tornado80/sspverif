use crate::{
    proof::Named,
    split::SplitOracleDef,
    writers::smt::{
        exprs::SmtExpr,
        names,
        patterns::{DatastructurePattern, FunctionPattern},
    },
};

use super::{GenericOracleContext, PackageInstanceContext, SplitOracleContext};

impl<'a> SplitOracleContext<'a> {
    pub fn smt_arg_name(&self, arg_name: &str) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let odef = &inst.pkg.oracles[self.split_oracle_offs];

        names::oracle_split_arg_name(&game.name, &odef.sig.name, arg_name).into()
    }

    pub fn oracle_def(&self) -> &SplitOracleDef {
        &self.game_ctx.game.pkgs[self.inst_offs].pkg.split_oracles[self.split_oracle_offs]
    }

    pub fn do_with_intermediate_state_pattern<R, F: FnMut(&DatastructurePattern) -> R>(
        &self,
        variant_name: &str,
        mut f: F,
    ) -> R {
        let game_ctx = self.game_ctx();
        let game = game_ctx.game();
        let pattern = DatastructurePattern::IntermediateState {
            game_name: &game.name,
            pkg_inst_name: self.pkg_inst_ctx().pkg_inst_name(),
            oracle_name: &self.oracle_def().sig.name,
            variant_name,
        };

        f(&pattern)
    }

    fn smt_construct_return<GS, PS, V>(&self, game_state: GS, partial_state: PS, expr: V) -> SmtExpr
    where
        GS: Into<SmtExpr>,
        PS: Into<SmtExpr>,
        V: Into<SmtExpr>,
    {
        let game = self.game_ctx.game();
        let game_name = &game.name;
        let inst_name = &self.pkg_inst_ctx().pkg_inst().name;
        let oracle_name_with_path = self.oracle_def().sig.name_with_path();

        (
            names::return_constructor_name(game_name, inst_name, &oracle_name_with_path),
            game_state,
            partial_state,
        )
            .into()

        /*
         *
         * (
         *   mk-partialreturn-bla-bli-blubb
         *     gamestate
         *     partialstate  -- encodes where in the state machine we are
         *     checkpoint-A  -- ignore for now, we'll add them once we add the statement type
         *     checkpoint-B  --    -"-
         *     return-value  -- no! this is in the end variant of the partial state
         *     is-abort      -- no! we use a different constructor for these
         *
         * )
         *
         *
         *
         *
         * */
    }

    fn oracle_function_pattern(&self) -> FunctionPattern {
        let game_ctx = self.game_ctx();
        let pkg_inst_ctx = self.pkg_inst_ctx();

        let game_name = &game_ctx.game.name;
        let pkg_inst_name = pkg_inst_ctx.pkg_inst_name();
        let oracle_name = self.oracle_name();
        let split_path = &self.oracle_def().sig.path;

        FunctionPattern::PartialOracle {
            game_name,
            pkg_inst_name,
            oracle_name,
            split_path,
        }
    }
}

impl<'a> GenericOracleContext for SplitOracleContext<'a> {
    fn game_ctx(&self) -> super::GameContext {
        self.game_ctx.clone()
    }

    fn pkg_inst_ctx(&self) -> super::PackageInstanceContext {
        PackageInstanceContext {
            game_ctx: self.game_ctx.clone(),
            inst_offs: self.inst_offs,
        }
    }

    fn oracle_name(&self) -> &str {
        &self.oracle_def().sig.name
    }

    fn oracle_return_type(&self) -> &crate::types::Type {
        &self.oracle_def().sig.tipe
    }

    fn smt_game_state(&self) -> SmtExpr {
        "__global_state".into()
    }

    fn smt_construct_abort<S, SL>(&self, state: S, state_len: SL) -> SmtExpr
    where
        S: Into<SmtExpr>,
        SL: Into<SmtExpr>,
    {
        let game = self.game_ctx.game();
        let game_name = &game.name;
        let inst_name = &self.pkg_inst_ctx().pkg_inst().name;
        let oracle_name_with_path = self.oracle_def().sig.name_with_path();

        SmtExpr::List(vec![names::return_constructor_abort_name(
            game_name,
            inst_name,
            &oracle_name_with_path,
        )
        .into()])
    }
}
