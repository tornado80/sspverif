use std::backtrace;

use crate::expressions::Expression;
use crate::package::{Export, OracleDef};
use crate::transforms::split_partial::SplitInfo;
use crate::types::Type;

use super::super::exprs::SmtExpr;
use super::super::{declare, names};

use super::{GameContext, GenericOracleContext, OracleContext, PackageInstanceContext};

impl<'a> OracleContext<'a> {
    pub fn is_exported(&self) -> bool {
        let export_needle = Export(self.inst_offs, self.oracle_def().sig.clone());
        self.game_ctx.game.exports.contains(&export_needle)
    }

    pub fn is_split(&self) -> bool {
        println!(
            "oracle_ctx.is_split called from {}",
            backtrace::Backtrace::force_capture()
        );
        false
    }

    pub fn smt_arg_name(&self, arg_name: &str) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let odef = &inst.pkg.oracles[self.oracle_offs];

        names::oracle_nonsplit_arg_name(&odef.sig.name, arg_name).into()
    }

    pub fn oracle_def(&self) -> &OracleDef {
        &self.game_ctx.game.pkgs[self.inst_offs].pkg.oracles[self.oracle_offs]
    }

    pub fn smt_sort_return(&self) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        names::return_sort_name(game_name, inst_name, oracle_name).into()
    }

    pub fn smt_declare_return(&self) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        let fields = vec![
            (
                names::return_selector_state_name(game_name, inst_name, oracle_name),
                self.game_ctx.smt_sort_gamestates(),
            ),
            (
                names::return_selector_state_length_name(game_name, inst_name, oracle_name),
                Type::Integer.into(),
            ),
            (
                names::return_selector_value_name(game_name, inst_name, oracle_name),
                Type::Maybe(Box::new(osig.tipe.clone())).into(),
            ),
            (
                names::return_selector_is_abort_name(game_name, inst_name, oracle_name),
                Type::Boolean.into(),
            ),
        ];

        declare::declare_single_constructor_datatype(
            &names::return_sort_name(game_name, inst_name, oracle_name),
            &names::return_constructor_name(game_name, inst_name, oracle_name),
            fields.into_iter(),
        )
    }

    pub fn smt_construct_return<S, SL, V, ISAB>(
        &self,
        state: S,
        state_len: SL,
        value: V,
        is_abort: ISAB,
    ) -> SmtExpr
    where
        S: Into<SmtExpr>,
        SL: Into<SmtExpr>,
        V: Into<SmtExpr>,
        ISAB: Into<SmtExpr>,
    {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let odef = &inst.pkg.oracles[self.oracle_offs];

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &odef.sig.name;

        (
            names::return_constructor_name(game_name, inst_name, oracle_name),
            state,
            state_len,
            value,
            is_abort,
        )
            .into()
    }

    pub(crate) fn smt_access_intermediate_parent<IS: Into<SmtExpr>>(
        &self,
        old_gamestate: IS,
    ) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let odef = &inst.pkg.oracles[self.oracle_offs];

        let game_name = &game.name;
        let oracle_name = &odef.sig.name;

        (
            names::intermediate_state_selector_parent(game_name, oracle_name),
            old_gamestate,
        )
            .into()
    }

    pub(crate) fn smt_construct_next_intermediate_state<IS: Into<SmtExpr> + std::fmt::Debug>(
        &self,
        split_info: &SplitInfo,
        parent: IS,
    ) -> Option<SmtExpr> {
        let game_name = &self.game_ctx.game.name;
        let pkg_inst_name = self.pkg_inst_ctx().pkg_inst_name();
        let oracle_name = &self.oracle_def().sig.name;

        let entry = split_info.iter().find(|entry| {
            entry.pkg_inst_name() == pkg_inst_name && entry.oracle_name() == oracle_name
        })?;

        let next_path = entry.next()?;
        let next_entry = split_info
            .iter()
            .find(|entry| entry.path() == next_path)
            .unwrap();

        let mut fn_call =
            vec![names::intermediate_state_constructor(game_name, &next_path.smt_name()).into()];
        for (local_name, _local_type) in next_entry.locals() {
            fn_call.push(local_name.clone().into());
        }

        println!("TTTTT {parent:?}");
        fn_call.push(parent.into());

        Some(SmtExpr::List(fn_call))
    }

    pub fn smt_access_return_state<R>(&self, ret: R) -> SmtExpr
    where
        R: Into<SmtExpr>,
    {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        (
            names::return_selector_state_name(game_name, inst_name, oracle_name),
            ret,
        )
            .into()
    }

    pub fn smt_select_return_state<R, L>(&self, ret: R, state_length: L) -> SmtExpr
    where
        R: Into<SmtExpr>,
        L: Into<SmtExpr>,
    {
        ("select", self.smt_access_return_state(ret), state_length).into()
    }

    pub fn smt_store_return_state<R: Into<SmtExpr>, L: Into<SmtExpr>, S: Into<SmtExpr>>(
        &self,
        ret: R,
        state_length: L,
        state: S,
    ) -> SmtExpr {
        (
            "store",
            self.smt_access_return_state(ret),
            state_length,
            state,
        )
            .into()
    }

    pub fn smt_access_return_state_length<R: Into<SmtExpr>>(&self, ret: R) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        (
            names::return_selector_state_length_name(game_name, inst_name, oracle_name),
            ret,
        )
            .into()
    }

    pub fn smt_access_return_is_abort<R: Into<SmtExpr>>(&self, ret: R) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        (
            names::return_selector_is_abort_name(game_name, inst_name, oracle_name),
            ret,
        )
            .into()
    }

    pub fn smt_access_return_value<R: Into<SmtExpr>>(&self, ret: R) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        (
            names::return_selector_value_name(game_name, inst_name, oracle_name),
            ret,
        )
            .into()
    }

    // returns none if the wrong number of arguments were provided
    pub fn smt_invoke_oracle<S, SLEN, ARGS>(
        &self,
        gamestates: S,
        state_length: SLEN,
        args: ARGS,
    ) -> Option<SmtExpr>
    where
        S: Into<SmtExpr>,
        SLEN: Into<SmtExpr>,
        ARGS: Iterator<Item = SmtExpr>,
    {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        let expected_len = 3 + osig.args.len();

        let mut cmdline = Vec::with_capacity(expected_len);
        cmdline.push(names::oracle_function_name(game_name, inst_name, oracle_name).into());
        cmdline.push(gamestates.into());
        cmdline.push(state_length.into());
        cmdline.extend(args);

        if cmdline.len() != expected_len {
            return None;
        }

        Some(SmtExpr::List(cmdline))
    }
}

impl<'a> GenericOracleContext for OracleContext<'a> {
    fn game_ctx(&self) -> GameContext {
        self.game_ctx.clone()
    }

    fn pkg_inst_ctx(&self) -> PackageInstanceContext {
        PackageInstanceContext {
            game_ctx: self.game_ctx.clone(),
            inst_offs: self.inst_offs,
        }
    }

    fn oracle_name(&self) -> &str {
        &self.oracle_def().sig.name
    }

    fn oracle_return_type(&self) -> &Type {
        &self.oracle_def().sig.tipe
    }

    fn smt_construct_abort<S, SL>(&self, state: S, state_len: SL) -> SmtExpr
    where
        S: Into<SmtExpr>,
        SL: Into<SmtExpr>,
    {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let osig = &inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = &game.name;
        let inst_name = &inst.name;
        let oracle_name = &osig.name;

        (
            names::return_constructor_name(game_name, inst_name, oracle_name),
            state,
            state_len,
            Expression::None(osig.tipe.clone()),
            "true",
        )
            .into()
    }
}
