use std::backtrace;

use crate::package::{Export, OracleDef};
use crate::types::Type;
use crate::writers::smt::patterns::{
    declare_datatype, DatastructurePattern, OraclePattern, ReturnConstructor, ReturnPattern,
    ReturnSelector, ReturnValue, ReturnValueConstructor,
};

use super::super::exprs::SmtExpr;
use super::super::names;

use super::{GameInstanceContext, GenericOracleContext, OracleContext, PackageInstanceContext};

impl<'a> OracleContext<'a> {
    pub fn is_exported(&self) -> bool {
        let export_needle = Export(self.pkg_inst_offs, self.oracle_def().sig.clone());
        self.game_inst_context
            .game_inst
            .game()
            .exports
            .contains(&export_needle)
    }

    pub fn is_split(&self) -> bool {
        println!(
            "oracle_ctx.is_split called from {}",
            backtrace::Backtrace::force_capture()
        );
        false
    }

    pub fn oracle_pattern(&'a self) -> OraclePattern<'a> {
        let game_inst_name = self.game_inst_context.game_inst().name();
        let pkg_inst_name = self.pkg_inst_ctx().pkg_inst_name();
        let oracle_name = self.oracle_name();
        let oracle_args = self.oracle_args();

        OraclePattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
            oracle_args,
        }
    }

    pub fn smt_arg_name(&self, arg_name: &str) -> SmtExpr {
        let game = self.game_inst_context.game_inst.game();
        let pkg_inst = &game.pkgs[self.pkg_inst_offs];
        let odef = &pkg_inst.pkg.oracles[self.oracle_offs];

        names::oracle_nonsplit_arg_name(&odef.sig.name, arg_name).into()
    }

    pub fn oracle_def(&self) -> &'a OracleDef {
        &self.game_inst_context.game_inst.game().pkgs[self.pkg_inst_offs]
            .pkg
            .oracles[self.oracle_offs]
    }

    pub fn smt_sort_return(&self) -> SmtExpr {
        let game_inst = &self.game_inst_context.game_inst;
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;

        let game_inst_name = game_inst.name();
        let pkg_inst_name = &pkg_inst.name;
        let oracle_name = &osig.name;

        ReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        }
        .sort()
        .into()
    }

    pub fn smt_declare_return(&self) -> SmtExpr {
        let game_inst = &self.game_inst_context.game_inst;
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;

        let game_inst_name = game_inst.name();
        let pkg_inst_name = &pkg_inst.name;
        let oracle_name = &osig.name;
        let return_type = &osig.tipe;

        let pattern = ReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        };

        let spec = pattern.datastructure_spec(&return_type);

        declare_datatype(&pattern, &spec)
    }

    pub fn smt_construct_return<S, V>(&self, state: S, value: V) -> SmtExpr
    where
        S: Into<SmtExpr>,
        V: Into<SmtExpr>,
    {
        let game_inst = self.game_inst_context.game_inst;
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let odef = &pkg_inst.pkg.oracles[self.oracle_offs];
        let osig = &odef.sig;

        let game_inst_name = game_inst.name();
        let pkg_inst_name = &pkg_inst.name;
        let oracle_name = &odef.sig.name;
        let return_type = &osig.tipe;

        let return_value_pattern = ReturnValue {
            inner_type: return_type,
        };
        let return_value_spec = return_value_pattern.datastructure_spec(&());

        // we do this here so we can clone the smt expression in the closure below
        // and don't have to require a `Clone` constraint from `value_smt`.
        let value_smt: SmtExpr = value.into();

        let return_value = return_value_pattern
            .call_constructor(&return_value_spec, &ReturnValueConstructor::Return, |_| {
                Some(value_smt.clone())
            })
            .unwrap();

        let return_pattern = ReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        };

        let return_spec = return_pattern.datastructure_spec(&return_type);

        let state_smt: SmtExpr = state.into();

        return_pattern
            .call_constructor(&return_spec, &ReturnConstructor, |sel: &ReturnSelector| {
                Some(match sel {
                    ReturnSelector::GameState => state_smt.clone(),
                    ReturnSelector::ReturnValueOrAbort {
                        return_type: spec_return_type,
                    } => {
                        assert_eq!(*spec_return_type, return_type);
                        return_value.clone()
                    }
                })
            })
            .unwrap()
    }

    pub fn smt_access_return_state<R>(&self, ret: R) -> SmtExpr
    where
        R: Into<SmtExpr>,
    {
        let game_inst = self.game_inst_context.game_inst;
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;
        let return_type = &osig.tipe;

        let game_inst_name = game_inst.name();
        let pkg_inst_name = &pkg_inst.name;
        let oracle_name = &osig.name;

        let pattern = ReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        };
        let spec = pattern.datastructure_spec(&return_type);

        pattern
            .access(&spec, &ReturnSelector::GameState, ret)
            .unwrap()
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

    pub fn smt_access_return_is_abort<R: Into<SmtExpr>>(&self, ret: R) -> SmtExpr {
        ("=", ret, self.smt_construct_abort()).into()
    }

    pub fn smt_access_return_value<R: Into<SmtExpr>>(&self, ret: R) -> SmtExpr {
        let game_inst = self.game_inst_context.game_inst;
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;
        let return_type = &osig.tipe;

        let game_inst_name = game_inst.name();
        let pkg_inst_name = &pkg_inst.name;
        let oracle_name = &osig.name;

        let pattern = ReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        };
        let spec = pattern.datastructure_spec(&return_type);

        pattern
            .access(
                &spec,
                &ReturnSelector::ReturnValueOrAbort { return_type },
                ret,
            )
            .unwrap()
    }

    // returns none if the wrong number of arguments were provided
    pub fn smt_invoke_oracle<S, ARGS>(&self, gamestates: S, args: ARGS) -> Option<SmtExpr>
    where
        S: Into<SmtExpr>,
        ARGS: Iterator<Item = SmtExpr>,
    {
        let game_inst = self.game_inst_context.game_inst;
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;

        let game_name = game_inst.name();
        let pkg_inst_name = &pkg_inst.name;
        let oracle_name = &osig.name;

        let expected_len = 2 + osig.args.len();

        let mut cmdline = Vec::with_capacity(expected_len);
        cmdline.push(names::oracle_function_name(game_name, pkg_inst_name, oracle_name).into());
        cmdline.push(gamestates.into());
        cmdline.extend(args);

        if cmdline.len() != expected_len {
            return None;
        }

        Some(SmtExpr::List(cmdline))
    }
}

impl<'a> GenericOracleContext for OracleContext<'a> {
    fn game_inst_ctx(&self) -> GameInstanceContext<'a> {
        self.game_inst_context.clone()
    }

    fn pkg_inst_ctx(&self) -> PackageInstanceContext<'a> {
        PackageInstanceContext {
            game_ctx: self.game_inst_context.clone(),
            inst_offs: self.pkg_inst_offs,
        }
    }

    fn oracle_name(&self) -> &'a str {
        &self.oracle_def().sig.name
    }

    fn oracle_args(&self) -> &'a [(String, Type)] {
        &self.oracle_def().sig.args
    }

    fn oracle_return_type(&self) -> &Type {
        &self.oracle_def().sig.tipe
    }

    fn smt_game_state(&self) -> SmtExpr {
        "__global_state".into()
    }

    fn smt_construct_abort(&self) -> SmtExpr {
        let game_inst = self.game_inst_context.game_inst;
        let pkg_inst = &game_inst.game().pkgs[self.pkg_inst_offs];
        let osig = &pkg_inst.pkg.oracles[self.oracle_offs].sig;

        let game_inst_name = game_inst.name();
        let pkg_inst_name = &pkg_inst.name;
        let oracle_name = &osig.name;
        let return_type = &osig.tipe;

        let return_value_pattern = ReturnValue {
            inner_type: &osig.tipe,
        };
        let return_value_spec = return_value_pattern.datastructure_spec(&());

        let abort = return_value_pattern
            .call_constructor(
                &return_value_spec,
                &ReturnValueConstructor::Abort,
                |_| unreachable!(),
            )
            .unwrap();

        let abort_as: SmtExpr = ("as", abort, return_value_pattern.sort()).into();

        let return_pattern = ReturnPattern {
            game_inst_name,
            pkg_inst_name,
            oracle_name,
        };

        let return_spec = return_pattern.datastructure_spec(&return_type);

        return_pattern
            .call_constructor(&return_spec, &ReturnConstructor, |sel: &ReturnSelector| {
                Some(match sel {
                    ReturnSelector::GameState => self.smt_game_state(),
                    ReturnSelector::ReturnValueOrAbort { .. } => abort_as.clone(),
                })
            })
            .unwrap()
    }
}
