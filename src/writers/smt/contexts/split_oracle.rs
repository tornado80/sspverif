use crate::writers::smt::{exprs::SmtExpr, names};

use super::SplitOracleContext;

impl<'a> SplitOracleContext<'a> {
    pub fn smt_arg_name(&self, arg_name: &str) -> SmtExpr {
        let game = self.game_ctx.game;
        let inst = &game.pkgs[self.inst_offs];
        let odef = &inst.pkg.oracles[self.split_oracle_offs];

        names::oracle_split_arg_name(&game.name, &odef.sig.name, arg_name).into()
    }
}
