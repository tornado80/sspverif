use crate::{
    package::Composition,
    types::Type,
    writers::smt::{exprs::SmtExpr, names},
};

pub struct GlobalContext;

impl GlobalContext {
    pub fn smt_latest_gamestate() -> SmtExpr {
        (
            "select",
            names::var_globalstate_name(),
            names::var_state_length_name(),
        )
            .into()
    }
}

mod game;
mod oracle;
mod pkg_inst;
mod split_oracle;

#[derive(Clone, Debug)]
pub struct GameContext<'a> {
    game: &'a Composition,
}

#[derive(Clone, Debug)]
pub struct SplitOracleContext<'a> {
    game_ctx: GameContext<'a>,
    inst_offs: usize,
    split_oracle_offs: usize,
}

#[derive(Clone, Debug)]
pub struct OracleContext<'a> {
    game_ctx: GameContext<'a>,
    inst_offs: usize,
    oracle_offs: usize,
}

#[derive(Clone, Debug)]
pub struct PackageInstanceContext<'a> {
    game_ctx: GameContext<'a>,
    inst_offs: usize,
}

pub trait GenericOracleContext {
    fn game_ctx(&self) -> GameContext;
    fn pkg_inst_ctx(&self) -> PackageInstanceContext;

    fn oracle_name(&self) -> &str;
    fn oracle_return_type(&self) -> &Type;

    fn smt_construct_abort<S, SL>(&self, state: S, state_len: SL) -> SmtExpr
    where
        S: Into<SmtExpr>,
        SL: Into<SmtExpr>;

    fn smt_construct_return<S, SL, V>(&self, state: S, state_len: SL, expr: V) -> SmtExpr
    where
        S: Into<SmtExpr>,
        SL: Into<SmtExpr>,
        V: Into<SmtExpr>;
}
