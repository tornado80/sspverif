use crate::{
    proof::GameInstance,
    types::Type,
    writers::smt::{exprs::SmtExpr, names},
};

use super::partials::PartialsDatatype;

pub struct GlobalContext;

impl GlobalContext {
    pub fn smt_latest_gamestate() -> SmtExpr {
        ("select", names::var_globalstate_name()).into()
    }
}

//mod game;
mod game_inst;
mod oracle;
mod pkg_inst;
mod split_oracle;

#[derive(Clone, Debug)]
pub struct GameInstanceContext<'a> {
    game_inst: &'a GameInstance,
}

#[derive(Clone, Debug)]
pub struct SplitOracleContext<'a> {
    game_inst_context: GameInstanceContext<'a>,
    pkg_inst_offs: usize,
    split_oracle_offs: usize,
    partials: &'a PartialsDatatype,
}

#[derive(Clone, Debug)]
pub struct OracleContext<'a> {
    game_inst_context: GameInstanceContext<'a>,
    pkg_inst_offs: usize,
    oracle_offs: usize,
}

#[derive(Clone, Debug)]
pub struct PackageInstanceContext<'a> {
    game_ctx: GameInstanceContext<'a>,
    inst_offs: usize,
}

pub trait GenericOracleContext {
    fn game_inst_ctx(&self) -> GameInstanceContext;
    fn pkg_inst_ctx(&self) -> PackageInstanceContext;

    fn oracle_name(&self) -> &str;
    fn oracle_args(&self) -> &[(String, Type)];
    fn oracle_return_type(&self) -> &Type;

    fn smt_game_state(&self) -> SmtExpr;

    fn smt_construct_abort(&self) -> SmtExpr;
}
