use crate::{
    proof::GameInstance,
    transforms::samplify::SampleInfo,
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

#[derive(Clone, Debug, Copy)]
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

#[derive(Copy, Clone, Debug)]
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

pub trait GenericOracleContext<'a> {
    fn game_inst_ctx(&self) -> GameInstanceContext<'a>;
    fn pkg_inst_ctx(&self) -> PackageInstanceContext<'a>;

    fn oracle_name(&self) -> &'a str;
    fn oracle_args(&self) -> &'a [(String, Type)];
    fn oracle_return_type(&self) -> &'a Type;

    fn smt_write_back_state(&self, sample_info: &SampleInfo) -> SmtExpr;
    fn smt_game_state(&self) -> SmtExpr;

    fn smt_construct_abort<S: Into<SmtExpr>>(&self, game_state: S) -> SmtExpr;

    fn smt_call_oracle_fn<
        GameState: Into<SmtExpr>,
        GameConsts: Into<SmtExpr>,
        Args: IntoIterator<Item = SmtExpr>,
    >(
        &self,
        game_state: GameState,
        game_consts: GameConsts,
        args: Args,
    ) -> Option<SmtExpr>;
}
