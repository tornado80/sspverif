use crate::{
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    types::Type,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            game_consts::GameConstsPattern, instance_names::encode_params,
            DatastructurePattern as _, FunctionPattern, GameStatePattern, ReturnPattern,
            ReturnSort,
        },
    },
};

pub const ORACLE_ARG_GAME_STATE: &str = "__global_state";
pub const ORACLE_ARG_INTERMEDIATE_STATE: &str = "__intermediate_state";

pub struct OraclePattern<'a> {
    pub game_name: &'a str,
    pub pkg_name: &'a str,
    pub oracle_name: &'a str,
    pub oracle_args: &'a [(String, Type)],
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
}

impl<'a> OraclePattern<'a> {
    fn pkg_expr_params(&self) -> impl Iterator<Item = &Expression> {
        self.pkg_params.iter().map(|(_, expr)| expr)
    }

    fn game_expr_params(&self) -> impl Iterator<Item = &Expression> {
        self.game_params.iter().map(|(_, expr)| expr)
    }
}

impl<'a> FunctionPattern for OraclePattern<'a> {
    type ReturnSort = ReturnSort<'a>;

    fn function_name(&self) -> String {
        let Self {
            game_name,
            pkg_name,
            oracle_name,
            ..
        } = self;

        let encoded_game_params = encode_params(self.pkg_expr_params());
        let encoded_pkg_params = encode_params(self.pkg_expr_params());

        format!("<oracle-{game_name}-{encoded_game_params}-{pkg_name}-{encoded_pkg_params}-{oracle_name}>")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        let Self {
            game_name,
            game_params,
            oracle_args,
            ..
        } = self;

        // build the (name sort) tuple for the game state variable
        let game_state_pair = (
            "<game-state>".to_string(),
            GameStatePattern {
                game_name,
                params: game_params,
            }
            .sort()
            .into(),
        );

        let game_const_pair = (
            "<game-consts>".to_string(),
            GameConstsPattern { game_name }.sort().into(),
        );

        vec![game_state_pair, game_const_pair]
            .into_iter()
            .chain(
                oracle_args
                    .iter()
                    .cloned()
                    .map(|(name, tipe)| (name, tipe.into())),
            )
            .collect()
    }

    fn function_return_sort(&self) -> ReturnSort<'a> {
        let Self {
            game_name,
            pkg_name,
            oracle_name,
            game_params,
            pkg_params,
            ..
        } = self;

        ReturnPattern {
            game_name,
            pkg_name,
            oracle_name,
            game_params: game_params.clone(),
            pkg_params: pkg_params.clone(),
        }
        .sort()
    }
}
