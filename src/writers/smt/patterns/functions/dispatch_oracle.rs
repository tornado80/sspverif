use crate::{
    expressions::Expression,
    identifier::{game_ident::GameConstIdentifier, pkg_ident::PackageConstIdentifier},
    package::OracleSig,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            instance_names::encode_params, DatastructurePattern as _, FunctionPattern,
            GameStatePattern, IntermediateStatePattern, PartialReturnPattern, PartialReturnSort,
        },
    },
};

use super::oracle::{ORACLE_ARG_GAME_STATE, ORACLE_ARG_INTERMEDIATE_STATE};

pub struct DispatchOraclePattern<'a> {
    pub game_name: &'a str,
    pub game_params: &'a [(GameConstIdentifier, Expression)],
    pub pkg_name: &'a str,
    pub pkg_params: &'a [(PackageConstIdentifier, Expression)],
    pub oracle_sig: &'a OracleSig,
}

impl<'a> DispatchOraclePattern<'a> {
    fn game_expr_params(&self) -> impl Iterator<Item = &Expression> {
        self.game_params.iter().map(|(_, expr)| expr)
    }

    fn pkg_expr_params(&self) -> impl Iterator<Item = &Expression> {
        self.pkg_params.iter().map(|(_, expr)| expr)
    }
}

impl<'a> FunctionPattern for DispatchOraclePattern<'a> {
    type ReturnSort = PartialReturnSort<'a>;
    fn function_name(&self) -> String {
        let Self {
            game_name,
            pkg_name,
            oracle_sig,
            ..
        } = self;

        let game_params = encode_params(self.game_expr_params());
        let pkg_params = encode_params(self.pkg_expr_params());

        let oracle_name = &oracle_sig.name;
        format!("oracle-{game_name}-{game_params}-{pkg_name}-{pkg_params}-{oracle_name}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        let DispatchOraclePattern {
            oracle_sig,
            game_name,
            pkg_name,
            pkg_params,
            ..
        } = self;

        let oracle_name = &oracle_sig.name;
        let game_state_pattern = GameStatePattern {
            game_name,
            params: self.game_params,
        };
        let intermediate_state_pattern = IntermediateStatePattern {
            pkg_name,
            params: pkg_params,
            oracle_name,
        };

        let mut args = vec![
            (
                ORACLE_ARG_GAME_STATE.to_string(),
                game_state_pattern.sort().into(),
            ),
            (
                ORACLE_ARG_INTERMEDIATE_STATE.to_string(),
                intermediate_state_pattern.sort().into(),
            ),
        ];

        args.extend(
            oracle_sig
                .args
                .iter()
                .cloned()
                .map(|(name, tipe)| (name, tipe.into())),
        );

        args
    }

    fn function_return_sort(&self) -> PartialReturnSort<'a> {
        let Self {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_sig,
            ..
        } = self;

        let partial_return_pattern = PartialReturnPattern {
            game_name,
            game_params,
            pkg_name,
            pkg_params,
            oracle_name: &oracle_sig.name,
        };

        partial_return_pattern.sort()
    }
}
