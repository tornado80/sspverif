use crate::{
    package::{Composition, PackageInstance},
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            datastructures::{game_consts::GameConstsSort, pkg_consts::PackageConstsSort},
            game_consts::bind_game_consts,
            pkg_consts::{PackageConstsDeclareInfo, PackageConstsPattern},
            DatastructurePattern, FunctionPattern,
        },
    },
};

pub struct ConstMappingFunction<'a> {
    pub game_name: &'a str,
    pub pkg_name: &'a str,
    pub pkg_inst_name: &'a str,
}

impl<'a> FunctionPattern for ConstMappingFunction<'a> {
    type ReturnSort = PackageConstsSort<'a>;

    fn function_name(&self) -> String {
        let Self {
            game_name,
            pkg_inst_name,
            ..
        } = self;

        format!("<pkg-consts-{game_name}-{pkg_inst_name}>")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        vec![(
            "<game-consts>".to_string(),
            GameConstsSort {
                game_name: self.game_name,
            }
            .into(),
        )]
    }

    fn function_return_sort(&self) -> Self::ReturnSort {
        PackageConstsSort {
            pkg_name: self.pkg_name,
        }
    }
}

pub fn define_fun(game: &Composition, pkg_inst_name: &str) -> Option<SmtExpr> {
    let pkg_inst = game
        .pkgs
        .iter()
        .find(|pkg_inst| pkg_inst.name == pkg_inst_name)?;

    let pkg = &pkg_inst.pkg;
    let pkg_name = &pkg.name;

    let mapping_fun = ConstMappingFunction {
        game_name: game.name(),
        pkg_inst_name,
        pkg_name,
    };

    let pkg_consts = PackageConstsPattern { pkg_name };
    let pkg_consts_declare_info = PackageConstsDeclareInfo { pkg };
    let pkg_consts_spec = pkg_consts.datastructure_spec(&pkg_consts_declare_info);

    Some(
        mapping_fun.define_fun(bind_game_consts(
            game,
            &"<game-consts>".into(),
            pkg_consts
                .call_constructor(&pkg_consts_spec, &(), |sel| {
                    pkg_inst
                        .params
                        .iter()
                        .find(|(name, _)| name.ident_ref() == sel.name)
                        .map(|(_, expr)| expr.clone().into())
                })
                .unwrap(),
        )),
    )
}
