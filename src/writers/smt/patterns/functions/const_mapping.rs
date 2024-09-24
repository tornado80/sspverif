use crate::{
    package::{Composition, Package, PackageInstance},
    writers::smt::{
        exprs::{SmtExpr, SmtLet},
        patterns::{
            datastructures::{game_consts::GameConstsSort, pkg_consts::PackageConstsSort},
            game_consts::bind_game_consts,
            pkg_consts::PackageConstsPattern,
            DatastructurePattern, FunctionPattern,
        },
    },
};

use super::SmtDefineFun;

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

pub fn define_fun<'a>(
    game: &'a Composition,
    pkg: &'a Package,
    pkg_inst_name: &'a str,
) -> Option<SmtDefineFun<SmtLet<SmtExpr>, PackageConstsSort<'a>>> {
    let pkg_inst = game
        .pkgs
        .iter()
        .find(|pkg_inst| pkg_inst.name == pkg_inst_name)?;

    if pkg_inst.pkg.name != pkg.name {
        // TODO: return an error here
        return None;
    }
    let pkg_name = &pkg.name;

    let mapping_fun = ConstMappingFunction {
        game_name: game.name(),
        pkg_inst_name,
        pkg_name,
    };

    let pkg_consts = PackageConstsPattern { pkg_name };
    let pkg_consts_spec = pkg_consts.datastructure_spec(pkg);

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
