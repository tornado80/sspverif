use crate::writers::smt::{
    exprs::SmtExpr,
    patterns::{
        datastructures::{game_consts::GameConstsSort, pkg_consts::PackageConstsSort},
        FunctionPattern,
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
            "game_consts".to_string(),
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
