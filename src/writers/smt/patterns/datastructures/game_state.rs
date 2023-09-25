use crate::{
    package::Composition, transforms::samplify::SampleInfo, types::Type, writers::smt::names,
};

use super::{DatastructurePattern2, DatastructureSpec};

pub struct GameStatePattern<'a> {
    pub game_name: &'a str,
}

#[derive(PartialEq, Eq)]
pub enum GameStateSelector<'a> {
    PackageInstance { pkg_inst_name: &'a str },
    Const { const_name: &'a str, tipe: &'a Type },
    Randomness { sample_id: usize },
}

pub struct GameStateDeclareInfo<'a> {
    pub game: &'a Composition,
    pub sample_info: &'a SampleInfo,
}

impl<'a> DatastructurePattern2<'a> for GameStatePattern<'a> {
    type Constructor = ();
    type Selector = GameStateSelector<'a>;
    type DeclareInfo = GameStateDeclareInfo<'a>;

    const CAMEL_CASE: &'static str = "CompositionState";
    const KEBAB_CASE: &'static str = "composition";

    fn sort_name(&self) -> String {
        let camel_case = Self::CAMEL_CASE;
        let Self { game_name } = self;

        format!("{camel_case}-{game_name}")
    }

    fn constructor_name(&self, _cons: &Self::Constructor) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self { game_name } = self;

        format!("mk-{kebab_case}-state-{game_name}")
    }

    fn selector_name(&self, sel: &Self::Selector) -> String {
        let kebab_case = Self::KEBAB_CASE;
        let Self { game_name } = self;

        let (kind_name, field_name) = match sel {
            GameStateSelector::PackageInstance { pkg_inst_name } => {
                ("pkgstate", pkg_inst_name.to_string())
            }
            GameStateSelector::Const { const_name, .. } => ("param", const_name.to_string()),
            GameStateSelector::Randomness { sample_id } => ("rand", format!("{sample_id}")),
        };

        format!("{kebab_case}-{kind_name}-{game_name}-{field_name}")
    }

    fn matchfield_name(&self, sel: &Self::Selector) -> String {
        let (kind_name, field_name) = match sel {
            GameStateSelector::PackageInstance { pkg_inst_name } => {
                ("pkgstate", pkg_inst_name.to_string())
            }
            GameStateSelector::Const { const_name, .. } => ("param", const_name.to_string()),
            GameStateSelector::Randomness { sample_id } => ("rand", format!("{sample_id}")),
        };

        format!("match-{kind_name}-{field_name}")
    }

    fn selector_sort(&self, sel: &Self::Selector) -> crate::writers::smt::exprs::SmtExpr {
        let Self { game_name } = self;
        match sel {
            GameStateSelector::PackageInstance { pkg_inst_name } => {
                names::pkgstate_sort_name(&game_name, &pkg_inst_name).into()
            }
            GameStateSelector::Const { tipe, .. } => (*tipe).into(),
            GameStateSelector::Randomness { .. } => Type::Integer.into(),
        }
    }

    fn datastructure_spec(&self, info: &Self::DeclareInfo) -> DatastructureSpec<'a, Self> {
        let Self { game_name } = self;
        assert_eq!(game_name, &info.game.name);

        let pkgstate_selectors =
            info.game
                .pkgs
                .iter()
                .map(|inst| GameStateSelector::PackageInstance {
                    pkg_inst_name: &inst.name,
                });

        let const_selectors = info
            .game
            .consts
            .iter()
            // function parameters are just declared as smtlib functions globally, so we don't
            // want them to be part of this datatype. This way we also stay compatible with
            // solvers that don't support higher-order functions.
            .filter(|(_, tipe)| !matches!(tipe, crate::types::Type::Fn(_, _)))
            .map(|(const_name, tipe)| GameStateSelector::Const { const_name, tipe });

        let rand_selectors = (0..info.sample_info.count)
            .map(|sample_id| GameStateSelector::Randomness { sample_id });

        let fields = pkgstate_selectors
            .chain(const_selectors)
            .chain(rand_selectors)
            .collect();

        DatastructureSpec(vec![((), fields)])
    }
}
