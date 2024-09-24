use super::patterns::{game_consts, pkg_consts, DatastructurePattern};
use crate::{
    parser::tests::*,
    writers::smt::{
        exprs::SmtExpr,
        patterns::{
            const_mapping::define_fun,
            game_consts::{GameConstsSelector, GameConstsSort},
            pkg_consts::{PackageConstsSelector, PackageConstsSort},
        },
    },
};

#[test]
fn test_const_datatypes_eq_small_small() {
    let pkgs = packages::parse_files(&["tiny.ssp"]);
    let games = games::parse_files(&["small.ssp"], &pkgs);
    let proof = proofs::parse_file("equivalence-small-small.ssp", &pkgs, &games);

    let equivalence = proof
        .game_hops
        .iter()
        .find_map(|hop| hop.as_equivalence())
        .unwrap();

    let game_inst = proof.find_game_instance(equivalence.left_name()).unwrap();
    let game = &game_inst.game;
    let game_name = game.name();
    let game = &games[game_name];

    let game_const_pattern = game_consts::GameConstsPattern { game_name };
    let game_const_spec = game_const_pattern.datastructure_spec(game);

    let game_const_constructors = &game_const_spec.0;
    assert_eq!(game_const_constructors.len(), 1);
    let (_, game_const_selectors) = &game_const_constructors[0];
    assert_eq!(game_const_selectors.len(), game.consts.len());

    for GameConstsSelector { name, ty } in game_const_selectors {
        let (_, const_ty) = game
            .consts
            .iter()
            .find(|(const_name, _ty)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let pkg_inst = &game.pkgs[0];
    let pkg_inst_name = &pkg_inst.name;
    let pkg = &pkg_inst.pkg;
    let pkg_name = &pkg.name;
    let pkg = &pkgs[pkg_name];

    let pkg_const_pattern = pkg_consts::PackageConstsPattern { pkg_name };
    let pkg_const_spec = pkg_const_pattern.datastructure_spec(pkg);

    let pkg_const_constructors = &pkg_const_spec.0;
    assert_eq!(pkg_const_constructors.len(), 1);
    let (_, pkg_const_selectors) = &pkg_const_constructors[0];
    assert_eq!(pkg_const_selectors.len(), 1);

    for PackageConstsSelector { name, ty } in pkg_const_selectors {
        let (_, const_ty, _) = pkg
            .params
            .iter()
            .find(|(const_name, _ty, _)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let mapping = define_fun(game, pkg, pkg_inst_name).unwrap();
    let args = &mapping.args;

    // takes a single argument as described here
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].0, "<game-consts>");
    assert_eq!(args[0].1, GameConstsSort { game_name }.into());

    // returns a package const
    assert_eq!(mapping.ty, PackageConstsSort { pkg_name });

    let bindings = &mapping.body.bindings;
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "n");
}

#[test]
fn test_const_datatypes_remap_consts() {
    let pkgs = packages::parse_files(&["tiny.ssp"]);
    let game = games::parse_file("small_remap_consts.ssp", &pkgs);

    let game_name = game.name();

    let game_const_pattern = game_consts::GameConstsPattern { game_name };
    let game_const_spec = game_const_pattern.datastructure_spec(&game);

    let game_const_constructors = &game_const_spec.0;
    assert_eq!(game_const_constructors.len(), 1);
    let (_, game_const_selectors) = &game_const_constructors[0];
    assert_eq!(game_const_selectors.len(), game.consts.len());

    for GameConstsSelector { name, ty } in game_const_selectors {
        let (_, const_ty) = game
            .consts
            .iter()
            .find(|(const_name, _ty)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let pkg_inst = &game.pkgs[0];
    let pkg_inst_name = &pkg_inst.name;
    let pkg = &pkg_inst.pkg;
    let pkg_name = &pkg.name;
    let pkg = &pkgs[pkg_name];

    let pkg_const_pattern = pkg_consts::PackageConstsPattern { pkg_name };
    let pkg_const_spec = pkg_const_pattern.datastructure_spec(pkg);

    let pkg_const_constructors = &pkg_const_spec.0;
    assert_eq!(pkg_const_constructors.len(), 1);
    let (_, pkg_const_selectors) = &pkg_const_constructors[0];
    assert_eq!(pkg_const_selectors.len(), 1);

    for PackageConstsSelector { name, ty } in pkg_const_selectors {
        let (_, const_ty, _) = pkg
            .params
            .iter()
            .find(|(const_name, _ty, _)| name == const_name)
            .unwrap();
        assert_eq!(ty, &const_ty);
    }

    let mapping = define_fun(&game, pkg, pkg_inst_name).unwrap();
    let args = &mapping.args;

    // takes a single argument as described here
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].0, "<game-consts>");
    assert_eq!(args[0].1, GameConstsSort { game_name }.into());

    // returns a package const
    assert_eq!(mapping.ty, PackageConstsSort { pkg_name });

    let bindings = &mapping.body.bindings;

    println!("bindings: {bindings:?}");
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "m");

    let constructor = &mapping.body.body;
    println!("body: {:?}", mapping.body.body);
    let SmtExpr::List(constructor_list) = constructor else {
        panic!("expected list in body, got {constructor}")
    };

    assert_eq!(constructor_list.len(), 2);
    assert_eq!(constructor_list[0].to_string(), "<mk-pkg-consts-TinyPkg>");
    assert_eq!(constructor_list[1].to_string(), "(+ m 1)\n");
}
