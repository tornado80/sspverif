//#![feature(backtrace)]

use std::collections::HashMap;
//use std::fmt;

mod expressions;
mod identifier;
mod package;
mod smtgen;
mod statement;
mod transforms;
mod types;
mod examples;

use crate::package::Composition;
use crate::smtgen::{CompositionSmtWriter, SmtFmt, SmtPackageState};
use crate::types::Type;

use crate::transforms::{Transformation,
                        treeify::Transformation as Treeify,
                        returnify::Transformation as Returnify};

fn main() {
    let mut params = HashMap::new();
    params.insert("n".to_string(), "256".to_string());

    let prf_real_game = examples::monoprf::mono_prf(&params);
    let key_real_pkg = examples::keypkg::key_pkg(&params);
    let mod_prf_real_pkg = examples::modprf::mod_prf(&params);

        
    let mod_prf_game = Composition {
        pkgs: vec![key_real_pkg.clone(), mod_prf_real_pkg.clone()],
        edges: vec![(1, 0, key_real_pkg.pkg.clone().oracles[1].sig.clone())],
        exports: vec![
            (0, key_real_pkg.pkg.clone().oracles[0].sig.clone()),
            (1, mod_prf_real_pkg.pkg.clone().oracles[0].sig.clone()),
        ],
        name: "real".to_string(),
    };

    let prf_real_game = Composition {
        pkgs: vec![prf_real_game.clone()],
        edges: vec![],
        exports: prf_real_game
            .get_oracle_sigs()
            .iter()
            .map(|osig| (0, osig.clone()))
            .collect(),
        name: String::from("mono-prf-game"),
    };

    let prf_real_game =
        crate::transforms::typecheck::Transform::new_with_empty_scope(prf_real_game)
            .transform()
            .expect("typecheck of prf real game failed")
            .0;

    let prf_real_game =
        Treeify(&prf_real_game)
            .transform()
            .expect("treeify of prf real game failed").0;
    let prf_real_game =
        Returnify(&prf_real_game)
            .transform()
            .expect("returnify of prf real game failed").0;

    use crate::smtgen::SmtExpr;

    let bits_n_smt = SmtExpr::List(vec![
        SmtExpr::Atom(String::from("declare-sort")),
        SmtExpr::Atom(String::from("Bits_n")),
        SmtExpr::Atom(String::from("0")),
    ]);
    bits_n_smt.write_smt_to(&mut std::io::stdout()).unwrap();
    println!();

    let bits_ast_smt = SmtExpr::List(vec![
        SmtExpr::Atom(String::from("declare-sort")),
        SmtExpr::Atom(String::from("Bits_*")),
        SmtExpr::Atom(String::from("0")),
    ]);
    bits_ast_smt.write_smt_to(&mut std::io::stdout()).unwrap();
    println!();

    println!("(declare-const bot Bits_n)");
    println!("(declare-fun __sample-rand-mono-prf-game (Int) Bits_n)");
    println!("(declare-fun __sample-rand-real (Int) Bits_n)");
    println!(
        "(assert (forall ((n Int)) (= (__sample-rand-real n) (__sample-rand-mono-prf-game n))))"
    );

    SmtPackageState::new(
        &prf_real_game.name,
        "__randomness",
        vec![("ctr".into(), Type::Integer)],
    )
    .smt_declare_datatype()
    .write_smt_to(&mut std::io::stdout())
    .unwrap();

    SmtPackageState::new(
        &mod_prf_game.name,
        "__randomness",
        vec![("ctr".into(), Type::Integer)],
    )
    .smt_declare_datatype()
    .write_smt_to(&mut std::io::stdout())
    .unwrap();

    //    println!("(declare-datatype State___randomness ((mk-state-__randomness (state-__randomness-ctr Int))))");

    let mod_prf_game = transforms::typecheck::Transform::new_with_empty_scope(mod_prf_game)
        .transform()
        .expect("typecheck of mod_prf_game failed")
        .0;

    let mod_prf_game = Treeify(&mod_prf_game)
        .transform()
        .expect("treeify of mod_prf_game failed").0;
    let mod_prf_game = Returnify(&mod_prf_game)
        .transform()
        .expect("returnify of mod_prf_game failed").0;

    eprintln!("smt expression of real composition");

    println!("; Ze PRF");
    println!("(declare-fun f (Bits_n Bits_*) Bits_*)");
    println!();

    println!(";;;;; Real Mono PRF");
    println!("; Real Mono PRF State Types");

    let prf_real_game_writer = CompositionSmtWriter::new(&prf_real_game);

    let smt_lines = prf_real_game_writer.smt_composition_state();
    for line in smt_lines {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }
    println!();
    println!("; Real Mono PRF Return Types");

    let smt_lines = prf_real_game_writer.smt_composition_return();
    for line in smt_lines {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }
    println!();
    println!("; Real Mono PRF Oracle Code");
    let smt_lines = prf_real_game_writer.code_smt();
    for line in smt_lines {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }

    let mod_prf_game_writer = CompositionSmtWriter::new(&mod_prf_game);

    println!(";;;;; Real Mod PRF Game");
    println!("; Real Mod PRF State Types");
    for line in mod_prf_game_writer.smt_composition_state() {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }
    println!();
    println!("; Real Mod PRF Return Types");
    for line in mod_prf_game_writer.smt_composition_return() {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }
    println!();
    println!("; Real Mod PRF Oracle Code");
    for line in mod_prf_game_writer.code_smt() {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }

    println!("(check-sat)");
    println!("(get-model)");
}
