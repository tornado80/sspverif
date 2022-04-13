//#![feature(backtrace)]

use std::collections::HashMap;

use sspds::hacks::{declare_par_Maybe, declare_tuples};
use sspds::package::Composition;
use sspds::smt::exprs::{SmtExpr, SmtFmt};
use sspds::smt::writer::CompositionSmtWriter;

fn main() {
    let mut params = HashMap::new();
    params.insert("n".to_string(), "256".to_string());

    let prf_real_game = sspds::examples::monoprf::mono_prf(&params);
    let key_real_pkg = sspds::examples::keypkg::key_pkg(&params);
    let mod_prf_real_pkg = sspds::examples::modprf::mod_prf(&params);
    let no_mapping_game = sspds::examples::nomapping::no_mapping_game(&params);
    let mapping_game = sspds::examples::mapping::mapping_game(&params);

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


    declare_tuples(10);
    declare_par_Maybe();

    println!("(declare-const bot (Maybe Bits_n))");

    println!("; The PRF");
    println!("(declare-fun f (Bits_n Bits_*) Bits_n)");
    println!();

    // println!(";;;;; Real Mono PRF Game");
    // let (prf_real_game, _) = sspds::transforms::transform_all(&prf_real_game).unwrap();
    // let prf_real_game_writer = CompositionSmtWriter::new(&prf_real_game);
    // for line in prf_real_game_writer.smt_composition_all() {
    //     line.write_smt_to(&mut std::io::stdout()).unwrap();
    //     println!();
    // }

    // println!(";;;;; Real Mod PRF Game");
    // let (mod_prf_game, _) = sspds::transforms::transform_all(&mod_prf_game).unwrap();
    // let mod_prf_game_writer = CompositionSmtWriter::new(&mod_prf_game);
    // for line in mod_prf_game_writer.smt_composition_all() {
    //     line.write_smt_to(&mut std::io::stdout()).unwrap();
    //     println!();
    // }

    println!(";;;;; No Mapping Game");
    let (no_mapping_game, _) = sspds::transforms::transform_all(&no_mapping_game).unwrap();
    let no_mapping_game_writer = CompositionSmtWriter::new(&no_mapping_game);
    for line in no_mapping_game_writer.smt_composition_all() {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }

    println!(";;;;; Mapping Game");
    let (mapping_game, _) = sspds::transforms::transform_all(&mapping_game).unwrap();
    let mapping_game_writer = CompositionSmtWriter::new(&mapping_game);
    for line in mapping_game_writer.smt_composition_all() {
        line.write_smt_to(&mut std::io::stdout()).unwrap();
        println!();
    }

    // println!(
    //     "(assert (forall ((n Int)) (= (__sample-rand-real n) (__sample-rand-mono-prf-game n))))"
    // );
    println!("(check-sat)");
    println!("(get-model)");
}
