//#![feature(backtrace)]

use std::collections::HashMap;
//use std::fmt;

mod errors;
mod expressions;
mod identifier;
mod package;
mod scope;
mod smtgen;
mod statement;
mod types;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, OracleDef, OracleSig, Package, PackageInstance};
use crate::scope::Scope;
use crate::smtgen::{CompositionSmtWriter, SmtFmt, SmtPackageState};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

fn main() {
    let mut params = HashMap::new();
    params.insert("n".to_string(), "256".to_string());

    let prf_real_game = PackageInstance {
        name: "mono-prf".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
                (
                    "f".to_string(),
                    Type::new_fn(
                        vec![Type::new_bits("n"), Type::new_bits("*")],
                        Type::new_bits("*"),
                    ),
                ),
            ],
            state: vec![("k".to_string(), Type::new_bits("n"))],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("k_".to_string(), Type::new_bits("n"))],
                        tipe: Type::Empty,
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::Bot,
                            ]),
                            block! {
                                Statement::Assign(Identifier::new_scalar("k"),
                                                Expression::Sample(Type::new_bits("n")),
                                )},
                            block! {
                                Statement::Abort
                            },
                        )
                    },
                },
                OracleDef {
                    sig: OracleSig {
                        name: "Eval".to_string(),
                        args: vec![("msg".to_string(), Type::new_bits("*"))],
                        tipe: Type::new_bits("*"),
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::Bot,
                            ]),
                            block! {Statement::Abort},
                            block! {},
                        ),
                        Statement::Return(Some(fncall! { "f",
                                                          Identifier::new_scalar("k").to_expression(),
                                                          Identifier::new_scalar("msg").to_expression()
                        }))
                    },
                },
            ],
        },
    };

    let key_real_pkg = PackageInstance {
        name: "key".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![("n".to_string(), Type::new_scalar("int"))],
            state: vec![("k".to_string(), Type::new_bits("n"))],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("k_".to_string(), Type::new_bits("n"))],
                        tipe: Type::Empty,
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::Bot,
                            ]),
                            block! {
                                Statement::Assign(Identifier::new_scalar("k"),
                                                Expression::Sample(Type::new_bits("n")),
                                )},
                            block! {
                                Statement::Abort
                            },
                        )
                    },
                },
                OracleDef {
                    sig: OracleSig {
                        name: "Get".to_string(),
                        args: vec![],
                        tipe: Type::new_bits("n"),
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::Bot,
                            ]),
                            block! {Statement::Abort},
                            block! {},
                        ),
                        Statement::Return(Some(Identifier::new_scalar("k").to_expression()))
                    },
                },
            ],
        },
    };

    let mod_prf_real_pkg = PackageInstance {
        name: "mod-prf".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
                (
                    "f".to_string(),
                    Type::new_fn(
                        vec![Type::new_bits("n"), Type::new_bits("*")],
                        Type::new_bits("*"),
                    ),
                ),
            ],
            state: vec![],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: "Eval".to_string(),
                    args: vec![("msg".to_string(), Type::new_bits("*"))],
                    tipe: Type::new_bits("*"),
                },
                code: block! {
                    Statement::Assign(Identifier::new_scalar("k"), Expression::OracleInvoc("Get".to_string(), vec![])), // TODO figure out why the macro doesn't work (and why it's a macro and not a function)
                    Statement::Return(Some(fncall! { "f",
                                                      Identifier::new_scalar("k").to_expression(),
                                                      Identifier::new_scalar("msg").to_expression()
                    }))
                },
            }],
        },
    };

    let mod_prf_game = Composition {
        pkgs: vec![key_real_pkg.clone(), mod_prf_real_pkg.clone()],
        edges: vec![(1, 0, key_real_pkg.pkg.clone().oracles[1].sig.clone())],
        exports: vec![
            (0, key_real_pkg.pkg.clone().oracles[0].sig.clone()),
            (1, mod_prf_real_pkg.pkg.clone().oracles[0].sig.clone()),
        ],
        name: "real".to_string(),
    };

    let mut scope: Scope = Scope::new();

    {
        let PackageInstance { pkg, .. } = prf_real_game.clone();
        eprintln!(
            "typecheck mono prf package: {:#?}",
            pkg.typecheck(&mut scope)
        );
        eprintln!("scope now: {:?}", scope);
    }

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

    let mut scope: Scope = Scope::new();
    eprintln!(
        "modular game typecheck: {:#?}",
        mod_prf_game.typecheck(&mut scope)
    );

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
