//#![feature(backtrace)]

use std::collections::HashMap;
//use std::fmt;

mod types;
mod scope;
mod identifier;
mod expressions;
mod package;
mod statement;
mod errors;
mod smtgen;

use crate::types::Type;
use crate::identifier::Identifier;
use crate::scope::Scope;
use crate::statement::Statement;
use crate::package::{PackageInstance, Package, OracleDef, OracleSig};
use crate::expressions::Expression;



fn main() {
    let mut params = HashMap::new();
    params.insert("n".to_string(), "256".to_string());
    

    let prf_real_game = PackageInstance::Atom {
        params: params.clone(),
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
                ("f".to_string(), Type::new_fn(
                    vec![&Type::new_bits("n"), &Type::new_bits("*")],
                    &Type::new_bits("*"))),
            ],
            state: vec![("k".to_string(), Type::new_bits("n"))],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("k'".to_string(), Type::new_bits("n"))],
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
                        Statement::Return(fncall! { "f",
                                                    Identifier::new_scalar("k").to_expression(),
                                                    Identifier::new_scalar("msg").to_expression()
                        })
                    },
                },
            ],
        },
    };

    let key_real_pkg = PackageInstance::Atom {
        params: params.clone(),
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
            ],
            state: vec![("k".to_string(), Type::new_bits("n"))],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("k'".to_string(), Type::new_bits("n"))],
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
                        Statement::Return(Identifier::new_scalar("k").to_expression())
                    },
                },
            ],
        },
    };


    let mod_prf_real_pkg = PackageInstance::Atom {
        params: params.clone(),
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
                ("f".to_string(), Type::new_fn(
                    vec![&Type::new_bits("n"), &Type::new_bits("*")],
                    &Type::new_bits("*"))),
            ],
            state: vec![],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Eval".to_string(),
                        args: vec![("msg".to_string(), Type::new_bits("*"))],
                        tipe: Type::new_bits("*"),
                    },
                    code: block! {
                        Statement::Assign(Identifier::new_scalar("k"), Expression::OracleInvoc("Get".to_string(), vec![])), // TODO figure out why the macro doesn't work (and why it's a macro and not a function)
                        Statement::Return(fncall! { "f",
                                                    Identifier::new_scalar("k").to_expression(),
                                                    Identifier::new_scalar("msg").to_expression()
                        })
                    },
                },
            ],
        },
    };

    let mod_prf_game = PackageInstance::Composition{
        pkgs: vec![
            Box::new(key_real_pkg.clone()),
            Box::new(mod_prf_real_pkg.clone()),
        ],
        edges: vec![
            (1, 0, key_real_pkg.get_pkg().oracles[1].sig.clone())
        ],
        exports: vec![
            (0, key_real_pkg.get_pkg().oracles[0].sig.clone()),
            (1, mod_prf_real_pkg.get_pkg().oracles[0].sig.clone()),
        ],
    };


    let mut scope: Scope = Scope::new();
    if let PackageInstance::Atom { pkg, .. } = prf_real_game.clone() {
        println!("typecheck mono prf package: {:#?}", pkg.typecheck(&mut scope));
        println!("scope now: {:?}", scope);
    }

    //println!("real game: {:#?}",    prf_real_game);
    //println!("modular game: {:#?}", mod_prf_game);

    let mut scope: Scope = Scope::new();
    println!("modular game typecheck: {:#?}", mod_prf_game.typecheck(&mut scope));
    println!("scope now: {:?}", scope);

    /*
    let scope: Scope = Scope::new();
    println!(
        "xor: {:#?}",
        Expression::Xor(vec![
            Box::new(Expression::BooleanLiteral("true".to_string())),
            Box::new(Expression::BooleanLiteral("false".to_string())),
            Box::new(Expression::BooleanLiteral("true".to_string())),
            Box::new(Expression::BooleanLiteral("false".to_string())),
            Box::new(Expression::BooleanLiteral("true".to_string())),
        ])
            .get_type(&scope)
    );

    println!(
        "type of false: {:#?}",
        Expression::Unwrap(Box::new(Expression::Some(Box::new(
            Expression::BooleanLiteral("false".to_string())
        ))))
            .get_type(&scope)
    );

    let foo_identifier = Identifier::Scalar("foo".to_string());

    let mut scp = Scope::new();
    scp.enter();
    scp.declare(foo_identifier.clone(), Type::Integer);
    println!("foo lookup: {:#?}", scp.lookup(&foo_identifier));
    scp.leave();
    println!("foo lookup: {:#?}", scp.lookup(&foo_identifier));
    */
}
