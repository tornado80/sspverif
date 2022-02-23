use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, OracleDef, OracleSig, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashMap;

use crate::block;
use crate::fncall;


pub fn mapping_game(params: &HashMap<String, String>) -> Composition {
    let key_pkg_top_map = PackageInstance {
        name: "key_pkg_top_map".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![("n".to_string(), Type::Integer)], /* key length*/
            state: vec![(
                "T".to_string(),
                Type::Table(Box::new(Type::Integer), Box::new(Type::new_bits("n"))),
            )], 
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![
                            ("h".to_string(), Type::Integer), /* handle h */
                            ("k".to_string(), Type::new_bits("n")),
                        ], /* key k  */
                        tipe: Type::Integer,
                    },
                    code: block! { /* if T[h] = bot, T[h]<--k, return h */
                                   /* if T[h] = bot, T[h]<--k, return h, else return h */
                        Statement::IfThenElse(
                                Expression::new_equals(vec![
                                    &Expression::TableAccess(Box::new(Identifier::new_scalar("T")),
                                                             Box::new(Identifier::new_scalar("h").to_expression())),
                                    &Expression::None(Type::new_bits("n")),
                                ]),
                         block! {
                                Statement::TableAssign(Identifier::new_scalar("T"),
                                                       Identifier::new_scalar("h").to_expression(),
                                                       Identifier::new_scalar("k").to_expression()),
                                Statement::Return(Some(Identifier::new_scalar("h").to_expression()))
                                 },
/*                         block! {Statement::Abort},*/
                        block! {
                                Statement::Return(Some(Identifier::new_scalar("h").to_expression()))
                               }
                            )
                    },
                },
                OracleDef {
                    sig: OracleSig {
                        name: "Get".to_string(),
                        args: vec![("h".to_string(), Type::Integer)],
                        tipe: Type::new_bits("n"),
                    },
                    code: block! {
                    Statement::IfThenElse(
                        Expression::new_equals(vec![
                                &Expression::TableAccess(Box::new(Identifier::new_scalar("T")),
                                                         Box::new(Identifier::new_scalar("h").to_expression())),
                                &Expression::None(Type::new_bits("n")),
                        ]),
                        block! {Statement::Abort},
                        block! {Statement::Return(
                            Some(Expression::TableAccess(Box::new(Identifier::new_scalar("T")),
                                                               Box::new(Identifier::new_scalar("h").to_expression()))))
                                }
                                        )
                    },
                },
            ],
        },
    };

    let mod_prf = PackageInstance {
        name: "prf".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
                (
                    "f".to_string(),
                    Type::new_fn(
                        vec![Type::new_bits("n"), Type::new_bits("*")],
                        Type::new_bits("n"),
                    ),
                ),
            ],
            state: vec![],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: "Eval".to_string(),
                    args: vec![
                        ("h".to_string(), Type::Integer),
                        ("msg".to_string(), Type::new_bits("*")),
                    ],
                    tipe: Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                },
                code: block! {
                    Statement::Assign(Identifier::new_scalar("k"), Expression::OracleInvoc("Get".to_string(), vec![Identifier::new_scalar("h").to_expression()])),
                    Statement::Assign(Identifier::new_scalar("y"),fncall! { "f",
                                                      Identifier::new_scalar("k").to_expression(),
                                                      Identifier::new_scalar("msg").to_expression()}),
                    Statement::Assign(Identifier::new_scalar("z"), Expression::OracleInvoc(
                        "Set".to_string(),
                        vec![
                            Expression::Tuple(vec![
                                Identifier::new_scalar("h").to_expression(),
                                Identifier::new_scalar("msg").to_expression()
                            ]),
                            Identifier::new_scalar("y").to_expression()
                        ]
                    )),
                    Statement::Return(Some(
                        Expression::Tuple(vec![
                            Identifier::new_scalar("h").to_expression(),
                            Identifier::new_scalar("msg").to_expression()
                        ])
                    ))
                },
            }],
        },
    };

    let key_pkg_bottom = PackageInstance {
        name: "key_pkg_bottom".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![("n".to_string(), Type::Integer)], /* key length*/
            state: vec![(
                "T".to_string(),
                Type::Table(
                    Box::new(Type::Tuple(vec![Type::Integer, Type::new_bits("*")])),
                    Box::new(Type::new_bits("n")),
                ),
            )],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![
                            (
                                "h".to_string(),
                                Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                            ),
                            ("k".to_string(), Type::new_bits("n")),
                        ], /* handle (int,msg) */
                        tipe: Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                    },
                    code: block! { /* assert T[h] = bot, T[h]<--k, return h  */
                        Statement::IfThenElse(
                               Expression::new_equals(vec![
                                   &Expression::TableAccess(Box::new(Identifier::new_scalar("T")),
                                                            Box::new(Identifier::new_scalar("h").to_expression())),
                                   &Expression::None(Type::new_bits("n")),
                               ]),
                            block! {
                                Statement::TableAssign(Identifier::new_scalar("T"),
                                Identifier::new_scalar("h").to_expression(),
                                Identifier::new_scalar("k").to_expression()),
                                Statement::Return(Some(Identifier::new_scalar("h").to_expression()))
                                   },
                            block! {Statement::Return(Some(Identifier::new_scalar("h").to_expression()))}
                         /* block! {Statement::Abort} */
                        )
                    },
                },
                OracleDef {
                    sig: OracleSig {
                        name: "Get".to_string(),
                        args: vec![(
                            "h".to_string(),
                            Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                        )],
                        tipe: Type::new_bits("n"),
                    },
                    code: block! { /*assert T[h]!=bot, return T[h] */
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                    &Expression::TableAccess(Box::new(Identifier::new_scalar("T")), 
                                                             Box::new(Identifier::new_scalar("h").to_expression())), 
                                    &Expression::None(Type::new_bits("n")),
                            ]),
                            block! {Statement::Abort},
                            block! {Statement::Return(Some(Expression::TableAccess(Box::new(Identifier::new_scalar("T")),
                            Box::new(Identifier::new_scalar("h").to_expression()))))}
                        )
                    },
                },
            ],
        },
    };

    let map_pkg = PackageInstance {
        name: "map_pkg".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![("n".to_string(), Type::Integer)], /* key length*/
            state: vec![(
                "Input_Map".to_string(),
                Type::Table(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                )),
                (
                "Output_Map".to_string(),
                Type::Table(
                    Box::new(Type::Tuple(vec![Type::Integer, Type::new_bits("*")])),
                    Box::new(Type::Tuple(vec![Type::Integer, Type::new_bits("*")])),
                ))],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![
                            (
                                "h".to_string(),
                                Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                            ),
                            ("k".to_string(), Type::new_bits("n")),
                        ], /* handle (int,msg) */
                        tipe: Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                    },
                    code: block! { /* if Input_Map[h] = bot, Input_Map[h] <-- Set(h,k), return h. Else return h.  */
                    Statement::IfThenElse(
                        Expression::new_equals(vec![
                            &Expression::TableAccess(Box::new(Identifier::new_scalar("Input_Map")),
                                                     Box::new(Identifier::new_scalar("h").to_expression())),
                            &Expression::None(Type::Integer),
                        ]),
                        block! {
                    Statement::Assign(Identifier::new_scalar("hh"), Expression::OracleInvoc(
                        "Set".to_string(),
                        vec![
                                Identifier::new_scalar("h").to_expression(),
                                Identifier::new_scalar("k").to_expression()
                            ])),
                            Statement::TableAssign(Identifier::new_scalar("Input_Map"),
                            Identifier::new_scalar("h").to_expression(),
                            Identifier::new_scalar("hh").to_expression()),
                    Statement::Return(Some(Identifier::new_scalar("h").to_expression()))
                            },
                        block! {Statement::Return(Some(Identifier::new_scalar("h").to_expression()))}                         
                    /* block! {Statement::Abort} */
                    )
                    },
                    },
                    OracleDef {
                        sig: OracleSig {
                            name: "Eval".to_string(),
                            args: vec![
                                ("h".to_string(), Type::Integer),
                                ("msg".to_string(), Type::new_bits("*")),
                            ],
                            tipe: Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                        },
                        code: block! { /* if Input_Map[h] = bot, Output_Map[h,msg] <-- Eval(h,msg), return h. Else return h.  */
                            Statement::IfThenElse(
                                Expression::new_equals(vec![
                                    &Expression::TableAccess(Box::new(Identifier::new_scalar("Input_Map")),
                                                             Box::new(Identifier::new_scalar("h").to_expression())),
                                    &Expression::None(Type::Integer),
                                ]),
                                block! {Statement::Return(Some(Identifier::new_scalar("h").to_expression()))}                         ,
                                /* block! {Statement::Abort} */    
                                block! {
                                    Statement::Assign(Identifier::new_scalar("hh"), Expression::TableAccess(Box::new(Identifier::new_scalar("Input_Map")),
                                    Box::new(Identifier::new_scalar("h").to_expression()))),
                                    Statement::Assign(Identifier::new_scalar("hhh"), Expression::OracleInvoc(
                                        "Eval".to_string(),
                                vec![
                                        Identifier::new_scalar("hh").to_expression(),
                                        Identifier::new_scalar("msg").to_expression()
                                    ])),
                                    Statement::TableAssign(Identifier::new_scalar("Output_Map"),
                                    Identifier::new_scalar("hh").to_expression(),
                                    Identifier::new_scalar("hhh").to_expression()),
                            Statement::Return(Some(Expression::Tuple(vec![
                                Identifier::new_scalar("h").to_expression(),
                                Identifier::new_scalar("msg").to_expression()
                            ])))
                            }
                            )
                        },
                    },
                OracleDef {
                    sig: OracleSig {
                        name: "Get".to_string(),
                        args: vec![(
                            "h".to_string(),
                            Type::Tuple(vec![Type::Integer, Type::new_bits("*")]),
                        )],
                        tipe: Type::new_bits("n"),
                    },
                    /*
                    if Output-Map[h] = bot
                    	abort
                    else hh <-- Output-Map[h]
                    	k <-- Get(hh)
                    	return k
                    */
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                    &Expression::TableAccess(Box::new(Identifier::new_scalar("Output-Map")),
                                                             Box::new(Identifier::new_scalar("h").to_expression())), 
                                    &Expression::None(Type::Tuple(vec![Type::Integer, Type::new_bits("*")])),
                            ]),
                            block! {Statement::Abort},
                            block! {
                                Statement::Assign(Identifier::new_scalar("hh"),
                                Expression::TableAccess(Box::new(Identifier::new_scalar("Output-Map")),
                                                        Box::new(Identifier::new_scalar("h").to_expression()))),
                                Statement::Assign(Identifier::new_scalar("k"), Expression::OracleInvoc("Get".to_string(), vec![Identifier::new_scalar("hh").to_expression()])),
                                Statement::Return(Some(Identifier::new_scalar("k").to_expression()))
                            }
                        )
                    },
                }
            ],
        },
    };

    Composition {
        pkgs: vec![key_pkg_top_map.clone(), mod_prf.clone(), key_pkg_bottom.clone(), map_pkg.clone()],
        edges: vec![
            (1, 0, key_pkg_top_map.pkg.clone().oracles[1].sig.clone()),
            (1, 2, key_pkg_bottom.pkg.clone().oracles[0].sig.clone()),
            (3, 0, key_pkg_top_map.pkg.clone().oracles[0].sig.clone()),
            (3, 1, mod_prf.pkg.clone().oracles[0].sig.clone()),
            (3, 2, key_pkg_bottom.pkg.clone().oracles[1].sig.clone()),
            ],
        exports: vec![
            (0, map_pkg.pkg.clone().oracles[0].sig.clone()),
            (1, map_pkg.pkg.clone().oracles[1].sig.clone()),
            (2, map_pkg.pkg.clone().oracles[2].sig.clone()),
        ],
        name: "no_mapping_game".to_string(),
    }
}