/*
Questions I:
Code-specific:
- Which params are cloned here? ok
- Paramters are currently ignored
- Option 1 and option 2 for integer types--> should be Integer, not new_scalar("int")
- Initialization of counter --> initialization is currently missing.
    - do we have constants such as 0 or 1?
    - What does "if ctr = bot then ..." do? Doesn't that mean that ctr was initialized to bot ?
- Handles: --> arbitrary tuples currently difficult in typing
    - What is a good type for a handle?
    - Can we use handle constructors? Can I use integers as handle in top key package and pairs of (int,bitstring) on lower key package?
    - handle constructor
    - int
    - (int,string) Type::Tuple(vec![Type::Integer, Type::String])
- Tables: --> check statement.rs file
    - add a table to the state
    - assign to a table
    - read from a table

Bigger SSP stuff:
- How do I specify multiple instances of the same package? let myname = Package {...}
- How do I disambiguate their oracle names?

Flow stuff:
- OracleDef typechecken
- Package typechecken
- composition typechecken
- How do I integrate this file into the project?
- How do I type-check this code? Which options do I have, which subparts can I check?
*/

/*
Questions II:
- empty code block okay?  Yes: block! {},
- oracle call without assignment? No.
- Can I re-use state variables in other packages
- When do I need to write the boxes?
- Return(Option<Expression>) - what is Option?

*/

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, OracleDef, OracleSig, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashMap;

use crate::block;
use crate::fncall;

pub fn no_mapping_game(params: &HashMap<String, String>) -> Composition {
    let key_pkg_top = PackageInstance {
        name: "key_pkg_top".to_string(),
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
                    code: block! { /* assert T[h] = bot, T[h]<--k, return h */
                                   /* if T[h] = bot, T[h]<--k, return h, else do nothing */
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
                                 block! {
                                    Statement::Return(Some(Identifier::new_scalar("h").to_expression()))
                                     },
                        /*  block! {Statement::Abort},*/
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
                            Some(Expression::Unwrap(Box::new(
                                Expression::TableAccess(Box::new(Identifier::new_scalar("T")),
                                                               Box::new(Identifier::new_scalar("h").to_expression()))))))
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
                    /*                            block! {Statement::Abort}*/
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
                            block! {Statement::Return(Some(Expression::Unwrap(Box::new( Expression::TableAccess(Box::new(Identifier::new_scalar("T")),
                            Box::new(Identifier::new_scalar("h").to_expression()))))))}
                        )
                    },
                },
            ],
        },
    };

    Composition {
        pkgs: vec![key_pkg_top.clone(), mod_prf.clone(), key_pkg_bottom.clone()],
        edges: vec![
            (1, 0, key_pkg_top.pkg.clone().oracles[1].sig.clone()),
            (1, 2, key_pkg_bottom.pkg.clone().oracles[0].sig.clone()),
        ],
        exports: vec![
            (0, key_pkg_top.pkg.clone().oracles[0].sig.clone()),
            (1, mod_prf.pkg.clone().oracles[0].sig.clone()),
            (2, key_pkg_bottom.pkg.clone().oracles[1].sig.clone()),
        ],
        name: "no_mapping_game".to_string(),
    }
}
