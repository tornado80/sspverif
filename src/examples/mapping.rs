
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



fn main() {
    let mut params = HashMap::new();
    params.insert("n".to_string(), "256".to_string());

    let key_pkg_top = PackageInstance {
        name: "key_pkg_top".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![("n".to_string(), Type::Integer)],   /* key length*/
            state: vec![("T".to_string(), Type::Table(Box<Integer>,Box<new_bits("n")>))]
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("h".to_string(), Type::Integer),  /* handle h */
                                   ("k".to_string(), Type::new_bits("n"))], /* key k  */
                        tipe: Type::Integer,
                    },
                    code: block! { /* if T[h] != bot, return bot */
                        Statement::IfThenElse(
                            Expression:: Not( /* Box ? */
                                new_equals(vec![
                                    &Expression::TableAccess(Identifier::T, /* Box ? */
                                                             Expression::h), /* Box ? */
                                    &Expression::Bot,
                                ])),
                            block! {
                                Statement::TableAssign(Identifier::T, 
                                                      Expression::h, 
                                                      Expression::k),
                                   },
                            block! {}      
                                )},
                            block! { 
                                Return(Expression:h)
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
                                    &Expression::TableAccess(Identifier::T, /* Box ? */
                                                             Expression::h), /* Box ? */
                                    &Expression::Bot,
                            ]),
                            block! {Statement::Abort},
                            block! {}                                        
                        ),
                        block! {Return(Expression::TableAccess(Identifier::T, /* Box ? */
                                                               Expression::h)}, /* Box ? */
                                 }
                    },
                },
            ],
        },

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
                        Type::new_bits("*"),
                    ),
                ),
            ],
            state: vec![],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: "Eval".to_string(),
                    args: vec![("h".to_string(), Type::Integer),("msg".to_string(), Type::new_bits("*"))],
                    tipe: Type::Tuple(vec![Integer,String]),
                },
                code: block! {
                    Statement::Assign(Identifier::new_scalar("k"), Expression::OracleInvoc("Get".to_string(), vec![Expression::h])), 
                    Statement::Assign(Identifier::new_scalar("y"),Some(fncall! { "f",
                                                      Identifier::new_scalar("k").to_expression(),
                                                      Identifier::new_scalar("msg").to_expression()}))
                    Statement::Assign(Identifier::new_scalar("z"), Expression::OracleInvoc("Set".to_string(), vec![Tuple::vec![Expression::h,Expression::k],Expression::y])), 
                            }
                    block! {Return(Expression::Tuple::vec![Expression::h,Expression::msg])}
                    }))
                },
            },

    let key_pkg_bottom = PackageInstance {
        name: "key_pkg_bottom".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![("n".to_string(), Type::Integer)],   /* key length*/
            state: vec![("T".to_string(), Type::Table(Type::Tuple(vec![Integer,new_bits("*")]),Box<new_bits("n")>))]
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("h".to_string(), Type::Tuple(vec![Integer,new_bits("*")]))],  /* handle (int,msg) */
                        tipe: Type::new_bits("*"),
                    },
                    code: block! { /* if T[h] != bot, return bot */
                        Statement::IfThenElse(
                            Expression:: Not( /* Box ? */
                                new_equals(vec![
                                    &Expression::TableAccess(Identifier::T, /* Box ? */
                                                             Expression::h), /* Box ? */
                                    &Expression::Bot,
                                ])),
                            block! {
                                Statement::TableAssign(Identifier::T, 
                                                      Expression::h, 
                                                      Expression::k),
                                   },
                            block! {}      
                                )},
                            block! { 
                                Return(Expression:h)
                                 },
                            },
                OracleDef {
                    sig: OracleSig {
                        name: "Get".to_string(),
                        args: vec![("h".to_string(), Type::Tuple(vec![Integer,new_bits("*")]))],
                        tipe: Type::new_bits("n"),
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                    &Expression::TableAccess(Identifier::T, /* Box ? */
                                                             Expression::h), /* Box ? */
                                    &Expression::Bot,
                            ]),
                            block! {Statement::Abort},
                            block! {}                                        
                        ),
                        block! {Return(Expression::TableAccess(Identifier::T, /* Box ? */
                                                               Expression::h)}, /* Box ? */
                                 }
                    },
                },
            ],
        },

    let plain_prf_game = Composition {
        pkgs: vec![key_pkg_top.clone(), , mod_prf.clone(), key_pkg_bottom.clone()],
        edges: vec![(1, 0, key_pkg_top.pkg.clone().oracles[1].sig.clone()),
                    (1, 2, key_pkg_bottom.pkg.clone().oracles[0].sig.clone())
                   ],
        exports: vec![
            (0, key_pkg_top.pkg.clone().oracles[0].sig.clone()),
            (1, mod_prf_real_pkg.pkg.clone().oracles[0].sig.clone()),
            (2, mod_prf_real_pkg.pkg.clone().oracles[1].sig.clone()),
            ],
        name: "real".to_string(),
    };
};