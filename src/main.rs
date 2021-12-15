use std::collections::HashMap;
//use std::fmt;

mod types;
mod scope;
mod identifier;
mod expressions;

use types::{Type, TypeError};
use scope::{Scope, ScopeError};
use expressions::Expression;
use identifier::Identifier;



#[derive(Debug, Clone, PartialEq, Eq)]
enum Statement {
    Abort,
    Return(Expression),
    Assign(Identifier, Expression),
    TableAssign(Identifier, Expression, Expression), // TableAssign(T, 2+3, g^r) <== T[2+3] <-- g^r
    IfThenElse(Expression, Vec<Box<Statement>>, Vec<Box<Statement>>),
}


fn verify_package(p: &Package, scope: &mut Scope) -> Result<(),TypeCheckError> {
    let Package{ params, state, oracles } = p;
    //let mut scope = Scope::new();
    scope.enter();
    for (name, ntipe) in params {
        scope.declare(Identifier::new_scalar(name), ntipe.clone());
    };
    for (name, ntipe) in state {
        scope.declare(Identifier::new_scalar(name), ntipe.clone());
    };
    
    for oracle in oracles {
        println!("checking oracle {:?}", oracle);
        verify_oracle(oracle, scope)?;
    }
    Ok(())
}

fn verify_oracle(def: &OracleDef, scope: &mut Scope) -> Result<(),TypeCheckError> {
    let OracleDef{
        sig: OracleSig{name: _name, args, tipe} ,
        code
    } = def;
    scope.enter();
    for (name, ntipe) in args {
        scope.declare(Identifier::new_scalar(name), ntipe.clone());
    };
    typecheck(&tipe, code, scope)
}

#[derive(Debug)]
enum TypeCheckError {
    Scope(ScopeError),
    Type(TypeError),
    TypeCheck(String)
}

impl From<ScopeError> for TypeCheckError {
    fn from(error: ScopeError) -> Self {
        TypeCheckError::Scope(error)
    }
}

impl From<TypeError> for TypeCheckError {
    fn from(error: TypeError) -> Self {
        TypeCheckError::Type(error)
    }
}


fn typecheck(ret_type: &Type, block: &Vec<Box<Statement>>, scope: &mut Scope) -> Result<(),TypeCheckError> {
    scope.enter();

    for (i, stmt) in block.into_iter().enumerate() {
        println!("looking at {:} - {:?}", i, stmt);
        match &**stmt {
            Statement::Abort => return Ok(()),
            Statement::Return(expr) => {
                let expr_type = expr.get_type(scope)?;
                if expr_type != *ret_type {
                    return Err(TypeCheckError::TypeCheck(format!("return type does not match: {:?} != {:?}", ret_type, expr_type).to_string()))
                } else {
                    return Ok(())
                }
            },
            Statement::Assign(id, expr) => {
                println!("scope: {:?}", scope);
                
                let expr_type = expr.get_type(scope)?;
                if let Some(id_type) = scope.lookup(id) {
                    if id_type != expr_type {
                        return Err(TypeCheckError::TypeCheck("overwriting some value with incompatible type".to_string()))
                    }
                } else {
                    scope.declare(id.clone(), expr_type)?;
                }
            },
            Statement::TableAssign(id, idx, expr) => {
                let expr_type = expr.get_type(scope)?;
                let idx_type = idx.get_type(scope)?;
                if let Some(id_type) = scope.lookup(id) {
                    if let Type::Table(k, v) = id_type {
                        if *k != idx_type || *v != expr_type {
                            return Err(TypeCheckError::TypeCheck("type of the table does not match".to_string()))
                        }
                    } else {
                        return Err(TypeCheckError::TypeCheck("table access on non-table".to_string()))
                    }
                } else {
                    return Err(TypeCheckError::TypeCheck("assigning to table but table does not exist (here)".to_string()))
                }
            },
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                if expr.get_type(scope)? != Type::Boolean {
                    return Err(TypeCheckError::TypeCheck("condition must be boolean".to_string()))
                }
                typecheck(ret_type, ifcode, scope)?;
                typecheck(ret_type, elsecode, scope)?;
            }
        }
    }

    scope.leave()?;
    Ok(())
}


macro_rules! block {
    ( $( $s:expr ),* ) => {
        {
            let mut res = Vec::new();
            $(
                res.push(Box::new($s.clone()));
            )*
                res
        }
    }
}

/*
 * Next Steps:
 * - type check
 * - normalize/canonicalize nested composition
 * - usable constructors
 * - extract SMT-LIB
 * - pretty-print: both text-only and cryptocode
 */

#[derive(Debug, Clone, PartialEq, Eq)]
struct FnSig {
    name: String,
    args: Vec<(String, Type)>,
    tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OracleSig {
    name: String,
    args: Vec<(String, Type)>,
    tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OracleDef {
    sig: OracleSig,
    code: Vec<Box<Statement>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Package {
    params: Vec<(String, Type)>,
    state: Vec<(String, Type)>,
    oracles: Vec<OracleDef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PackageInstance {
    Atom {
        params: HashMap<String, String>,
        pkg: Package,
    },
    Composition {
        pkgs: Vec<Box<PackageInstance>>,
        edges: Vec<(usize, usize, OracleSig)>, // (from, to, oraclename)
        exports: Vec<(usize, OracleSig)>,
    },
}

impl PackageInstance {
    fn get_pkg(&self) -> Package {
        match self {
            PackageInstance::Atom{pkg, ..} => pkg.clone(),
            _ => panic!(),
        }
    }

    fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        match self {
            PackageInstance::Atom{pkg, ..} => {
                pkg.oracles.clone()
                    .into_iter()
                    .map(|d| d.sig)
                    .collect()
            },
            PackageInstance::Composition{pkgs, exports, ..} => {
                exports.into_iter()
                    .map(|(_, sig)| sig.clone())
                    .collect()
            }
        }
    }

    fn verify(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        match self {
            PackageInstance::Atom{pkg, .. } => {
                // TODO also check params
                verify_package(pkg, scope)
            },
            PackageInstance::Composition{pkgs, edges, exports} => {
                
                // 1. check signature exists in edge destination
                for (_, to, sig_) in edges {
                    let mut found = false;
                    for sig in pkgs[to.clone()].get_oracle_sigs() {
                        if sig == sig_.clone() {
                            found = true
                        }
                    }
                    if !found {
                        return Err(TypeCheckError::TypeCheck(format!("couldn't find signature for {:?} in package {:?} with id {:}", sig_, pkgs[to.clone()], to)))
                    }
                }

                // 2. check exports exists
                for (id, sig) in exports {
                    if !pkgs[id.clone()].get_oracle_sigs().contains(sig) {
                        return Err(TypeCheckError::TypeCheck(format!("signature {:?} is not in package {:?} with index {:}", sig, pkgs[id.clone()].clone(), id)))
                    }
                }

                // 3. check all package instances
                for (id, pkg) in pkgs.clone().into_iter().enumerate() {
                    scope.enter();
                    for (from, _, sig) in edges {
                        if from.clone() == id {
                            println!("adding oracle {:} to scope", sig.name);
                            scope.declare(
                                Identifier::new_scalar(sig.name.as_str()),
                                Type::Oracle(
                                    sig.args.clone()
                                        .into_iter()
                                        .map(|(_, tipe)| Box::new(tipe)).collect(),
                                    Box::new(sig.tipe.clone()))
                            )?;
                        }
                    }
                    let result = pkg.verify(scope)?;
                    scope.leave()?;

                    result
                }


                Ok(())
            }
        }
    }
}

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
                        args: vec![("k".to_string(), Type::new_bits("n"))],
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
                        args: vec![("k".to_string(), Type::new_bits("n"))],
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
    if let PackageInstance::Atom { params, pkg } = prf_real_game.clone() {
        println!("verify mono prf package: {:#?}", verify_package(&pkg, &mut scope));
    }

    //println!("real game: {:#?}", prf_real_game);

    println!("modular game: {:#?}", mod_prf_game);

    let mut scope: Scope = Scope::new();
    println!("modular game verify: {:#?}", mod_prf_game.verify(&mut scope))

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
