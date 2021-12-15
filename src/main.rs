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



#[derive(Debug, Clone)]
enum Statement {
    Abort,
    Return(Expression),
    Assign(Identifier, Expression),
    TableAssign(Identifier, Expression, Expression), // TableAssign(T, 2+3, g^r) <== T[2+3] <-- g^r
    IfThenElse(Expression, Vec<Box<Statement>>, Vec<Box<Statement>>),
}


fn verify_package(p: &Package) -> Result<(),TypeCheckError> {
    let Package{ params, state, oracles } = p;
    let mut scope = Scope::new();
    scope.enter();
    for (name, ntipe) in params {
        scope.declare(Identifier::new_scalar(name), ntipe.clone());
    };
    for (name, ntipe) in state {
        scope.declare(Identifier::new_scalar(name), ntipe.clone());
    };
    
    for oracle in oracles {
        println!("checking oracle {:?}", oracle);
        verify_oracle(oracle, scope.clone())?;
    }
    Ok(())
}

fn verify_oracle(def: &OracleDef, mut scope: Scope) -> Result<(),TypeCheckError> {
    let OracleDef{
        sig: OracleSig{name: _name, args, tipe} ,
        code
    } = def;
    scope.enter();
    for (name, ntipe) in args {
        scope.declare(Identifier::new_scalar(name), ntipe.clone());
    };
    typecheck(&tipe, code, &mut scope)
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

    for stmt in block {
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
                let expr_type = expr.get_type(scope)?;
                if let Some(id_type) = scope.lookup(id) {
                    if id_type != expr_type {
                        return Err(TypeCheckError::TypeCheck("overwriting some value with incompatible type".to_string()))
                    }
                } else {
                    scope.declare(id.clone(), expr_type);
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

#[derive(Debug, Clone)]
struct FnSig {
    name: String,
    args: Vec<(String, Type)>,
    tipe: Type,
}

#[derive(Debug, Clone)]
struct OracleSig {
    name: String,
    args: Vec<(String, Type)>,
    tipe: Type,
}

#[derive(Debug, Clone)]
struct OracleDef {
    sig: OracleSig,
    code: Vec<Box<Statement>>,
}

#[derive(Debug, Clone)]
struct Package {
    params: Vec<(String, Type)>,
    state: Vec<(String, Type)>,
    oracles: Vec<OracleDef>,
}

#[derive(Debug, Clone)]
enum PackageInstance {
    Atom {
        params: HashMap<String, String>,
        pkg: Package,
    },
    Composition {
        pkgs: Vec<Box<PackageInstance>>,
        edges: Vec<(i32, i32, OracleSig)>, // (from, to, oraclename)
        exports: Vec<(i32, OracleSig)>,
    },
}

fn main() {
    let mut params = HashMap::new();
    params.insert("n".to_string(), "256".to_string());
    

    let prf_real_game = PackageInstance::Atom {
        params: params,
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
                ("f".to_string(), Type::new_fn(
                    vec![&Type::new_bits("n"), &Type::new_bits("*")],
                    &Type::new_bits("*"))),
            ],
            state: vec![("k".to_string(), Type::new_bits("n"))],
            oracles: vec![OracleDef {
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
                        block! {
                            Statement::Assign(Identifier::new_scalar("k"),
                                              Expression::Sample(Type::new_bits("n")),
                            )},
                        block! { /* // This is total nonsense, the block was empty before
                            Statement::TableAssign(Identifier::new_scalar("D"),
                                                   Expression::Add(Box::new(Expression::IntegerLiteral("2".to_string())),
                                                                   Box::new(Expression::IntegerLiteral("3".to_string()))),
                                                   Expression::StringLiteral("Hallo".to_string())),
                            Statement::Assign(Identifier::new_scalar("handle"),
                                              Expression::TableAccess(Box::new(Identifier::new_scalar("D")),
                                                                      Box::new(Expression::IntegerLiteral("5".to_string())))) */
                        },
                    ),
                    Statement::Return(fncall! { "f",
                                                 Identifier::new_scalar("k").to_expression(),
                                                 Identifier::new_scalar("msg").to_expression()
                    })
                },
            }],
        },
    };

    if let PackageInstance::Atom { params, pkg } = prf_real_game.clone() {
        println!("verify package: {:#?}", verify_package(&pkg));
    }
    
    println!("real game: {:#?}", prf_real_game);

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
}
