use std::collections::HashMap;
//use std::fmt;

mod types;
mod scope;
mod identifier;
mod expressions;

use types::Type;
use scope::Scope;
use expressions::Expression;
use identifier::Identifier;




#[derive(Debug, Clone)]
enum Statement {
    Abort,
    Return(Expression),
    Assign(Identifier, Expression),
    IfThenElse(Expression, Vec<Box<Statement>>, Vec<Box<Statement>>),
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
    code: Vec<Statement>,
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
        edges: Vec<(i32, i32, String)>, // (from, to, oraclename)
        exports: Vec<(i32, String)>,
    },
}

fn main() {
    let mut params = HashMap::new();
    params.insert("n".to_string(), "256".to_string());

    let prf_real_game = PackageInstance::Atom {
        params: params,
        pkg: Package {
            params: vec![("n".to_string(), Type::new_scalar("int"))],
            state: vec![("k".to_string(), Type::new_bits("n"))],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: "Eval".to_string(),
                    args: vec![("msg".to_string(), Type::new_bits("*"))],
                    tipe: Type::new_bits("*"),
                },
                code: vec![
                    Statement::IfThenElse(
                        Expression::new_equals(vec![
                            &(Identifier::new_scalar("k").to_expression()),
                            &Expression::Bot,
                        ]),
                        block! {
                            Statement::Assign(Identifier::new_scalar("k"),
                                              Expression::Sample(Type::new_bits("n")),
                        )},
                        block! {},
                    ),
                    Statement::Return(fncall! { "f",
                        Identifier::new_scalar("k").to_expression(),
                         Identifier::new_scalar("msg").to_expression()
                    }),
                ],
            }],
        },
    };

    println!("{:#?}", prf_real_game);

    let scope: Scope = Scope::new();
    println!(
        "{:#?}",
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
        "{:#?}",
        Expression::Unwrap(Box::new(Expression::Some(Box::new(
            Expression::BooleanLiteral("false".to_string())
        ))))
        .get_type(&scope)
    );

    let foo_identifier = Identifier::Scalar("foo".to_string());

    let mut scp = Scope::new();
    scp.enter();
    scp.declare(foo_identifier.clone(), Type::Integer);
    println!("{:#?}", scp.lookup(&foo_identifier));
    scp.leave();
    println!("{:#?}", scp.lookup(&foo_identifier));
}
