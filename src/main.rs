use std::collections::HashMap;

#[derive(Debug, Clone)]
enum Type {
    Empty,
    Bits(String), // Bits strings of length ...
    Scalar(String),
    List(Box<Type>),
    Tuple(Vec<Box<Type>>),
    Table((Box<Type>, Box<Type>)),
}

impl Type {
	fn new_bits(length: &str) -> Type {
		Type::Bits(length.to_string())
	}
	
	fn new_scalar(name: &str) -> Type {
		Type::Scalar(name.to_string())
	}
	
	fn new_list(t: &Type) -> Type {
		Type::List(Box::new(t.clone()))
	}
}

#[derive(Debug, Clone)]
enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Equals,
}

#[derive(Debug, Clone)]
enum Expression {
    Bot,
    Sample(Type),
    Literal(String),
    Identifier(String),
    Tuple(Vec<Box<Expression>>),
    Arith(ArithOp, Vec<Box<Expression>>),
    FnCall(String, Vec<Box<Expression>>),
    // or maybe at some point: FnCall(Box<Expression>, Vec<Box<Expression>>),
    OracleInvoc(String, Vec<Box<Expression>>),
}

impl Expression {
	fn new_identifier(name: &str) -> Expression {
		Expression::Identifier(name.to_string())
	}
	
	
}

#[derive(Debug, Clone)]
enum Statement {
    Abort,
    Return(Expression),
    Assign(String, Expression),
    IfThenElse(Expression, Vec<Box<Statement>>, Vec<Box<Statement>>),
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
                        Expression::Arith(
                            ArithOp::Equals,
                            vec![
                                Box::new(Expression::new_identifier("k")),
                                Box::new(Expression::Bot),
                            ],
                        ),
                        vec![Box::new(Statement::Assign(
                            "k".to_string(),
                            Expression::Sample(Type::new_bits("n")),
                        ))],
                        vec![],
                    ),
                    Statement::Return(Expression::FnCall(
                        "f".to_string(),
                        vec![
                            Box::new(Expression::new_identifier("k")),
                            Box::new(Expression::new_identifier("msg")),
                        ],
                    )),
                ],
            }],
        },
    };

    println!("{:#?}", prf_real_game);
}
