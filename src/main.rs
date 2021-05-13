use std::collections::HashMap;

#[derive(Debug, Clone)]
enum Type {
    Empty,
    Integer,
    String,
    Boolean,
    Bits(String), // Bits strings of length ...
    Scalar(String),
    AddiGroup(String), // name of the group
    MultGroup(String), // name of the group
    List(Box<Type>),
    Set(Box<Type>),
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

    fn new_set(t: &Type) -> Type {
        Type::Set(Box::new(t.clone()))
    }
}

#[derive(Debug, Clone)]
enum Expression {
    Bot,
    Sample(Type),
    StringLiteral(String),
    IntegerLiteral(String),
    BooleanLiteral(String),
    Identifier(String),
    Tuple(Vec<Box<Expression>>),
    List(Vec<Box<Expression>>),
    FnCall(String, Vec<Box<Expression>>),
    // or maybe at some point: FnCall(Box<Expression>, Vec<Box<Expression>>),
    OracleInvoc(String, Vec<Box<Expression>>),

    // Scalar Operations:
    Not(Box<Expression>), // 1-x (not really, in fact: true \mapsto false; false \mapsto true)
    Neg(Box<Expression>), //  -x
    Inv(Box<Expression>), // 1/x

    Sub(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Pow(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),
    Xor(Box<Expression>, Box<Expression>),

    Equals(Vec<Box<Expression>>),
    Add(Vec<Box<Expression>>),
    Mul(Vec<Box<Expression>>),
    And(Vec<Box<Expression>>),
    Or(Vec<Box<Expression>>),

    // Set/List Operations:
    Sum(Box<Expression>),
    Prod(Box<Expression>),
    Any(Box<Expression>), // set/list or
    All(Box<Expression>), // set/list and
    Union(Box<Expression>),
    Cut(Box<Expression>),
    SetDiff(Box<Expression>),

    Concat(Vec<Box<Expression>>),
}

impl Expression {
    fn new_identifier(name: &str) -> Expression {
        Expression::Identifier(name.to_string())
    }

    fn new_equals(exprs: Vec<&Expression>) -> Expression {
        Expression::Equals(
            exprs
                .into_iter()
                .map(|expr| Box::new(expr.clone()))
                .collect(),
        )
    }
}

macro_rules! tuple {
    ( $($e:expr),* ) => {
        {
            let mut res = Vec::new();
            $(
                res.push(Box::new($e.clone()));
            )*
            Expression::Tuple(res)
        }
    };
}

macro_rules! list {
    ( $($e:expr),* ) => {
        {
            let mut res = Vec::new();
            $(
                res.push(Box::new($e.clone()));
            )*
            Expression::Tuple(res)
        }
    };
}

macro_rules! oracleinvoc {
    ( $name:expr, $($e:expr),* ) => {
        {
            let mut res = Vec::new();
            $(
                res.push(Box::new($e.clone()));
            )*
            Expression::OracleInvoc($name.to_string(), res)
        }
    };
}

macro_rules! fncall {
    ( $name:expr, $($e:expr),* ) => {
        {
            let mut res = Vec::new();
            $(
                res.push(Box::new($e.clone()));
            )*
            Expression::FnCall($name.to_string(), res)
        }
    };
}

#[derive(Debug, Clone)]
enum Statement {
    Abort,
    Return(Expression),
    Assign(String, Expression),
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
                            &Expression::new_identifier("k"),
                            &Expression::Bot,
                        ]),
                        block! {
                            Statement::Assign("k".to_string(),
                                              Expression::Sample(Type::new_bits("n")),
                        )},
                        block! {},
                    ),
                    Statement::Return(fncall! { "f",
                        Expression::new_identifier("k"),
                        Expression::new_identifier("msg")
                    }),
                ],
            }],
        },
    };

    println!("{:#?}", prf_real_game);
}
