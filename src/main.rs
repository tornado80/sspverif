use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Type {
    Empty,
    Integer,
    String,
    Boolean,
    Bits(String), // Bits strings of length ...
    Scalar(String),
    AddiGroupEl(String), // name of the group
    MultGroupEl(String), // name of the group
    List(Box<Type>),
    Set(Box<Type>),
    Tuple(Vec<Box<Type>>),
    Table((Box<Type>, Box<Type>)),
    Maybe(Box<Type>),
}

struct ScopeError;

// TODO
#[derive(Debug, Clone)]
struct Scope(Vec<HashMap<Identifier, Type>>);

impl Scope {
    fn new() -> Scope {
        Scope(vec![])
    }

    fn enter(&mut self) {
        self.0.push(HashMap::new())
    }

    fn leave(&mut self) -> Result<(), ScopeError> {
        if self.0.len() > 0 {
            self.0.pop();
            Ok(())
        } else {
            Err(ScopeError)
        }
    }

    fn declare(&mut self, id: Identifier, t: Type) -> Result<(), ScopeError> {
        if let Some(mut last) = self.0.last_mut() {
            last.insert(id, t);
            Ok(())
        } else {
            Err(ScopeError)
        }
    }

    fn lookup(&self, id: Identifier) -> Option<Type> {
        for table in self.0.clone().into_iter().rev() {
            if let Some(t) = table.get(&id) {
                return Some(t.clone());
            }
        }

        None
    }
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Identifier {
    Scalar(String),
    Bracket(Box<Identifier>, Expression),
}

impl Identifier {
    fn new_scalar(name: &str) -> Identifier {
        Identifier::Scalar(name.to_string())
    }

    // TODO implement correct converter trait to identifier expression
    fn to_expression(&self) -> Expression {
        Expression::Identifier(Box::new(self.clone()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Expression {
    Bot,
    Sample(Type),
    StringLiteral(String),
    IntegerLiteral(String),
    BooleanLiteral(String),
    Identifier(Box<Identifier>),
    Tuple(Vec<Box<Expression>>),
    List(Vec<Box<Expression>>),
    FnCall(String, Vec<Box<Expression>>),
    // or maybe at some point: FnCall(Box<Expression>, Vec<Box<Expression>>),
    OracleInvoc(String, Vec<Box<Expression>>),

    None(Type),
    Some(Box<Expression>),
    Unwrap(Box<Expression>),

    // Scalar Operations:
    Not(Box<Expression>), // 1-x (not really, in fact: true \mapsto false; false \mapsto true)
    Neg(Box<Expression>), //  -x
    Inv(Box<Expression>), // 1/x

    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
    Mul(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Pow(Box<Expression>, Box<Expression>),
    Mod(Box<Expression>, Box<Expression>),

    Equals(Vec<Box<Expression>>),
    And(Vec<Box<Expression>>),
    Or(Vec<Box<Expression>>),
    Xor(Vec<Box<Expression>>),

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

#[derive(Debug, Clone)]
struct TypeError;

type TypeResult = std::result::Result<Type, TypeError>;

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid type")
    }
}

impl Expression {
    /*
    fn new_identifier(name: &str) -> Expression {
        Expression::Identifier(name.to_string())
    }
    */

    fn new_equals(exprs: Vec<&Expression>) -> Expression {
        Expression::Equals(
            exprs
                .into_iter()
                .map(|expr| Box::new(expr.clone()))
                .collect(),
        )
    }

    fn get_type(&self, scope: &Scope) -> TypeResult {
        match self {
            Expression::Sample(t) => Ok(t.clone()),
            Expression::StringLiteral(_) => Ok(Type::String),
            Expression::IntegerLiteral(_) => Ok(Type::Integer),
            Expression::BooleanLiteral(_) => Ok(Type::Boolean),
            Expression::Tuple(elems) => {
                let mut types = vec![];

                for elem in elems {
                    types.push(Box::new(elem.get_type(scope)?));
                }

                Ok(Type::Tuple(types))
            }
            Expression::Some(v) => Ok(Type::Maybe(Box::new(v.get_type(scope)?))),
            Expression::None(t) => Ok(Type::Maybe(Box::new(t.clone()))),
            Expression::Unwrap(v) => {
                if let Expression::Some(inner) = &**v {
                    Ok(inner.get_type(scope)?)
                } else {
                    Err(TypeError)
                }
            }
            Expression::Neg(v) => {
                let t = v.get_type(scope)?;
                if t == Type::Integer && matches!(t, Type::AddiGroupEl(_)) {
                    Ok(t)
                } else {
                    Err(TypeError)
                }
            }
            Expression::Not(v) => {
                let t = v.get_type(scope)?;
                if t != Type::Boolean {
                    return Err(TypeError);
                }

                Ok(t)
            }
            Expression::Inv(v) => {
                let t = v.get_type(scope)?;
                if matches!(t, Type::MultGroupEl(_)) {
                    return Ok(t);
                }

                Err(TypeError)
            }
            Expression::Add(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                let same_type = t_left == t_right;
                let left_is_int = t_left.clone() == Type::Integer;
                let left_is_age = matches!(t_left, Type::AddiGroupEl(_));

                if same_type && (left_is_int || left_is_age) {
                    Ok(t_left)
                } else {
                    Err(TypeError)
                }
            }
            Expression::Mul(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                let same_type = t_left == t_right;
                let left_is_int = t_left.clone() == Type::Integer;
                let left_is_mge = matches!(t_left, Type::MultGroupEl(_));
                let right_is_age = matches!(t_right, Type::AddiGroupEl(_));

                if same_type {
                    if left_is_int || left_is_mge {
                        Ok(t_left)
                    } else {
                        Err(TypeError)
                    }
                } else {
                    if left_is_int && right_is_age {
                        Ok(t_right)
                    } else {
                        Err(TypeError)
                    }
                }
            }
            Expression::Sub(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                if (t_left.clone() == Type::Integer || matches!(t_left, Type::AddiGroupEl(_)))
                    && t_left == t_right
                {
                    return Ok(t_left);
                }

                Err(TypeError)
            }
            Expression::Div(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                if t_left != Type::Integer || t_left != t_right {
                    return Err(TypeError);
                }

                Ok(t_left)
            }
            Expression::Pow(base, exp) => {
                let t_base = base.get_type(scope)?;
                let t_exp = exp.get_type(scope)?;

                let base_is_int = t_base.clone() == Type::Integer;
                let exp_is_int = t_exp.clone() == Type::Integer;
                let base_is_mge = matches!(t_base, Type::MultGroupEl(_));

                if exp_is_int {
                    if base_is_int || base_is_mge {
                        Ok(t_base)
                    } else {
                        Err(TypeError)
                    }
                } else {
                    Err(TypeError)
                }
            }
            Expression::Mod(num, modulus) => {
                let t_num = num.get_type(scope)?;
                let t_mod = modulus.get_type(scope)?;

                if t_num != Type::Integer || t_mod != Type::Integer {
                    return Err(TypeError);
                }

                Ok(t_num)
            }
            Expression::Xor(vs) | Expression::And(vs) | Expression::Or(vs) => {
                // TODO bit strings
                for v in vs {
                    if v.get_type(scope)? != Type::Boolean {
                        return Err(TypeError);
                    }
                }

                Ok(Type::Boolean)
            }

            _ => {
                println!("not implemented!");
                Err(TypeError)
            }
        }
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
    println!("{:#?}", scp.lookup(foo_identifier.clone()));
    scp.leave();
    println!("{:#?}", scp.lookup(foo_identifier));
}
