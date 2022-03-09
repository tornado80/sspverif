use crate::identifier::Identifier;
use crate::types::Type;

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Typed(Type, Box<Expression>),
    Bot,
    Sample(Type),
    StringLiteral(String),
    IntegerLiteral(String),
    BooleanLiteral(String),
    Identifier(Identifier),
    TableAccess(Identifier, Box<Expression>),
    Tuple(Vec<Expression>),
    List(Vec<Expression>),
    FnCall(String, Vec<Expression>),
    // or maybe at some point: FnCall(Box<Expression>, Vec<Expression>),
    OracleInvoc(String, Vec<Expression>),
    LowLevelOracleInvoc {
        name: String,
        pkgname: String,
        args: Vec<Expression>,
    },

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

    Equals(Vec<Expression>),
    And(Vec<Expression>),
    Or(Vec<Expression>),
    Xor(Vec<Expression>),

    // Set/List Operations:
    Sum(Box<Expression>),
    Prod(Box<Expression>),
    Any(Box<Expression>), // set/list or
    All(Box<Expression>), // set/list and
    Union(Box<Expression>),
    Cut(Box<Expression>),
    SetDiff(Box<Expression>),

    Concat(Vec<Expression>),
}

impl Expression {
    /*
    fn new_identifier(name: &str) -> Expression {
        Expression::Identifier(name.to_string())
    }
    */

    pub fn map<F>(&self, f: F) -> Expression
    where
        F: Fn(Expression) -> Expression + Copy,
    {
        f(match &self {
            Expression::Bot
            | Expression::None(_)
            | Expression::Sample(_)
            | Expression::StringLiteral(_)
            | Expression::IntegerLiteral(_)
            | Expression::BooleanLiteral(_)
            | Expression::Identifier(_) => self.clone(),

            Expression::Not(expr) => Expression::Not(Box::new(expr.map(f))),
            Expression::Some(expr) => Expression::Some(Box::new(expr.map(f))),
            Expression::TableAccess(id, expr) => {
                Expression::TableAccess(id.clone(), Box::new(expr.map(f)))
            }
            Expression::Tuple(exprs) => {
                Expression::Tuple(exprs.iter().map(|expr| expr.map(f)).collect())
            }
            Expression::Equals(exprs) => {
                Expression::Equals(exprs.iter().map(|expr| expr.map(f)).collect())
            }
            Expression::FnCall(name, exprs) => {
                Expression::FnCall(name.clone(), exprs.iter().map(|expr| expr.map(f)).collect())
            }
            Expression::OracleInvoc(name, exprs) => Expression::OracleInvoc(
                name.clone(),
                exprs.iter().map(|expr| expr.map(f)).collect(),
            ),
            Expression::LowLevelOracleInvoc {
                name,
                pkgname,
                args,
            } => Expression::LowLevelOracleInvoc {
                name: name.clone(),
                pkgname: pkgname.clone(),
                args: args.iter().map(|expr| expr.map(f)).collect(),
            },
            Expression::Typed(t, inner) => {
                Expression::Typed(t.clone(), Box::new(f(*inner.clone())))
            }
            _ => {
                panic!("Expression: not implemented: {:#?}", self)
            }
        })
    }

    pub fn new_equals(exprs: Vec<&Expression>) -> Expression {
        Expression::Equals(exprs.into_iter().cloned().collect())
    }
}

#[macro_export]
macro_rules! tuple {
    ( $($e:expr),* ) => {
        {
            Expression::Tuple(vec![ $( $e.clone(), )* ])
        }
    };
}

#[macro_export]
macro_rules! list {
    ( $($e:expr),* ) => {
        {
            Expression::List(vec![ $( $e.clone(), )* ])
        }
    };
}

#[macro_export]
macro_rules! oracleinvoc {
    ( $name:expr, $($e:expr),* ) => {
        {
            Expression::OracleInvoc(
                $name.to_string(),
                vec![ $( $e.clone(), )* ],
            )
        }
    };
}

#[macro_export]
macro_rules! fncall {
    ( $name:expr, $($e:expr),* ) => {
        {
            Expression::FnCall(
                $name.to_string(),
                vec![ $( $e.clone(), )* ],
            )
        }
    };
}
