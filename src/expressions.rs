use crate::identifier::Identifier;
use crate::types::{Type, TypeResult, TypeError};
use crate::scope::Scope;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Bot,
    Sample(Type),
    StringLiteral(String),
    IntegerLiteral(String),
    BooleanLiteral(String),
    Identifier(Box<Identifier>),
    TableAccess(Box<Identifier>, Box<Expression>),
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

impl Expression {
    /*
    fn new_identifier(name: &str) -> Expression {
        Expression::Identifier(name.to_string())
    }
    */

    pub fn new_equals(exprs: Vec<&Expression>) -> Expression {
        Expression::Equals(
            exprs
                .into_iter()
                .map(|expr| Box::new(expr.clone()))
                .collect(),
        )
    }

    pub fn get_type(&self, scope: &Scope) -> TypeResult {
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
                println!("{:#?}", self);
                Err(TypeError)
            }
        }
    }
}

#[macro_export]
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

#[macro_export]
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

#[macro_export]
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

#[macro_export]
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
