use crate::errors::TypeError;
use crate::identifier::Identifier;
use crate::scope::Scope;
use crate::types::{Type, TypeResult};

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Bot,
    Sample(Type),
    StringLiteral(String),
    IntegerLiteral(String),
    BooleanLiteral(String),
    Identifier(Identifier),
    TableAccess(Box<Identifier>, Box<Expression>),
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
            _ => {
                panic!("Expression: not implemented: {:#?}", self)
            }
        })
    }

    pub fn new_equals(exprs: Vec<&Expression>) -> Expression {
        Expression::Equals(exprs.into_iter().cloned().collect())
    }

    pub fn get_type(&self, scope: &Scope) -> TypeResult {
        match self {
            Expression::Sample(t) => Ok(t.clone()),
            Expression::StringLiteral(_) => Ok(Type::String),
            Expression::IntegerLiteral(_) => Ok(Type::Integer),
            Expression::BooleanLiteral(_) => Ok(Type::Boolean),
            Expression::Equals(_) => Ok(Type::Boolean),
            Expression::Tuple(elems) => {
                let mut types = vec![];

                for elem in elems {
                    types.push(elem.get_type(scope)?);
                }

                Ok(Type::Tuple(types))
            }
            Expression::Some(v) => Ok(Type::Maybe(Box::new(v.get_type(scope)?))),
            Expression::None(t) => Ok(Type::Maybe(Box::new(t.clone()))),
            Expression::Unwrap(v) => {
                if let Expression::Some(inner) = &**v {
                    Ok(inner.get_type(scope)?)
                } else {
                    Err(TypeError("".to_string()))
                }
            }
            Expression::Neg(v) => {
                let t = v.get_type(scope)?;
                if t == Type::Integer && matches!(t, Type::AddiGroupEl(_)) {
                    Ok(t)
                } else {
                    Err(TypeError("".to_string()))
                }
            }
            Expression::Not(v) => {
                let t = v.get_type(scope)?;
                if t != Type::Boolean {
                    return Err(TypeError("".to_string()));
                }

                Ok(t)
            }
            Expression::Inv(v) => {
                let t = v.get_type(scope)?;
                if matches!(t, Type::MultGroupEl(_)) {
                    return Ok(t);
                }

                Err(TypeError("".to_string()))
            }
            Expression::Add(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                let same_type = t_left == t_right;
                let left_is_int = t_left == Type::Integer;
                let left_is_age = matches!(t_left, Type::AddiGroupEl(_));

                if same_type && (left_is_int || left_is_age) {
                    Ok(t_left)
                } else {
                    Err(TypeError("".to_string()))
                }
            }
            Expression::Mul(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                let same_type = t_left == t_right;
                let left_is_int = t_left == Type::Integer;
                let left_is_mge = matches!(t_left, Type::MultGroupEl(_));
                let right_is_age = matches!(t_right, Type::AddiGroupEl(_));

                #[allow(clippy::collapsible_else_if)]
                if same_type {
                    if left_is_int || left_is_mge {
                        Ok(t_left)
                    } else {
                        Err(TypeError("".to_string()))
                    }
                } else {
                    if left_is_int && right_is_age {
                        Ok(t_right)
                    } else {
                        Err(TypeError("".to_string()))
                    }
                }
            }
            Expression::Sub(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                if (t_left == Type::Integer || matches!(t_left, Type::AddiGroupEl(_)))
                    && t_left == t_right
                {
                    return Ok(t_left);
                }

                Err(TypeError("".to_string()))
            }
            Expression::Div(left, right) => {
                let t_left = left.get_type(scope)?;
                let t_right = right.get_type(scope)?;

                if t_left != Type::Integer || t_left != t_right {
                    return Err(TypeError("".to_string()));
                }

                Ok(t_left)
            }
            Expression::Pow(base, exp) => {
                let t_base = base.get_type(scope)?;
                let t_exp = exp.get_type(scope)?;

                let base_is_int = t_base == Type::Integer;
                let exp_is_int = t_exp == Type::Integer;
                let base_is_mge = matches!(t_base, Type::MultGroupEl(_));

                if exp_is_int {
                    if base_is_int || base_is_mge {
                        Ok(t_base)
                    } else {
                        Err(TypeError("".to_string()))
                    }
                } else {
                    Err(TypeError("".to_string()))
                }
            }

            Expression::Mod(num, modulus) => {
                let t_num = num.get_type(scope)?;
                let t_mod = modulus.get_type(scope)?;

                if t_num != Type::Integer || t_mod != Type::Integer {
                    return Err(TypeError("".to_string()));
                }

                Ok(t_num)
            }

            Expression::Xor(vs) | Expression::And(vs) | Expression::Or(vs) => {
                // TODO bit strings
                for v in vs {
                    if v.get_type(scope)? != Type::Boolean {
                        return Err(TypeError("".to_string()));
                    }
                }

                Ok(Type::Boolean)
            }

            Expression::FnCall(name, args) => {
                if let Some(Type::Fn(arg_types, ret_type)) =
                    scope.lookup(&Identifier::new_scalar(name))
                {
                    // 1. check that arg types match args
                    if args.len() != arg_types.len() {
                        return Err(TypeError("".to_string()));
                    }

                    for (i, arg) in args.iter().enumerate() {
                        if arg.get_type(scope)? != arg_types[i] {
                            return Err(TypeError("".to_string()));
                        }
                    }

                    // 2. return ret type
                    Ok(*ret_type)
                } else {
                    Err(TypeError("".to_string()))
                }
            }

            Expression::OracleInvoc(name, args) => {
                if let Some(entry) = scope.lookup(&Identifier::new_scalar(name)) {
                    if let Type::Oracle(arg_types, ret_type) = entry {
                        // 1. check that arg types match args
                        if args.len() != arg_types.len() {
                            return Err(TypeError(
                                "oracle invocation arg count mismatch".to_string(),
                            ));
                        }

                        for (i, arg) in args.iter().enumerate() {
                            if arg.get_type(scope)? != arg_types[i] {
                                return Err(TypeError(format!(
                                    "oracle invocation arg type doesn't match at position {:}",
                                    i
                                )));
                            }
                        }

                        // 2. return ret type
                        Ok(*ret_type)
                    } else {
                        Err(TypeError(format!("expected oracle, got {:#?}", entry)))
                    }
                } else {
                    Err(TypeError(format!("couldn't look up oracle {:}", name)))
                }
            }

            Expression::Identifier(id) => {
                if let Some(t) = scope.lookup(id) {
                    Ok(t)
                } else {
                    Err(TypeError("".to_string()))
                }
            }

            _ => {
                println!("get_type not implemented for:");
                println!("{:#?}", self);
                Err(TypeError("".to_string()))
            }
        }
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
