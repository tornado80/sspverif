use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

use super::errors::{TypeError, TypeResult};
use super::scope::Scope;

pub fn get_type(expr: &Expression, scope: &Scope) -> TypeResult {
    match expr {
        Expression::Sample(t) => Ok(t.clone()),
        Expression::StringLiteral(_) => Ok(Type::String),
        Expression::IntegerLiteral(_) => Ok(Type::Integer),
        Expression::BooleanLiteral(_) => Ok(Type::Boolean),
        Expression::Equals(_) => Ok(Type::Boolean),
        Expression::Tuple(elems) => {
            let mut types = vec![];

            for elem in elems {
                types.push(get_type(&elem, scope)?);
            }

            Ok(Type::Tuple(types))
        }
        Expression::Some(v) => Ok(Type::Maybe(Box::new(get_type(v, scope)?))),
        Expression::None(t) => Ok(Type::Maybe(Box::new(t.clone()))),
        Expression::Unwrap(v) => {
            if let Expression::Some(inner) = &**v {
                Ok(get_type(inner, scope)?)
            } else {
                Err(TypeError("".to_string()))
            }
        }
        Expression::Neg(v) => {
            let t = get_type(v, scope)?;
            if t == Type::Integer && matches!(t, Type::AddiGroupEl(_)) {
                Ok(t)
            } else {
                Err(TypeError("".to_string()))
            }
        }
        Expression::Not(v) => {
            let t = get_type(v, scope)?;
            if t != Type::Boolean {
                return Err(TypeError("".to_string()));
            }

            Ok(t)
        }
        Expression::Inv(v) => {
            let t = get_type(v, scope)?;
            if matches!(t, Type::MultGroupEl(_)) {
                return Ok(t);
            }

            Err(TypeError("".to_string()))
        }
        Expression::Add(left, right) => {
            let t_left = get_type(left, scope)?;
            let t_right = get_type(right, scope)?;

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
            let t_left = get_type(left, scope)?;
            let t_right = get_type(right, scope)?;

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
            let t_left = get_type(left, scope)?;
            let t_right = get_type(right, scope)?;

            if (t_left == Type::Integer || matches!(t_left, Type::AddiGroupEl(_)))
                && t_left == t_right
            {
                return Ok(t_left);
            }

            Err(TypeError("".to_string()))
        }
        Expression::Div(left, right) => {
            let t_left = get_type(left, scope)?;
            let t_right = get_type(right, scope)?;

            if t_left != Type::Integer || t_left != t_right {
                return Err(TypeError("".to_string()));
            }

            Ok(t_left)
        }
        Expression::Pow(base, exp) => {
            let t_base = get_type(base, scope)?;
            let t_exp = get_type(exp, scope)?;

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
            let t_num = get_type(num, scope)?;
            let t_mod = get_type(modulus, scope)?;

            if t_num != Type::Integer || t_mod != Type::Integer {
                return Err(TypeError("".to_string()));
            }

            Ok(t_num)
        }

        Expression::Xor(vs) | Expression::And(vs) | Expression::Or(vs) => {
            // TODO bit strings
            for v in vs {
                if get_type(v, scope)? != Type::Boolean {
                    return Err(TypeError("".to_string()));
                }
            }

            Ok(Type::Boolean)
        }

        Expression::FnCall(name, args) => {
            if let Some(Type::Fn(arg_types, ret_type)) = scope.lookup(&Identifier::new_scalar(name))
            {
                // 1. check that arg types match args
                if args.len() != arg_types.len() {
                    return Err(TypeError("".to_string()));
                }

                for (i, arg) in args.iter().enumerate() {
                    if get_type(arg, scope)? != arg_types[i] {
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
                        if get_type(arg, scope)? != arg_types[i] {
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
            println!("{:#?}", expr);
            Err(TypeError("".to_string()))
        }
    }
}
