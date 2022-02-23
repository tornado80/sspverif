use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

use super::errors::{ExpressionResult, TypeError, TypeResult};
use super::scope::Scope;

pub fn get_type(expr: &Expression, scope: &Scope) -> TypeResult {
    Ok(match expr {
        Expression::Typed(t, _) => t.clone(),
        _ => get_type(&typify(expr, scope)?, scope)?,
    })
}

pub fn typify(expr: &Expression, scope: &Scope) -> ExpressionResult {
    match expr {
        Expression::Sample(t) => Ok(Expression::Typed(t.clone(), expr.clone().into())),
        Expression::StringLiteral(_) => Ok(Expression::Typed(Type::String, expr.clone().into())),
        Expression::IntegerLiteral(_) => Ok(Expression::Typed(Type::Integer, expr.clone().into())),
        Expression::BooleanLiteral(_) => Ok(Expression::Typed(Type::Boolean, expr.clone().into())),
        Expression::Equals(exprs) => {
            let mut exprs_ = vec![];
            let mut t: Option<Type> = None;

            for expr in exprs {
                exprs_.push(typify(expr, scope)?);

                match &t {
                    None => {
                        t = Some(get_type(expr, scope)?);
                    }
                    Some(t_) => {
                        let t__ = get_type(expr, scope)?;
                        if t_ != &t__ {
                            return Err(TypeError(format!(
                                "equality compares expression of different type: {:?} {:?} in {:?}",
                                t_, t__, exprs
                            )));
                        }
                    }
                }
            }
            Ok(Expression::Typed(
                Type::Boolean,
                Box::new(Expression::Equals(exprs_)),
            ))
        }
        Expression::Tuple(elems) => {
            let mut types = vec![];
            let mut elems_ = vec![];

            for elem in elems {
                let elem_ = typify(&elem, scope)?;
                let t = get_type(&elem_, scope)?;
                types.push(t);
                elems_.push(elem_);
            }

            Ok(Expression::Typed(
                Type::Tuple(types),
                Box::new(Expression::Tuple(elems_)),
            ))
        }
        Expression::Some(v) => Ok(Expression::Typed(
            Type::Maybe(Box::new(get_type(v, scope)?)),
            Box::new(Expression::Some(Box::new(typify(v, scope)?))),
        )),
        Expression::None(t) => Ok(Expression::Typed(
            Type::Maybe(Box::new(t.clone())),
            Box::new(Expression::None(t.clone())),
        )),
        Expression::Unwrap(v) => {
            if let Expression::Some(inner) = &**v {
                Ok(Expression::Typed(
                    get_type(inner, scope)?,
                    Box::new(Expression::Unwrap(Box::new(typify(v, scope)?))),
                ))
            } else {
                Err(TypeError(format!("type error: {:?}", expr)))
            }
        }
        Expression::Neg(v) => {
            let t = get_type(v, scope)?;
            if t == Type::Integer || matches!(t, Type::AddiGroupEl(_)) {
                Ok(Expression::Typed(
                    t,
                    Box::new(Expression::Neg(Box::new(typify(v, scope)?))),
                ))
            } else {
                Err(TypeError(format!("type error: {:?}", expr)))
            }
        }
        Expression::Not(v) => {
            let t = get_type(v, scope)?;
            if t != Type::Boolean {
                return Err(TypeError(format!("type error: {:?}", expr)));
            }

            Ok(Expression::Typed(
                t,
                Box::new(Expression::Not(Box::new(typify(v, scope)?))),
            ))
        }
        Expression::Inv(v) => {
            let t = get_type(v, scope)?;
            if matches!(t, Type::MultGroupEl(_)) {
                return Ok(Expression::Typed(
                    t,
                    Box::new(Expression::Inv(Box::new(typify(v, scope)?))),
                ));
            } else {
                Err(TypeError(format!("type error: {:?}", expr)))
            }
        }
        Expression::Add(left, right) => {
            let t_left = get_type(left, scope)?;
            let t_right = get_type(right, scope)?;

            let same_type = t_left == t_right;
            let left_is_int = t_left == Type::Integer;
            let left_is_age = matches!(t_left, Type::AddiGroupEl(_));

            if same_type && (left_is_int || left_is_age) {
                Ok(Expression::Typed(
                    t_left,
                    Box::new(Expression::Add(
                        Box::new(typify(left, scope)?),
                        Box::new(typify(right, scope)?),
                    )),
                ))
            } else {
                Err(TypeError(format!("type error: {:?}", expr)))
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
                    Ok(Expression::Typed(
                        t_left,
                        Box::new(Expression::Mul(
                            Box::new(typify(left, scope)?),
                            Box::new(typify(right, scope)?),
                        )),
                    ))
                } else {
                    Err(TypeError(format!("type error: {:?}", expr)))
                }
            } else {
                if left_is_int && right_is_age {
                    Ok(Expression::Typed(
                        t_right,
                        Box::new(Expression::Mul(
                            Box::new(typify(left, scope)?),
                            Box::new(typify(right, scope)?),
                        )),
                    ))
                } else {
                    Err(TypeError(format!("type error: {:?}", expr)))
                }
            }
        }
        Expression::Sub(left, right) => {
            let t_left = get_type(left, scope)?;
            let t_right = get_type(right, scope)?;

            if (t_left == Type::Integer || matches!(t_left, Type::AddiGroupEl(_)))
                && t_left == t_right
            {
                return Ok(Expression::Typed(
                    t_left,
                    Box::new(Expression::Sub(
                        Box::new(typify(left, scope)?),
                        Box::new(typify(right, scope)?),
                    )),
                ));
            }

            Err(TypeError(format!("type error: {:?}", expr)))
        }
        Expression::Div(left, right) => {
            let t_left = get_type(left, scope)?;
            let t_right = get_type(right, scope)?;

            if t_left != Type::Integer || t_left != t_right {
                return Err(TypeError(format!("type error: {:?}", expr)));
            }

            Ok(Expression::Typed(
                t_left,
                Box::new(Expression::Div(
                    Box::new(typify(left, scope)?),
                    Box::new(typify(right, scope)?),
                )),
            ))
        }
        Expression::Pow(base, exp) => {
            let t_base = get_type(base, scope)?;
            let t_exp = get_type(exp, scope)?;

            let base_is_int = t_base == Type::Integer;
            let exp_is_int = t_exp == Type::Integer;
            let base_is_mge = matches!(t_base, Type::MultGroupEl(_));

            if exp_is_int {
                if base_is_int || base_is_mge {
                    Ok(Expression::Typed(
                        t_base,
                        Box::new(Expression::Pow(
                            Box::new(typify(base, scope)?),
                            Box::new(typify(exp, scope)?),
                        )),
                    ))
                } else {
                    Err(TypeError(format!("type error: {:?}", expr)))
                }
            } else {
                Err(TypeError(format!("type error: {:?}", expr)))
            }
        }

        Expression::Mod(num, modulus) => {
            let t_num = get_type(num, scope)?;
            let t_mod = get_type(modulus, scope)?;

            if t_num != Type::Integer || t_mod != Type::Integer {
                return Err(TypeError(format!("type error: {:?}", expr)));
            }

            Ok(Expression::Typed(
                t_num,
                Box::new(Expression::Pow(
                    Box::new(typify(num, scope)?),
                    Box::new(typify(modulus, scope)?),
                )),
            ))
        }

        Expression::Xor(vs) => {
            let mut vs_ = vec![];
            // TODO bit strings
            for v in vs {
                let v_ = typify(v, scope)?;
                if get_type(&v_, scope)? != Type::Boolean {
                    return Err(TypeError(format!("type error: {:?}", expr)));
                }

                vs_.push(v_);
            }

            Ok(Expression::Typed(
                Type::Boolean,
                Box::new(Expression::Xor(vs_)),
            ))
        }

        Expression::And(vs) => {
            let mut vs_ = vec![];
            // TODO bit strings
            for v in vs {
                let v_ = typify(v, scope)?;
                if get_type(&v_, scope)? != Type::Boolean {
                    return Err(TypeError(format!("type error: {:?}", expr)));
                }
                vs_.push(v_);
            }

            Ok(Expression::Typed(
                Type::Boolean,
                Box::new(Expression::And(vs_)),
            ))
        }

        Expression::Or(vs) => {
            let mut vs_ = vec![];
            // TODO bit strings
            for v in vs {
                let v_ = typify(v, scope)?;
                if get_type(&v_, scope)? != Type::Boolean {
                    return Err(TypeError(format!("type error: {:?}", expr)));
                }
                vs_.push(v_);
            }

            Ok(Expression::Typed(
                Type::Boolean,
                Box::new(Expression::Or(vs_)),
            ))
        }

        Expression::FnCall(name, args) => {
            if let Some(Type::Fn(arg_types, ret_type)) = scope.lookup(&Identifier::new_scalar(name))
            {
                // 1. check that arg types match args
                if args.len() != arg_types.len() {
                    return Err(TypeError(format!("type error: {:?}", expr)));
                }

                for (i, arg) in args.iter().enumerate() {
                    if get_type(arg, scope)? != arg_types[i] {
                        return Err(TypeError(format!("type error: {:?}", expr)));
                    }
                }

                // 2. return ret type
                Ok(Expression::Typed(
                    *ret_type,
                    Box::new(Expression::OracleInvoc(name.clone(), args.clone())),
                ))
            } else {
                Err(TypeError(format!("type error: {:?}", expr)))
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
                        let t_arg = get_type(arg, scope)?;
                        if t_arg != arg_types[i] {
                            return Err(TypeError(format!(
                                "oracle {:} invocation arg type doesn't match at position {:}. expected {:?}, got {:?}",
                                name,
                                i,
                                arg_types[i],
                                t_arg
                            )));
                        }
                    }

                    // 2. return ret type
                    Ok(Expression::Typed(
                        *ret_type,
                        Box::new(Expression::OracleInvoc(name.clone(), args.clone())),
                    ))
                } else {
                    Err(TypeError(format!("expected oracle, got {:#?}", entry)))
                }
            } else {
                Err(TypeError(format!("couldn't look up oracle {:}", name)))
            }
        }

        Expression::Identifier(id) => {
            if let Some(t) = scope.lookup(id) {
                Ok(Expression::Typed(
                    t,
                    Box::new(Expression::Identifier(id.clone())),
                ))
            } else {
                Err(TypeError(format!("type error: {:?}", expr)))
            }
        }
        Expression::TableAccess(id, expr) => match scope.lookup(&**id) {
            Some(Type::Table(t_idx, t_val)) => {
                let expr_ = typify(&expr, scope)?;
                let t_expr = get_type(&expr_, scope)?;
                if *t_idx == t_expr {
                    Ok(Expression::Typed(
                        *t_val,
                        Box::new(Expression::TableAccess(id.clone(), Box::new(expr_))),
                    ))
                } else {
                    Err(TypeError(format!(
                        "type error: bad index type. expected {:?}, got {:?}",
                        t_idx, t_expr
                    )))
                }
            }
            Some(t) => Err(TypeError(format!(
                "type error: table access on value of type {:?}",
                t
            ))),
            _ => Err(TypeError(format!(
                "error during table accesses; couldn't find identifier {:?} in scope",
                id
            ))),
        },
        _ => {
            println!("get_type not implemented for:");
            println!("{:#?}", expr);
            Err(TypeError(format!("type error: {:?}", expr)))
        }
    }
}
