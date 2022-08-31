use super::exprs::{SmtExpr, SspSmtVar};
use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

impl From<Expression> for SmtExpr {
    fn from(expr: Expression) -> SmtExpr {
        eprintln!("DEBUG expr->smt: {expr:?}");
        match expr {
            Expression::Typed(t, inner) if *inner == Expression::EmptyTable => {
                if let Type::Table(idxtipe, valtipe) = t {
                    (
                        (
                            "as",
                            "const",
                            ("Array", *idxtipe, Type::Maybe(valtipe.clone())),
                        ),
                        ("as", "mk-none", Type::Maybe(valtipe)),
                    )
                        .into()
                } else {
                    panic!("Empty table of type {:?}", t)
                }
            }
            Expression::Typed(_t, inner) => SmtExpr::from(*inner),
            Expression::Unwrap(_inner) => {
                panic!("unwrap expressions need to be on the right hand side of an assign!");
                // TODO find a better way to present that error to the user.
            }
            Expression::Some(inner) => {
                SmtExpr::List(vec![SmtExpr::Atom("mk-some".into()), SmtExpr::from(*inner)])
            }
            Expression::None(inner) => SmtExpr::List(vec![
                SmtExpr::Atom("as".into()),
                SmtExpr::Atom("mk-none".into()),
                Type::Maybe(Box::new(inner)).into(),
            ]),
            Expression::StringLiteral(litname) => SmtExpr::Atom(format!("\"{}\"", litname)),
            Expression::BooleanLiteral(litname) => SmtExpr::Atom(litname),
            Expression::IntegerLiteral(litname) => SmtExpr::Atom(litname),
            Expression::Equals(exprs) => {
                let mut acc = vec![SmtExpr::Atom("=".to_string())];
                for expr in exprs {
                    acc.push(expr.clone().into());
                }

                SmtExpr::List(acc)
            }
            Expression::Add(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("+".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            Expression::Sub(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("-".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            Expression::Mul(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("*".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            Expression::Div(lhs, rhs) => SmtExpr::List(vec![
                SmtExpr::Atom("/".to_string()),
                SmtExpr::from(*lhs),
                SmtExpr::from(*rhs),
            ]),
            Expression::Not(expr) => {
                SmtExpr::List(vec![SmtExpr::Atom("not".to_string()), (*expr).into()])
            }
            Expression::And(vals) => SmtExpr::List({
                let mut list = vec![SmtExpr::Atom("and".to_owned())];
                for val in vals {
                    list.push(SmtExpr::from(val))
                }
                list
            }),
            Expression::Or(vals) => SmtExpr::List({
                let mut list = vec![SmtExpr::Atom("or".to_owned())];
                for val in vals {
                    list.push(SmtExpr::from(val))
                }
                list
            }),
            Expression::Xor(vals) => SmtExpr::List({
                let mut list = vec![SmtExpr::Atom("xor".to_owned())];
                for val in vals {
                    list.push(SmtExpr::from(val))
                }
                list
            }),
            Expression::Identifier(Identifier::Scalar(identname)) => {
                panic! {"Found a scalar {:} which should have been removed by varspecify at this point", identname}
            }
            Expression::Identifier(Identifier::Local(identname)) => SmtExpr::Atom(identname),
            Expression::Identifier(Identifier::State {
                name: identname,
                pkgname,
                compname,
            }) => SmtExpr::List(vec![
                SmtExpr::Atom(format!("state-{}-{}-{}", compname, pkgname, identname)),
                SspSmtVar::SelfState.into(),
            ]),
            Expression::Identifier(Identifier::Params {
                name_in_comp,
                compname,
                ..
            }) => SmtExpr::List(vec![
                // Note: when changing this, make sure you also change state_helpers!
                SmtExpr::Atom(format!("composition-param-{}-{}", compname, name_in_comp)),
                SspSmtVar::CompositionContext.into(),
            ]),
            Expression::Bot => SmtExpr::Atom("bot".to_string()),
            Expression::TableAccess(table, index) => SmtExpr::List(vec![
                SmtExpr::Atom("select".into()),
                table.to_expression().into(),
                (*index).into(),
            ]),
            Expression::Tuple(exprs) => {
                let mut l = vec![SmtExpr::Atom(format!("mk-tuple{}", exprs.len()))];

                for expr in exprs {
                    l.push(expr.into())
                }

                SmtExpr::List(l)
            }
            Expression::FnCall(
                Identifier::Params {
                    name_in_comp: name,
                    compname,
                    ..
                },
                args,
            ) => {
                let fn_name = format!("__func-{compname}-{name}");
                let mut call = vec![SmtExpr::Atom(fn_name)];

                for expr in args {
                    call.push(expr.into());
                }

                SmtExpr::List(call)
            }
            Expression::FnCall(id, exprs) => {
                let mut call = vec![SmtExpr::Atom(id.ident())];

                for expr in exprs {
                    call.push(expr.into());
                }

                SmtExpr::List(call)
            }
            Expression::List(inner) => {
                let t = if let Expression::Typed(t, _) = inner[0].clone() {
                    Some(t)
                } else {
                    None
                };

                let t = t.unwrap();

                let nil = SmtExpr::List(vec![
                    SmtExpr::Atom("as".to_owned()),
                    SmtExpr::Atom("nil".to_owned()),
                    SmtExpr::List(vec![SmtExpr::Atom("List".to_owned()), t.into()]),
                ]);

                let mut lst = nil;

                for el in inner.iter().rev() {
                    lst =
                        SmtExpr::List(vec![SmtExpr::Atom("insert".into()), el.clone().into(), lst])
                }

                lst
            }
            Expression::Set(inner) => {
                let t = if let Expression::Typed(t, _) = inner[0].clone() {
                    Some(t)
                } else {
                    None
                };

                let t = t.unwrap();

                let empty_set = SmtExpr::List(vec![
                    SmtExpr::List(vec![
                        SmtExpr::Atom("as".to_owned()),
                        SmtExpr::Atom("const".to_owned()),
                        SmtExpr::List(vec![SmtExpr::Atom("Set".to_owned()), t.into()]),
                    ]),
                    SmtExpr::Atom("false".to_string()),
                ]);

                let mut set = empty_set;

                for el in inner.iter().rev() {
                    set = SmtExpr::List(vec![
                        SmtExpr::Atom("store".into()),
                        set,
                        el.clone().into(),
                        SmtExpr::Atom("true".to_string()),
                    ])
                }

                set
            }
            _ => {
                panic!("not implemented: {:?}", expr);
            }
        }
    }
}
