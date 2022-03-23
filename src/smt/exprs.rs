use std::io::{Result, Write};

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

pub fn smt_to_string<T: Into<SmtExpr>>(t: T) -> String {
    let expr: SmtExpr = t.into();
    expr.to_string()
}

pub trait SmtFmt {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()>;

    fn to_string(&self) -> String {
        let mut buf = vec![];
        self.write_smt_to(&mut buf)
            .expect("can't happen, we assume the buffer never errors");

        String::from_utf8(buf).expect("can't happen, we only write utf8")
    }
}

#[derive(Debug, Clone)]
pub enum SmtExpr {
    Comment(String),
    Atom(String),
    List(Vec<SmtExpr>),
}

impl SmtFmt for SmtExpr {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()> {
        match self {
            SmtExpr::Comment(str) => write!(write, "; {}", str),
            SmtExpr::Atom(str) => write!(write, "{}", str),
            SmtExpr::List(lst) => {
                let mut peek = lst.iter().peekable();

                write!(write, "(")?;
                while let Some(elem) = peek.next() {
                    elem.write_smt_to(write)?;

                    if peek.peek().is_some() {
                        write!(write, " ")?;
                    }
                }
                write!(write, ")")
            }
        }
    }
}

impl From<Expression> for SmtExpr {
    fn from(expr: Expression) -> SmtExpr {
        match expr {
            Expression::Typed(t, inner) => match *inner {
                Expression::Unwrap(inner) => {
                    panic!("unwrap expressions need to be on the right hand side of an assign!");
                    // TODO find a better way to present that error to the user.
                }
                Expression::Some(inner) => {
                    if let Type::Maybe(t_inner) = t {
                        SmtExpr::List(vec![
                            SmtExpr::Atom(format!("mk-some-{}", smt_to_string(*t_inner))),
                            SmtExpr::from(*inner),
                        ])
                    } else {
                        unreachable!()
                    }
                }
                _ => SmtExpr::from(*inner),
            },
            Expression::None(t) => SmtExpr::Atom(format!("mk-none-{}", smt_to_string(t))),
            Expression::BooleanLiteral(litname) => SmtExpr::Atom(litname),
            Expression::IntegerLiteral(litname) => SmtExpr::Atom(litname),
            Expression::Equals(exprs) => {
                let mut acc = vec![SmtExpr::Atom("=".to_string())];
                for expr in exprs {
                    acc.push(expr.clone().into());
                }

                SmtExpr::List(acc)
            }
            Expression::Not(expr) => {
                SmtExpr::List(vec![SmtExpr::Atom("not".to_string()), (*expr).into()])
            }
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
            Expression::Bot => SmtExpr::Atom("bot".to_string()),
            Expression::TableAccess(table, index) => SmtExpr::List(vec![
                SmtExpr::Atom("select".into()),
                table.to_expression().into(),
                (*index).into(),
            ]),
            Expression::Tuple(exprs) => {
                let mut l = vec![SmtExpr::Atom(format!("mk-tuple-{}", "grrrTODO"))];

                for expr in exprs {
                    l.push(expr.into())
                }

                SmtExpr::List(l)
            }
            Expression::FnCall(name, exprs) => {
                let mut call = vec![SmtExpr::Atom(name)];

                for expr in exprs {
                    call.push(expr.into());
                }

                SmtExpr::List(call)
            }
            _ => {
                panic!("not implemented: {:?}", expr);
            }
        }
    }
}

impl From<Type> for SmtExpr {
    fn from(t: Type) -> SmtExpr {
        match t {
            Type::Bits(length) => {
                // TODO make sure we define this somewhere
                SmtExpr::Atom(format!("Bits_{}", length))
            }
            Type::Maybe(t) => match *t {
                Type::Boolean => SmtExpr::Atom("Maybe_Bool".to_string()),
                Type::Integer => SmtExpr::Atom("Maybe_Int".to_string()),
                Type::String => SmtExpr::Atom("Maybe_String".to_string()),
                Type::Bits(l) => SmtExpr::Atom(format!("Maybe_Bits_{}", l)),
                _ => {
                    panic!("Maybe is only implemented over Bool, Int, String and Bits.")
                }
            },
            Type::Boolean => SmtExpr::Atom("Bool".to_string()),
            Type::Integer => SmtExpr::Atom("Int".into()),
            Type::Table(t_idx, t_val) => SmtExpr::List(vec![
                SmtExpr::Atom("Array".into()),
                (*t_idx).into(),
                (*t_val).into(),
            ]),
            Type::Tuple(types) => SmtExpr::List(vec![SmtExpr::Atom(format!(
                "Tuple__{}",
                types
                    .into_iter()
                    .map(|t| {
                        let expr: SmtExpr = t.into();
                        smt_to_string(expr)
                    })
                    .collect::<Vec<String>>()
                    .join("_")
            ))]),
            _ => {
                panic!("not implemented: {:?}", t)
            }
        }
    }
}

impl<C, T, E> From<SmtIte<C, T, E>> for SmtExpr
where
    C: Into<SmtExpr>,
    T: Into<SmtExpr>,
    E: Into<SmtExpr>,
{
    fn from(ite: SmtIte<C, T, E>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::Atom("ite".into()),
            ite.cond.into(),
            ite.then.into(),
            ite.els.into(),
        ])
    }
}

impl<C, E> From<SmtIs<C, E>> for SmtExpr
where
    C: Into<String>,
    E: Into<SmtExpr>,
{
    fn from(is: SmtIs<C, E>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::List(vec![
                SmtExpr::Atom("_".into()),
                SmtExpr::Atom("is".into()),
                SmtExpr::Atom(is.con.into()),
            ]),
            is.expr.into(),
        ])
    }
}

impl<B> From<SmtLet<B>> for SmtExpr
where
    B: Into<SmtExpr>,
{
    fn from(l: SmtLet<B>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::Atom(String::from("let")),
            SmtExpr::List(
                l.bindings
                    .into_iter()
                    .map(|(id, expr)| SmtExpr::List(vec![SmtExpr::Atom(id), expr]))
                    .collect(),
            ),
            l.body.into(),
        ])
    }
}

impl From<SspSmtVar> for SmtExpr {
    fn from(v: SspSmtVar) -> SmtExpr {
        match v {
            SspSmtVar::GlobalState => SmtExpr::Atom("__global_state".into()),
            SspSmtVar::SelfState => SmtExpr::Atom("__self_state".into()),
            SspSmtVar::ReturnValue => SmtExpr::Atom("__ret".into()),
            SspSmtVar::OracleReturnConstructor { pkgname, oname } => {
                SmtExpr::Atom(format!("mk-return-{}-{}", pkgname, oname))
            }
            SspSmtVar::OracleAbort { pkgname, oname } => {
                SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, oname))
            }
        }
    }
}

pub struct SmtLet<B>
where
    B: Into<SmtExpr>,
{
    pub bindings: Vec<(String, SmtExpr)>,
    pub body: B,
}

pub struct SmtIte<C, T, E>
where
    C: Into<SmtExpr>,
    T: Into<SmtExpr>,
    E: Into<SmtExpr>,
{
    pub cond: C,
    pub then: T,
    pub els: E,
}

pub struct SmtIs<C, E>
where
    C: Into<String>,
    E: Into<SmtExpr>,
{
    pub con: C,
    pub expr: E,
}

pub enum SspSmtVar {
    GlobalState,
    SelfState,
    ReturnValue,
    OracleReturnConstructor { pkgname: String, oname: String },
    OracleAbort { pkgname: String, oname: String },
}
