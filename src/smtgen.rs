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

        String::from_utf8(buf)
            .expect("can't happen, we only write utf8")
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

pub fn statevarname() -> SmtExpr {
    /*
    SmtExpr::List(vec![
        SmtExpr::Atom("'".to_string()),
        SmtExpr::Atom("sspds-rs".to_string()),
        SmtExpr::Atom("state".to_string()),
    ])
    */

    SmtExpr::Atom(String::from("sspds-rs-state"))
}

impl From<Expression> for SmtExpr {
    fn from(expr: Expression) -> SmtExpr {
        match expr {
            Expression::BooleanLiteral(litname) => SmtExpr::Atom(litname),
            Expression::IntegerLiteral(litname) => SmtExpr::Atom(litname),
            Expression::Equals(exprs) => {
                let mut acc = vec![SmtExpr::Atom("=".to_string())];
                for expr in exprs {
                    acc.push(expr.clone().into());
                }

                SmtExpr::List(acc)
            }
            Expression::Identifier(Identifier::Scalar(identname)) => SmtExpr::Atom(identname),
            Expression::Identifier(Identifier::Local(identname)) => SmtExpr::Atom(identname),
            Expression::Identifier(Identifier::State {
                name: identname,
                pkgname,
            }) => SmtExpr::List(vec![
                SmtExpr::Atom(format!("state-{}-{}", pkgname, identname)),
                statevarname(),
            ]),
            Expression::Bot => SmtExpr::Atom("bot".to_string()),
            Expression::Sample(_tipe) => {
                // TODO: fix this later! This is generally speaking not correct!
                SmtExpr::Atom("rand".to_string())
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
            Type::Boolean => SmtExpr::Atom("Bool".to_string()),
            _ => {
                panic!("not implemented!")
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

impl<C, E> From<SmtIs<C, E>> for SmtExpr  where C: Into<String>, E: Into<SmtExpr>{
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
            SspSmtVar::PackageStateConstructor{pkgname} => SmtExpr::Atom(format!("mk-state-{}", pkgname)),
            SspSmtVar::OracleReturnConstructor{pkgname, oname} => SmtExpr::Atom(format!("mk-return-{}-{}", pkgname, oname)),
            SspSmtVar::OracleAbort{pkgname, oname} => SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, oname)),
            SspSmtVar::CompositionStateConstructor{compname} => SmtExpr::Atom(format!("mk-composition-state-{}", compname)),
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
    E: Into<SmtExpr>
    {
    pub con: C,
    pub expr: E,
}

pub enum SspSmtVar {
    GlobalState,
    SelfState,
    ReturnValue,
    CompositionStateConstructor{compname: String},
    PackageStateConstructor{pkgname: String},
    OracleReturnConstructor{pkgname: String, oname: String},
    OracleAbort{pkgname: String, oname: String},
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::string::FromUtf8Error;
    use thiserror::Error;

    #[derive(Error, Debug)]
    enum TestError {
        #[error("Error parsing the utf8: {0}")]
        Utf8DecodeError(#[from] FromUtf8Error),
        #[error("Error Writing: {0}")]
        WriteError(#[from] std::io::Error),
    }

    type TestResult = std::result::Result<(), TestError>;

    #[test]
    fn test_smtlet() -> TestResult {
        let l = SmtLet {
            bindings: vec![(
                "x".into(),
                Expression::IntegerLiteral(String::from("42")).into(),
            )],
            body: SmtExpr::Atom(String::from("x")),
        };

        let out: SmtExpr = l.into();
        let mut str = Vec::<u8>::new();
        out.write_smt_to(&mut str)?;

        assert_eq!(String::from_utf8(str)?, "(let ((x 42)) x)");

        Ok(())
    }
}
