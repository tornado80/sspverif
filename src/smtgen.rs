use std::io::{Result, Write};
//use std::io::prelude::*;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

pub trait SmtFmt {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()>;
}

#[derive(Debug, Clone)]
pub enum SmtExpr {
    Comment(String),
    Atom(String),
    List(Vec<SmtExpr>)
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
                };
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
            Expression::BooleanLiteral(litname) => {
                SmtExpr::Atom(litname)
            },
            Expression::IntegerLiteral(litname) => {
                SmtExpr::Atom(litname)
            }
            Expression::Equals(exprs) => {
                let mut acc = vec![
                    SmtExpr::Atom("=".to_string())];
                for expr in exprs {
                    acc.push(expr.clone().into());
                }

                SmtExpr::List(acc)
            },
            Expression::Identifier(Identifier::Scalar(identname)) => {
                SmtExpr::Atom(identname)
            },
            Expression::Identifier(Identifier::Local(identname)) => {
                SmtExpr::Atom(identname)
            },
            Expression::Identifier(Identifier::State{name:identname, pkgname}) => {
                SmtExpr::List(vec![SmtExpr::Atom(format!("state-{}-{}", pkgname, identname)), statevarname()])
            },
            Expression::Bot => {
                SmtExpr::Atom("bot".to_string())
            },
            Expression::Sample(_tipe) => {
                // TODO: fix this later! This is generally speaking not correct!
                SmtExpr::Atom("rand".to_string())
            },
            Expression::FnCall(name, exprs) => {
                let mut call = vec![
                    SmtExpr::Atom(name),
                ];

                for expr in exprs {
                    call.push(expr.into());
                }

                SmtExpr::List(call)
            },
            _ => { panic!("not implemented: {:?}", expr); }
        }
    }
}

impl From<Type> for SmtExpr {
    fn from(t: Type) -> SmtExpr {
        match t {
            Type::Bits(length) => {
                // TODO make sure we define this somewhere
                SmtExpr::Atom(format!("Bits_{}", length))
            },
            Type::Boolean => {
                SmtExpr::Atom("Bool".to_string())
            },
            _ => {panic!("not implemented!")}
        }
    }
}

impl From<SmtLet> for SmtExpr {
    fn from(l: SmtLet) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::Atom(String::from("let")),
            SmtExpr::List(
                l.bindings
                    .into_iter()
                    .map(|(id, expr)| {
                        SmtExpr::List(vec![
                            id.to_expression().into(),
                            expr.into(),
                        ])
                    }).collect()
            ),
            l.body,           
        ])
    }
}

struct SmtLet {
    bindings: Vec<(Identifier, Expression)>,
    body: SmtExpr,
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
        let l = SmtLet{
            bindings: vec![(Identifier::Local(String::from("x")), Expression::IntegerLiteral(String::from("42")))],
            body: SmtExpr::Atom(String::from("x")),
        };

        let out: SmtExpr = l.into();
        let mut str = Vec::<u8>::new();
        out.write_smt_to(&mut str)?;

        assert_eq!(String::from_utf8(str)?, "(let ((x 42)) x)");

        Ok(())
    }
}