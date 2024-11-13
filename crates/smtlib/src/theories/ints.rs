//! https://smt-lib.org/theories-Ints.shtml

use crate::syntax::{sort::Sort, term::Term, tokens::Symbol};

pub enum Symbols {
    Int,
    Minus,
    Plus,
    Asterisk,
    Div,
    Mod,
    Abs,
    Lte,
    Lt,
    Gte,
    Gt,
}

impl From<Symbols> for Symbol {
    fn from(value: Symbols) -> Symbol {
        match value {
            Symbols::Int => "Int",
            Symbols::Minus => "-",
            Symbols::Plus => "+",
            Symbols::Asterisk => "*",
            Symbols::Div => "div",
            Symbols::Mod => "mod",
            Symbols::Abs => "abs",
            Symbols::Lte => "<=",
            Symbols::Lt => "<",
            Symbols::Gte => ">=",
            Symbols::Gt => ">",
        }
        .into()
    }
}

pub fn int() -> Sort {
    Sort {
        name: Symbols::Int.into(),
        parameters: vec![],
    }
}

pub fn negate(term: Term) -> Term {
    Term::Base(Symbols::Minus.into(), vec![term])
}

pub fn sub(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Minus.into(), terms)
}

pub fn add(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Plus.into(), terms)
}

pub fn mul(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Asterisk.into(), terms)
}

pub fn div(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Div.into(), terms)
}

pub fn modulo(lhs: Term, rhs: Term) -> Term {
    Term::Base(Symbols::Mod.into(), vec![lhs, rhs])
}

pub fn abs(term: Term) -> Term {
    Term::Base(Symbols::Abs.into(), vec![term])
}

pub fn lte(lhs: Term, rhs: Term) -> Term {
    Term::Base(Symbols::Lte.into(), vec![lhs, rhs])
}

pub fn lt(lhs: Term, rhs: Term) -> Term {
    Term::Base(Symbols::Lt.into(), vec![lhs, rhs])
}

pub fn gte(lhs: Term, rhs: Term) -> Term {
    Term::Base(Symbols::Gte.into(), vec![lhs, rhs])
}

pub fn gt(lhs: Term, rhs: Term) -> Term {
    Term::Base(Symbols::Gt.into(), vec![lhs, rhs])
}
