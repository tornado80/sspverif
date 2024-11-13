//!  https://smt-lib.org/theories-Core.shtml

use crate::syntax::{sort::Sort, term::Term, tokens::Symbol};

pub enum Symbols {
    Bool,
    True,
    False,
    Not,
    Implies,
    And,
    Or,
    Xor,
    Eq,
    Distinct,
    Ite,
}

impl From<Symbols> for Symbol {
    fn from(value: Symbols) -> Symbol {
        match value {
            Symbols::Bool => "Bool",
            Symbols::True => "true",
            Symbols::False => "false",
            Symbols::Not => "not",
            Symbols::Implies => "=>",
            Symbols::And => "and",
            Symbols::Or => "or",
            Symbols::Xor => "xor",
            Symbols::Eq => "=",
            Symbols::Distinct => "distinct",
            Symbols::Ite => "ite",
        }
        .into()
    }
}

pub fn bool_() -> Sort {
    Sort {
        name: Symbols::Bool.into(),
        parameters: vec![],
    }
}

pub fn true_() -> Term {
    Symbols::True.into()
}

pub fn false_() -> Term {
    Symbols::False.into()
}

pub fn not(term: Term) -> Term {
    Term::Base(Symbols::Not.into(), vec![term])
}

pub fn implies(pre: Term, post: Term) -> Term {
    Term::Base(Symbols::Implies.into(), vec![pre, post])
}

pub fn and(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::And.into(), terms)
}

pub fn or(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Or.into(), terms)
}

pub fn xor(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Xor.into(), terms)
}

pub fn eq(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Eq.into(), terms)
}

pub fn neq(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Distinct.into(), terms)
}

pub fn ite(cond: Term, then: Term, els: Term) -> Term {
    Term::Base(Symbols::Ite.into(), vec![cond, then, els])
}
