use crate::syntax::{term::Term, tokens::Symbol};

pub enum Symbols {
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

impl Symbols {
    fn symbol(self) -> Symbol {
        match self {
            Symbols::True => "true".into(),
            Symbols::False => "false".into(),
            Symbols::Not => "not".into(),
            Symbols::Implies => "=>".into(),
            Symbols::And => "and".into(),
            Symbols::Or => "or".into(),
            Symbols::Xor => "xor".into(),
            Symbols::Eq => "=".into(),
            Symbols::Distinct => "distinct".into(),
            Symbols::Ite => "ite".into(),
        }
    }
}

pub fn true_() -> Term {
    Symbols::True.symbol().into()
}

pub fn false_() -> Term {
    Symbols::False.symbol().into()
}

pub fn not(term: Term) -> Term {
    Term::Base(Symbols::Not.symbol().into(), vec![term])
}

pub fn implies(pre: Term, post: Term) -> Term {
    Term::Base(Symbols::Implies.symbol().into(), vec![pre, post])
}

pub fn and(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::And.symbol().into(), terms)
}

pub fn or(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Or.symbol().into(), terms)
}

pub fn xor(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Xor.symbol().into(), terms)
}

pub fn eq(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Eq.symbol().into(), terms)
}

pub fn neq(terms: Vec<Term>) -> Term {
    Term::Base(Symbols::Distinct.symbol().into(), terms)
}

pub fn ite(cond: Term, then: Term, els: Term) -> Term {
    Term::Base(Symbols::Ite.symbol().into(), vec![cond, then, els])
}
