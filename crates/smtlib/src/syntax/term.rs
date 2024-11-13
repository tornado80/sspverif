use super::{
    identifier::Identifier,
    s_expr::{SExpr, SpecConstant},
    sort::Sort,
    tokens::{ReservedWord, Symbol},
};

#[derive(Debug, Clone)]
pub struct QualifiedIdentifier(pub Identifier, pub Option<Sort>);

impl From<QualifiedIdentifier> for SExpr {
    fn from(value: QualifiedIdentifier) -> Self {
        let QualifiedIdentifier(ident, sort) = value;
        if let Some(sort) = sort {
            let as_sexpr: SExpr = ReservedWord::As.into();
            SExpr::from_iter(vec![as_sexpr, ident.into(), sort.into()])
        } else {
            ident.into()
        }
    }
}

impl From<QualifiedIdentifier> for Term {
    fn from(value: QualifiedIdentifier) -> Self {
        Self::Base(value, vec![])
    }
}

impl From<Symbol> for QualifiedIdentifier {
    fn from(value: Symbol) -> Self {
        QualifiedIdentifier(Identifier(value, vec![]), None)
    }
}
impl From<&str> for QualifiedIdentifier {
    fn from(value: &str) -> Self {
        QualifiedIdentifier(Identifier(Symbol::parse(value).unwrap(), vec![]), None)
    }
}

#[derive(Debug, Clone)]
pub struct VarBinding(pub Symbol, pub Term);

impl From<VarBinding> for SExpr {
    fn from(value: VarBinding) -> Self {
        SExpr::SExpr(vec![value.0.into(), value.1.into()])
    }
}

#[derive(Debug, Clone)]
pub struct SortedVar(pub Symbol, pub Sort);

impl From<SortedVar> for SExpr {
    fn from(value: SortedVar) -> Self {
        SExpr::SExpr(vec![value.0.into(), value.1.into()])
    }
}

#[derive(Debug, Clone)]
pub struct Pattern(pub Symbol, pub Vec<Symbol>);

#[derive(Debug, Clone)]
pub struct MatchCase(pub Pattern, pub Term);

#[derive(Debug, Clone)]
pub enum Term {
    Const(SpecConstant),
    Base(QualifiedIdentifier, Vec<Term>),
    Let(Vec<VarBinding>, Box<Term>),
    ForAll(Vec<SortedVar>, Box<Term>),
    Exists(Vec<SortedVar>, Box<Term>),
    //Annotation(Box<Term>, Vec<Attribute>),
}

impl<T: Into<SpecConstant>> From<T> for Term {
    fn from(value: T) -> Self {
        Self::Const(value.into())
    }
}

impl From<Term> for SExpr {
    fn from(term: Term) -> Self {
        match term {
            Term::Const(con) => con.into(),
            Term::Base(qid, terms) => {
                if terms.is_empty() {
                    qid.into()
                } else {
                    let qid_sexpr: SExpr = qid.into();

                    SExpr::from_iter(Some(qid_sexpr).into_iter().chain(
                        terms.into_iter().map(|term| term.into()),
                        //.flat_map(|term| vec![term.into(), SExpr::HintNewline]),
                    ))
                }
            }
            Term::Let(bindings, term) => SExpr::SExpr(vec![
                ReservedWord::Let.into(),
                SExpr::from_iter(bindings),
                (*term).into(),
            ]),
            Term::ForAll(vars, term) => SExpr::SExpr(vec![
                ReservedWord::Forall.into(),
                SExpr::from_iter(vars),
                (*term).into(),
            ]),
            Term::Exists(vars, term) => SExpr::SExpr(vec![
                ReservedWord::Exists.into(),
                SExpr::from_iter(vars),
                (*term).into(),
            ]),
            // Term::Annotation(term, attrs) => SExpr::from_iter(vec![
            //     ReservedWord::Bang.into(),
            //     (*term).into(),
            // ]).chain(attrs.into_iter()),
        }
    }
}

impl From<&str> for Term {
    fn from(value: &str) -> Self {
        Term::Base(
            QualifiedIdentifier(Identifier(Symbol::parse(value).unwrap(), vec![]), None),
            vec![],
        )
    }
}

impl From<Symbol> for Term {
    fn from(value: Symbol) -> Self {
        Term::Base(QualifiedIdentifier(Identifier(value, vec![]), None), vec![])
    }
}
