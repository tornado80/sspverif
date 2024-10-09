use std::borrow::Borrow;

use crate::{expressions::Expression, writers::smt::exprs::SmtExpr};

pub fn only_expression<'a, T: 'a, I: IntoIterator<Item = &'a (T, Expression)>>(
    iter: I,
) -> impl Iterator<Item = &'a Expression> {
    iter.into_iter().map(|(_, expr)| expr)
}

pub fn encode_params<'a, I>(params_iter: I) -> String
where
    I: IntoIterator<Item = &'a Expression>,
{
    encode_smt_exprs(
        params_iter
            .into_iter()
            .map(|expr: &Expression| -> SmtExpr { expr.clone().into() }),
    )
}

pub fn encode_smt_exprs<Ref: Borrow<SmtExpr>, Iter: IntoIterator<Item = Ref>>(
    exprs: Iter,
) -> String {
    let mut out = String::with_capacity(64);

    out.push_str("<$");
    let mut out = exprs.into_iter().fold(out, |mut acc, expr| {
        acc.push_str(&encode_smt_expr(expr.borrow()));
        acc
    });
    out.push_str("$>");

    out
}

fn encode_smt_expr(expr: &SmtExpr) -> String {
    match expr {
        SmtExpr::Comment(_) => "".to_string(),
        SmtExpr::Atom(atom) => format!("<!{atom}!>"),
        SmtExpr::List(exprs) => encode_smt_exprs(exprs),
    }
}
