use crate::{expressions::Expression, types::Type};
use sspverif_smtlib::{
    syntax::{
        s_expr::SpecConstant,
        term::{QualifiedIdentifier, Term},
        tokens::{Numeral, StringLiteral},
    },
    theories,
};

fn build_none(ty: Type) -> Term {
    Term::Base(
        QualifiedIdentifier("mk-none".into(), Some(Type::Maybe(Box::new(ty)).into())),
        vec![],
    )
}

fn build_some<T: Into<Term>>(term: T) -> Term {
    Term::Base("mk-some".into(), vec![term.into()])
}

impl From<Expression> for Term {
    fn from(expr: Expression) -> Self {
        match expr {
            Expression::EmptyTable(t) => {
                if let Type::Table(ty_idx, ty_val) = t {
                    let none = build_none(*ty_val.clone());
                    sspverif_smtlib::theories::array_ex::const_(*ty_idx, *ty_val, none)
                } else {
                    panic!("Empty table of type {:?}", t)
                }
            }
            Expression::Unwrap(inner) => {
                panic!(
                    "found an unwrap and don't knwo what to do with it -- {expr:?}",
                    expr = inner
                );
                //panic!("unwrap expressions need to be on the right hand side of an assign!");
                // TODO find a better way to present that error to the user.
            }
            Expression::Some(inner) => build_some(*inner),
            Expression::None(ty) => build_none(ty),

            Expression::StringLiteral(text) => StringLiteral::from(text).into_const().into(),
            Expression::IntegerLiteral(num) if num < 0 => {
                panic!("smt-lib does not support negative literals at the moment")
            }
            Expression::IntegerLiteral(num) => Numeral::from(num as u64).into_const().into(),
            Expression::BooleanLiteral(bit) => match bit.as_str() {
                "true" => theories::core::true_(),
                "false" => theories::core::false_(),
                _ => unreachable!(
                    "found a boolean literal '{bit}', the parse should have caught that"
                ),
            },

            Expression::Equals(exprs) => {
                theories::core::eq(exprs.into_iter().map(|expr| expr.into()).collect())
            }
            Expression::Identifier(_) => todo!(),
            Expression::TableAccess(_, _) => todo!(),
            Expression::Tuple(_) => todo!(),
            Expression::List(_) => todo!(),
            Expression::Set(_) => todo!(),
            Expression::FnCall(_, _) => todo!(),
            Expression::Not(_) => todo!(),
            Expression::Neg(_) => todo!(),
            Expression::Inv(_) => todo!(),
            Expression::Add(_, _) => todo!(),
            Expression::Sub(_, _) => todo!(),
            Expression::Mul(_, _) => todo!(),
            Expression::Div(_, _) => todo!(),
            Expression::Pow(_, _) => todo!(),
            Expression::Mod(_, _) => todo!(),
            Expression::And(_) => todo!(),
            Expression::Or(_) => todo!(),
            Expression::Xor(_) => todo!(),
            Expression::Sum(_) => todo!(),
            Expression::Prod(_) => todo!(),
            Expression::Any(_) => todo!(),
            Expression::All(_) => todo!(),
            Expression::Union(_) => todo!(),
            Expression::Cut(_) => todo!(),
            Expression::SetDiff(_) => todo!(),
            Expression::Concat(_) => todo!(),
            Expression::Bot => todo!(),
            Expression::Sample(_) => todo!(),
        }
    }
}
