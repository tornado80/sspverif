use crate::types::Type;

use super::exprs::SmtExpr;

pub trait SmtSort: Into<SmtExpr> {}

impl SmtSort for Type {}

pub trait SmtPlainSort: SmtSort {
    fn sort_name(&self) -> String;
}

#[macro_export]
macro_rules! impl_Into_for_PlainSort {
    ($a:lifetime, $plain_sort:ty) => {
        impl<$a> Into<$crate::writers::smt::exprs::SmtExpr> for $plain_sort {
            fn into(self) -> $crate::writers::smt::exprs::SmtExpr {
                self.sort_name().into()
            }
        }
        impl<$a> $crate::writers::smt::sorts::SmtSort for $plain_sort {}
    };
    ($plain_sort:ty) => {
        impl Into<$crate::writers::smt::exprs::SmtExpr> for $plain_sort {
            fn into(self) -> $crate::writers::smt::exprs::SmtExpr {
                self.sort_name().into()
            }
        }
        impl<$a> $crate::writers::smt::sorts::SmtSort for $plain_sort {}
    };
}

pub struct Array<K, V>
where
    K: Into<SmtExpr>,
    V: Into<SmtExpr>,
{
    pub key: K,
    pub value: V,
}

impl<K, V> From<Array<K, V>> for SmtExpr
where
    K: Into<SmtExpr>,
    V: Into<SmtExpr>,
{
    fn from(t: Array<K, V>) -> Self {
        let Array { key, value } = t;
        ("Array", key, value).into()
    }
}
