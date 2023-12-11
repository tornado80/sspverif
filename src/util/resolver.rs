use crate::{
    expressions::Expression,
    package::{Composition, Package, PackageInstance},
    proof::Assumption,
};

pub trait Resolver<'a, T> {
    fn resolve(&self, name: &str) -> Option<&'a T>;
    fn resolve_index(&self, name: &str) -> Option<usize>;
}

pub trait Named {
    fn as_name(&self) -> &str;
}

pub struct SliceResolver<'a, T>(pub &'a [T]);

impl<'a, T: Named> Resolver<'a, T> for SliceResolver<'a, T> {
    fn resolve(&self, name: &str) -> Option<&'a T> {
        self.0.iter().find(|v| v.as_name() == name)
    }

    fn resolve_index(&self, name: &str) -> Option<usize> {
        self.0
            .iter()
            .enumerate()
            .find(|(_i, v)| v.as_name() == name)
            .map(|(i, _v)| i)
    }
}

impl<T> Named for (String, T) {
    fn as_name(&self) -> &str {
        &self.0
    }
}

impl<T, U> Named for (String, T, U) {
    fn as_name(&self) -> &str {
        &self.0
    }
}

#[macro_export]
macro_rules! impl_Named {
    ($tipe:ident) => {
        impl $crate::util::resolver::Named for $tipe {
            fn as_name(&self) -> &str {
                &self.name
            }
        }
    };
}

impl_Named!(Package);
impl_Named!(PackageInstance);
impl_Named!(Composition);
impl_Named!(Assumption);
//impl_Named!(Reduction);
//impl_Named!(Equivalence);
impl<'a> Resolver<'a, Expression> for SliceResolver<'a, (String, Expression)> {
    fn resolve(&self, name: &str) -> Option<&'a Expression> {
        self.0
            .iter()
            .find(|(item_name, _)| item_name == name)
            .map(|(_, v)| v)
    }

    fn resolve_index(&self, name: &str) -> Option<usize> {
        self.0
            .iter()
            .enumerate()
            .find(|(_i, (item_name, _))| item_name == name)
            .map(|(i, _)| i)
    }
}
