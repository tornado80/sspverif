mod codeblock;
mod composition;
mod errors;
mod expression;
mod oracledef;
mod pkg;
mod scope;

use composition::typecheck_comp;
use errors::TypeCheckError;
pub use scope::Scope;

use crate::package::Composition;

pub struct Transform {
    scope: Scope,
    comp: Composition,
}

impl Transform {
    pub fn new(scope: Scope, comp: Composition) -> Transform {
        Transform { scope, comp }
    }

    pub fn new_with_empty_scope(comp: Composition) -> Transform {
        Transform::new(Scope::new(), comp)
    }

    pub fn scope(self) -> Scope {
        self.scope
    }
}

impl super::Transformation for Transform {
    type Err = TypeCheckError;
    type Aux = Scope;
    fn transform(&self) -> Result<(Composition, Scope), TypeCheckError> {
        let scope = self.scope.clone();
        let typed_comp = typecheck_comp(&self.comp, &mut scope.clone())?;

        Ok((typed_comp, scope))
    }
}
