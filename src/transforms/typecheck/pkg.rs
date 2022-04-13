use super::errors::TypeCheckError;
use super::oracledef::typecheck_odef;
use super::scope::Scope;

use crate::identifier::Identifier;
use crate::package::Package;

pub fn typecheck_pkg(pkg: &Package, scope: &mut Scope) -> Result<Package, TypeCheckError> {
    let Package {
        params,
        state,
        oracles,
        ..
    } = pkg;

    scope.enter();
    for (name, ntipe) in params {
        scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
    }
    for (name, ntipe) in state {
        scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
    }

    let mut typed_oracles = vec![];

    for oracle in oracles {
        typed_oracles.push(typecheck_odef(oracle, scope)?);
    }

    scope.leave();
    Ok(Package {
        oracles: typed_oracles,
        ..pkg.clone()
    })
}
