use super::errors::*;
use super::oracledef::typecheck_odef;
use super::scope::Scope;

use crate::identifier::Identifier;
use crate::package::Package;

pub fn typecheck_pkg(pkg: &Package, scope: &mut Scope) -> Result<(), TypeCheckError> {
    let Package {
        params,
        state,
        oracles,
    } = pkg;

    scope.enter();
    for (name, ntipe) in params {
        scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
    }
    for (name, ntipe) in state {
        scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
    }

    for oracle in oracles {
        typecheck_odef(oracle, scope)?;
    }

    scope.leave();
    Ok(())
}
