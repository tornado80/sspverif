use super::errors::*;
use super::pkg::typecheck_pkg;
use super::scope::Scope;

use crate::package::Composition;

use crate::identifier::Identifier;
use crate::types::Type;

pub fn typecheck_comp(comp: &Composition, scope: &mut Scope) -> Result<(), TypeCheckError> {
    let Composition {
        pkgs,
        edges,
        exports,
        ..
    } = comp;

    // 1. check signature exists in edge destination
    for (_, to, sig_) in edges {
        let mut found = false;
        for sig in pkgs[*to].get_oracle_sigs() {
            if sig == sig_.clone() {
                found = true
            }
        }
        if !found {
            return Err(TypeCheckError::TypeCheck(format!(
                "couldn't find signature for {:?} in package {:?} with id {:}",
                sig_, pkgs[*to], to
            )));
        }
    }

    // 2. check exports exists
    for (id, sig) in exports {
        if !pkgs[*id].get_oracle_sigs().contains(sig) {
            return Err(TypeCheckError::TypeCheck(format!(
                "signature {:?} is not in package {:?} with index {:}",
                sig,
                pkgs[*id].clone(),
                id
            )));
        }
    }

    // 3. check all package instances
    for (id, pkg) in pkgs.clone().into_iter().enumerate() {
        scope.enter();
        for (from, _, sig) in edges {
            if *from == id {
                scope.declare(
                    Identifier::new_scalar(sig.name.as_str()),
                    Type::Oracle(
                        sig.args.clone().into_iter().map(|(_, tipe)| tipe).collect(),
                        Box::new(sig.tipe.clone()),
                    ),
                )?;
            }
        }
        let result = typecheck_pkg(&pkg.pkg, scope)?;
        scope.leave();

        result
    }

    Ok(())
}
