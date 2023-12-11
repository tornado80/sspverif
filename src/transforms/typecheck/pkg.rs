use super::errors::TypeCheckError;
use super::oracledef::typecheck_odef;
use super::scope::Scope;

use crate::identifier::Identifier;
use crate::package::{OracleDef, OracleSig, Package};

pub fn typecheck_pkg(pkg: &Package, scope: &mut Scope) -> Result<Package, TypeCheckError> {
    let Package {
        params,
        state,
        oracles,
        imports,
        ..
    } = pkg;

    scope.enter();

    // TODO: should the declare calls here also get the position, so they can include it
    //       in the potentially returned error?
    for (name, ntipe, file_pos) in params {
        scope
            .declare(Identifier::new_scalar(name), ntipe.clone())
            .map_err(|err| TypeCheckError::new_scope_error(err, file_pos))?;
    }
    for (name, ntipe, file_pos) in state {
        scope
            .declare(Identifier::new_scalar(name), ntipe.clone())
            .map_err(|err| TypeCheckError::new_scope_error(err, file_pos))?;
    }

    for (
        OracleSig {
            name, args, tipe, ..
        },
        file_pos,
    ) in imports
    {
        let arg_types = args.iter().map(|(_, tipe)| tipe).cloned().collect();
        let id = Identifier::Scalar(name.clone());
        scope
            .declare_oracle(id, arg_types, tipe.clone())
            .map_err(|err| TypeCheckError::new_scope_error(err, file_pos))?;
    }

    let mut typed_oracles = vec![];

    for oracle in oracles {
        // kept around so we don't have to get it out when we want to debug it next time
        let OracleDef {
            sig: OracleSig {
                name: _oracle_name, ..
            },
            ..
        } = &oracle;
        //eprintln!("DEBUG typecheck_pkg: checking {pkg_name}.{oracle_name}");
        typed_oracles.push(typecheck_odef(oracle, scope)?);
    }

    scope.leave();
    Ok(Package {
        oracles: typed_oracles,
        ..pkg.clone()
    })
}
