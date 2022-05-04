use super::errors::TypeCheckError;
use super::pkg::typecheck_pkg;
use super::scope::Scope;

use crate::package::{Composition, PackageInstance};

use crate::identifier::Identifier;
use crate::types::Type;

use std::collections::{HashMap,HashSet};
use std::iter::FromIterator;

pub fn typecheck_comp(
    comp: &Composition,
    scope: &mut Scope,
) -> Result<Composition, TypeCheckError> {
    let Composition {
        pkgs,
        edges,
        exports,
        ..
    } = comp;

    // 1a. check signature exists in edge destination
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

    // 1b. check signature matches in package imports
    let mut declared_imports:HashMap<_,_> = pkgs.clone()
        .into_iter()
        .enumerate()
        .map(|(i, pkg)| (i, HashSet::from_iter(pkg.pkg.imports.into_iter())))
        .filter(|(_, v)| ! v.is_empty())
        .collect();
    let mut edge_imports = HashMap::new();

    for (from, _, sig_) in edges {
        edge_imports.entry(*from).or_insert(HashSet::new()).insert(sig_.clone());
    }
    if declared_imports != edge_imports {
        if declared_imports.keys().collect::<Vec<_>>() != edge_imports.keys().collect::<Vec<_>>() {
            panic!("Different set of keys with imports, declared: {:?} edges: {:?}", declared_imports.keys(), edge_imports.keys())
        }
        for (i, pkg) in pkgs.clone().iter().enumerate() {
            if !declared_imports.contains_key(&i) {
                continue;
            }
            if declared_imports[&i] != edge_imports[&i] {
                panic!("package: {} declared: {:?} edges: {:?}", pkg.name, declared_imports[&i], edge_imports[&i]);
            }
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

    let mut typed_pkgs = vec![];

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

        typed_pkgs.push(PackageInstance {
            pkg: result,
            ..pkg.clone()
        });
    }

    Ok(Composition {
        pkgs: typed_pkgs,
        ..comp.clone()
    })
}
