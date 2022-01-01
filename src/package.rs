use crate::types::Type;
use crate::identifier::Identifier;
use crate::scope::Scope;
use crate::errors::TypeCheckError;
use crate::statement::{TypedCodeBlock, CodeBlock};

use std::collections::HashMap;

/*
 * Next Steps:
 * - type check
 * - normalize/canonicalize nested composition
 * - usable constructors
 * - extract SMT-LIB
 * - pretty-print: both text-only and cryptocode
 */

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleDef {
    pub sig: OracleSig,
    pub code: CodeBlock,
}

impl OracleDef {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(),TypeCheckError> {
        let OracleDef{
            sig: OracleSig{name: _name, args, tipe},
            code
        } = self;
        scope.enter();
        for (name, ntipe) in args {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        };
        let code_block = TypedCodeBlock{
            expected_return_type: tipe.clone(),
            block: code.clone(),
        };

        code_block.typecheck(scope)?;
        scope.leave();
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Package {
    pub params: Vec<(String, Type)>,
    pub state: Vec<(String, Type)>,
    pub oracles: Vec<OracleDef>,
}


impl Package {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(),TypeCheckError> {
        let Package{ params, state, oracles } = self;
        //println!("scope in package typecheck: {:?}", scope);

        scope.enter();
        for (name, ntipe) in params {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        };
        for (name, ntipe) in state {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        };
        
        for oracle in oracles {
            oracle.typecheck(scope)?;
        }

        scope.leave();
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackageInstance {
    Atom {
        params: HashMap<String, String>,
        pkg: Package,
    },
    Composition {
        pkgs: Vec<PackageInstance>,
        edges: Vec<(usize, usize, OracleSig)>,  // (from, to, oraclesig)
                                                // TODO: how do we deal with the case where we have
                                                // e.g. multiple key packages that we Set into?
                                                // Idea: Add a name to this tuple that is used by
                                                // the invoking package
                                                // contemplation: globally unique oracle identifiers vs
                                                // multiple shades of local uniqueness
        exports: Vec<(usize, OracleSig)>,
    },
}

impl PackageInstance {
    pub fn get_pkg(&self) -> Package {
        match self {
            PackageInstance::Atom{pkg, ..} => pkg.clone(),
            _ => panic!(),
        }
    }

    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        match self {
            PackageInstance::Atom{pkg, ..} => {
                pkg.oracles.clone()
                    .into_iter()
                    .map(|d| d.sig)
                    .collect()
            },
            PackageInstance::Composition{exports, ..} => {
                exports.into_iter()
                    .map(|(_, sig)| sig.clone())
                    .collect()
            }
        }
    }

    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        match self {
            PackageInstance::Atom{pkg, .. } => {
                // TODO also check params
                pkg.typecheck(scope)
            },
            PackageInstance::Composition{pkgs, edges, exports} => {
                
                // 1. check signature exists in edge destination
                for (_, to, sig_) in edges {
                    let mut found = false;
                    for sig in pkgs[to.clone()].get_oracle_sigs() {
                        if sig == sig_.clone() {
                            found = true
                        }
                    }
                    if !found {
                        return Err(TypeCheckError::TypeCheck(format!("couldn't find signature for {:?} in package {:?} with id {:}", sig_, pkgs[to.clone()], to)))
                    }
                }

                // 2. check exports exists
                for (id, sig) in exports {
                    if !pkgs[id.clone()].get_oracle_sigs().contains(sig) {
                        return Err(TypeCheckError::TypeCheck(format!("signature {:?} is not in package {:?} with index {:}", sig, pkgs[id.clone()].clone(), id)))
                    }
                }

                // 3. check all package instances
                for (id, pkg) in pkgs.clone().into_iter().enumerate() {
                    scope.enter();
                    for (from, _, sig) in edges {
                        if from.clone() == id {
                            scope.declare(
                                Identifier::new_scalar(sig.name.as_str()),
                                Type::Oracle(
                                    sig.args.clone()
                                        .into_iter()
                                        .map(|(_, tipe)| Box::new(tipe)).collect(),
                                    Box::new(sig.tipe.clone()))
                            )?;
                        }
                    }
                    let result = pkg.typecheck(scope)?;
                    scope.leave();

                    result
                }


                Ok(())
            }
        }
    }
}
