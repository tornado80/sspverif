use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

use std::collections::HashMap;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Package {
    pub params: Vec<(String, Type)>,
    pub state: Vec<(String, Type)>,
    pub oracles: Vec<OracleDef>,
}

impl Package {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageInstance {
    pub params: HashMap<String, String>,
    pub pkg: Package,
    pub name: String,
}

impl PackageInstance {
    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        self.pkg
            .oracles
            .clone()
            .into_iter()
            .map(|d| d.sig)
            .collect()
    }

    fn var_specify_helper(&self, block: CodeBlock, comp_name: &str) -> CodeBlock {
        let PackageInstance {
            name,
            pkg: Package { state, params, .. },
            ..
        } = self;

        let fixup = |expr| match expr {
            Expression::Identifier(Identifier::Scalar(id)) => {
                if state.clone().iter().any(|(id_, _)| id == *id_) {
                    Expression::Identifier(Identifier::State {
                        name: id,
                        pkgname: name.clone(),
                        compname: comp_name.into(),
                    })
                } else if params.clone().iter().any(|(id_, _)| id == *id_) {
                    Expression::Identifier(Identifier::Params {
                        name: id,
                        pkgname: name.clone(),
                        compname: comp_name.into(),
                    })
                } else {
                    Expression::Identifier(Identifier::Local(id))
                }
            }
            _ => expr,
        };
        CodeBlock(
            block
                .0
                .iter()
                .map(|stmt| match stmt {
                    Statement::Abort => Statement::Abort,
                    Statement::Return(None) => Statement::Return(None),
                    Statement::Return(Some(expr)) => Statement::Return(Some(expr.map(fixup))),
                    Statement::Assign(id, expr) => {
                        if let Expression::Identifier(id) = fixup(id.to_expression()) {
                            Statement::Assign(id, expr.map(fixup))
                        } else {
                            unreachable!()
                        }
                    }
                    Statement::IfThenElse(expr, ifcode, elsecode) => Statement::IfThenElse(
                        expr.map(fixup),
                        self.var_specify_helper(ifcode.clone(), comp_name),
                        self.var_specify_helper(elsecode.clone(), comp_name),
                    ),
                    _ => panic!("not implemented"),
                })
                .collect(),
        )
    }

    pub fn var_specify(&self, comp_name: &str) -> PackageInstance {
        PackageInstance {
            name: self.name.clone(),
            params: self.params.clone(),
            pkg: Package {
                params: self.pkg.params.clone(),
                state: self.pkg.state.clone(),
                oracles: self
                    .pkg
                    .oracles
                    .iter()
                    .map(|def| OracleDef {
                        sig: def.sig.clone(),
                        code: self.var_specify_helper(def.code.clone(), comp_name),
                    })
                    .collect(),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Composition {
    pub pkgs: Vec<PackageInstance>,
    pub edges: Vec<(usize, usize, OracleSig)>, // (from, to, oraclesig)
    // TODO: how do we deal with the case where we have
    // e.g. multiple key packages that we Set into?
    // Idea: Add a name to this tuple that is used by
    // the invoking package
    // contemplation: globally unique oracle identifiers vs
    // multiple shades of local uniqueness
    pub exports: Vec<(usize, OracleSig)>,
    pub name: String,
}

impl Composition {
    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        self.exports.iter().map(|(_, sig)| sig.clone()).collect()
    }

    fn pkg_map<F>(&self, f: F) -> Composition
    where
        F: Fn(&PackageInstance) -> PackageInstance,
    {
        Composition {
            pkgs: self.pkgs.iter().map(f).collect(),
            edges: self.edges.clone(),
            exports: self.exports.clone(),
            name: self.name.clone(),
        }
    }

    pub fn lowlevelify_oracleinvocs(&self) -> Self {
        let pkgs = self
            .pkgs
            .iter()
            .enumerate()
            .map(|(pos, inst)| {
                let mut table = HashMap::<String, String>::new();
                let relevant = self.edges.iter().filter(|(from, _, _)| *from == pos);

                for (_, to, sig) in relevant {
                    let pkgname = self.pkgs[*to].name.clone();
                    table.insert(sig.name.clone(), pkgname);
                }

                let fixup = |expr| match expr {
                    Expression::OracleInvoc(name, args) => {
                        if let Some(pkgname) = table.get(&name) {
                            Expression::LowLevelOracleInvoc {
                                name,
                                pkgname: pkgname.clone(),
                                args,
                            }
                        } else {
                            panic!("couldn't find package for oracle {}", name);
                        }
                    }
                    _ => expr,
                };

                PackageInstance {
                    pkg: Package {
                        oracles: inst
                            .pkg
                            .oracles
                            .iter()
                            .map(|oracle| OracleDef {
                                code: CodeBlock(
                                    oracle
                                        .code
                                        .0
                                        .iter()
                                        .map(|stmt| match stmt {
                                            Statement::Assign(id, expr) => {
                                                Statement::Assign(id.clone(), expr.map(fixup))
                                            }
                                            _ => stmt.clone(),
                                        })
                                        .collect(),
                                ),
                                ..oracle.clone()
                            })
                            .collect(),
                        ..inst.pkg.clone()
                    },
                    ..inst.clone()
                }
            })
            .collect();

        Composition {
            pkgs,
            ..self.clone()
        }
    }
}
