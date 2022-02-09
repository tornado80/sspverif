use crate::expressions::Expression;
use crate::package::{Composition, OracleDef, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};

use std::collections::HashMap;

pub struct Transformation<'a>(pub &'a Composition);

impl<'a> super::Transformation for Transformation<'a> {
    type Err = ();
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), ()> {
        let pkgs = self
            .0
            .pkgs
            .iter()
            .enumerate()
            .map(|(pos, inst)| {
                let mut table = HashMap::<String, String>::new();
                let relevant = self.0.edges.iter().filter(|(from, _, _)| *from == pos);

                for (_, to, sig) in relevant {
                    let pkgname = self.0.pkgs[*to].name.clone();
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

        Ok((
            Composition {
                pkgs,
                ..self.0.clone()
            },
            (),
        ))
    }
}
