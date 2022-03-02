use crate::expressions::Expression;
use crate::package::{Composition, OracleDef, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};

use std::collections::HashMap;

pub struct Transformation<'a>(pub &'a Composition);

fn transform_helper(table: &HashMap<String, String>, block: CodeBlock) -> CodeBlock {
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

    let out = block
        .0
        .iter()
        .map(|stmt| match stmt {
            Statement::Assign(id, expr) => Statement::Assign(id.clone(), expr.map(fixup)),
            Statement::IfThenElse(cond, ifcode, elsecode) => Statement::IfThenElse(
                cond.clone(),
                transform_helper(table, ifcode.clone()),
                transform_helper(table, elsecode.clone()),
            ),
            _ => stmt.clone(),
        })
        .collect();

    CodeBlock(out)
}

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

                PackageInstance {
                    pkg: Package {
                        oracles: inst
                            .pkg
                            .oracles
                            .iter()
                            .map(|oracle| OracleDef {
                                code: transform_helper(&table, oracle.code.clone()),
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
