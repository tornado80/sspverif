use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, OracleDef, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};

pub struct Transformation(pub Composition);

impl super::Transformation for Transformation {
    type Err = ();
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), ()> {
        Ok((
            Composition {
                pkgs: self
                    .0
                    .pkgs
                    .iter()
                    .map(|inst| var_specify(inst, &self.0.name))
                    .collect(),
                ..self.0.clone()
            },
            (),
        ))
    }
}

fn var_specify_helper(inst: &PackageInstance, block: CodeBlock, comp_name: &str) -> CodeBlock {
    let PackageInstance {
        name,
        pkg: Package { state, params, .. },
        ..
    } = inst;

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
                    var_specify_helper(inst, ifcode.clone(), comp_name),
                    var_specify_helper(inst, elsecode.clone(), comp_name),
                ),
                _ => panic!("not implemented"),
            })
            .collect(),
    )
}

fn var_specify(inst: &PackageInstance, comp_name: &str) -> PackageInstance {
    PackageInstance {
        name: inst.name.clone(),
        params: inst.params.clone(),
        pkg: Package {
            params: inst.pkg.params.clone(),
            state: inst.pkg.state.clone(),
            oracles: inst
                .pkg
                .oracles
                .iter()
                .map(|def| OracleDef {
                    sig: def.sig.clone(),
                    code: var_specify_helper(inst, def.code.clone(), comp_name),
                })
                .collect(),
        },
    }
}
