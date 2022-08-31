use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

#[derive(Debug, Clone)]
pub struct Error(pub String);

pub struct Transformation<'a>(pub &'a Composition);

impl<'a> super::Transformation for Transformation<'a> {
    type Err = Error;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Error> {
        let insts: Result<Vec<_>, _> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = tableinitialize(&oracle.code, &[])?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            (),
        ))
    }
}

pub fn tableinitialize(cb: &CodeBlock, initialized: &[String]) -> Result<CodeBlock, Error> {
    let mut newcode = Vec::new();
    let new_initialized = initialized.clone();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                newcode.push(Statement::IfThenElse(
                    expr,
                    tableinitialize(&ifcode, &new_initialized)?,
                    tableinitialize(&elsecode, &new_initialized)?,
                ));
            }
            Statement::Assign(Identifier::Local(ref id), Some(ref idxexpr), ref expr) => {
                let indextype = match idxexpr {
                    Expression::Typed(t, _) => t,
                    _ => unreachable!("all expressions are typed at this point!"),
                };
                let valuetype = match expr {
                    Expression::Typed(Type::Maybe(t), _) => &**t,
                    _ => unreachable!("all expressions are typed at this point, and the value needs to be a maybe type!"),
                };
                let tabletype =
                    Type::Table(Box::new(indextype.clone()), Box::new(valuetype.clone()));

                if !new_initialized.contains(&id) {
                    newcode.push(Statement::Assign(
                        Identifier::Local(id.clone()),
                        None,
                        Expression::Typed(tabletype, Box::new(Expression::EmptyTable)),
                    ))
                }
                newcode.push(stmt);
            }
            Statement::Sample(Identifier::Local(ref id), Some(ref idxexpr), _, ref tipe) => {
                let indextype = match idxexpr {
                    Expression::Typed(t, _) => t,
                    _ => unreachable!("all expressions are typed at this point!"),
                };
                let tabletype = Type::Table(Box::new(indextype.clone()), Box::new(tipe.clone()));

                if !new_initialized.contains(&id) {
                    newcode.push(Statement::Assign(
                        Identifier::Local(id.clone()),
                        None,
                        Expression::Typed(tabletype, Box::new(Expression::EmptyTable)),
                    ))
                }
                newcode.push(stmt);
            }
            Statement::InvokeOracle {
                id: Identifier::Local(ref id),
                opt_idx: Some(ref idxexpr),
                name: _,
                args: _,
                target_inst_name: _,
                tipe: ref opt_tipe,
            } => {
                let indextype = match idxexpr {
                    Expression::Typed(t, _) => t,
                    _ => unreachable!("all expressions are typed at this point!"),
                };
                let valuetype = match opt_tipe {
                    Some(t) => t,
                    _ => unreachable!("all expressions are typed at this point!"),
                };
                let tabletype =
                    Type::Table(Box::new(indextype.clone()), Box::new(valuetype.clone()));

                if !new_initialized.contains(&id) {
                    newcode.push(Statement::Assign(
                        Identifier::Local(id.clone()),
                        None,
                        Expression::Typed(tabletype, Box::new(Expression::EmptyTable)),
                    ))
                }
                newcode.push(stmt);
            }
            _ => {
                newcode.push(stmt);
            }
        }
    }
    Ok(CodeBlock(newcode))
}

#[cfg(test)]
mod test {}
