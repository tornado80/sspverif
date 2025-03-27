use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
use std::io::{self, Write};

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::statement::{CodeBlock, IfThenElse, InvokeOracleStatement, Statement};
use crate::types::Type;

pub type Error = Infallible;

pub struct Transformation<'a>(pub &'a Composition);

impl super::Transformation for Transformation<'_> {
    type Err = Error;
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), Error> {
        let insts: Result<Vec<_>, Error> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                println!("transforming instance: {}", inst.name);
                //io::stdout().flush().unwrap();
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    println!("transforming oracle: {} with {} statements", oracle.sig.name, oracle.code.0.len());
                    //io::stdout().flush().unwrap();
                    newinst.pkg.oracles[i].code = tableinitialize(&oracle.code, HashSet::new())?;
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

pub fn tableinitialize(
    cb: &CodeBlock,
    mut new_initialized: HashSet<String>,
) -> Result<CodeBlock, Error> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(ite) => {
                //println!("tableinitialize if statement");
                newcode.push(Statement::IfThenElse(IfThenElse {
                    then_block: tableinitialize(&ite.then_block, new_initialized.clone())?,
                    else_block: tableinitialize(&ite.else_block, new_initialized.clone())?,

                    ..ite
                }));
            }
            Statement::Assign(
                Identifier::Generated(ref id, ref ty),
                Some(ref idxexpr),
                ref expr,
                ref file_pos,
            ) => {
                println!("tableinitialize: Assign {}", id);
                let indextype = idxexpr.get_type();
                let Type::Maybe(valuetype) = expr.get_type() else {
                    unreachable!("all expressions are expected to be typed at this point, and the value needs to be a maybe type! ({:?})", file_pos);
                };
                let tabletype = Type::Table(
                    Box::new(indextype.clone()),
                    Box::new(valuetype.as_ref().clone()),
                );

                debug_assert_eq!(*ty, tabletype);

                if !new_initialized.contains(id) {
                    new_initialized.insert(id.clone());
                    newcode.push(Statement::Assign(
                        Identifier::Generated(id.clone(), tabletype.clone()),
                        None,
                        Expression::EmptyTable(tabletype),
                        *file_pos,
                    ))
                }
                newcode.push(stmt);
            }
            Statement::Sample(
                Identifier::Generated(ref id, ref ty),
                Some(ref idxexpr),
                _,
                ref tipe,
                ref file_pos,
            ) => {
                println!("tableinitialize: Sample {}", id);
                let indextype = idxexpr.get_type();
                let tabletype = Type::Table(Box::new(indextype.clone()), Box::new(tipe.clone()));

                debug_assert_eq!(*ty, tabletype);

                if !new_initialized.contains(id) {
                    new_initialized.insert(id.clone());
                    newcode.push(Statement::Assign(
                        Identifier::Generated(id.clone(), tabletype.clone()),
                        None,
                        Expression::EmptyTable(tabletype),
                        *file_pos,
                    ))
                }
                newcode.push(stmt);
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id: Identifier::Generated(ref id, _),
                opt_idx: Some(ref idxexpr),
                tipe: ref opt_ret_tipe,
                ref file_pos,
                ..
            }) => {
                println!("tableinitialize: Invoke ORacle {}", id);
                let indextype = idxexpr.get_type();
                let valuetype = match opt_ret_tipe {
                    Some(t) => t.to_owned(),
                    _ => Type::Empty,
                };
                let tabletype =
                    Type::Table(Box::new(indextype.clone()), Box::new(valuetype.clone()));

                if !new_initialized.contains(id) {
                    new_initialized.insert(id.clone());
                    newcode.push(Statement::Assign(
                        Identifier::Generated(id.clone(), tabletype.clone()),
                        None,
                        Expression::EmptyTable(tabletype),
                        *file_pos,
                    ))
                }
                newcode.push(stmt);
            }
            _ => {
                //println!("tableinitialize other statement");
                newcode.push(stmt);
            }
        }
    }
    Ok(CodeBlock(newcode))
}

#[cfg(test)]
mod test {}
