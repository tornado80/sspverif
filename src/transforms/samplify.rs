use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};


#[derive(Debug, Clone)]
pub struct Error(pub String);

pub struct Transformation<'a>(pub &'a Composition);

impl<'a> super::Transformation for Transformation<'a> {
    type Err = Error;
    type Aux = u32;

    fn transform(&self) -> Result<(Composition, u32), Error> {
        let mut ctr = 1u32;
        let insts: Result<Vec<_>, _> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = samplify(&oracle.code, &mut ctr)?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            ctr,
        ))
    }
}

pub fn samplify(cb: &CodeBlock, ctr: &mut u32) -> Result<CodeBlock, Error> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                newcode.push(Statement::IfThenElse(
                    expr,
                    samplify(&ifcode, ctr)?,
                    samplify(&elsecode, ctr)?,
                ));
            },
            Statement::Sample(id, expr, None, tipe) => {
                newcode.push(Statement::Sample(id.clone(), expr, Some(*ctr), tipe.clone()));
                *ctr = *ctr+1;
            },
            _ => newcode.push(stmt)
        }
    }
    Ok(CodeBlock(newcode))
}
