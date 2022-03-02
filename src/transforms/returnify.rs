use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};

pub struct Transformation<'a>(pub &'a Composition);

impl<'a> super::Transformation for Transformation<'a> {
    type Err = ();
    type Aux = ();

    fn transform(&self) -> Result<(Composition, ()), ()> {
        let insts = self.0.pkgs.iter().map(|inst| {
            let mut newinst = inst.clone();
            newinst.pkg.oracles.iter_mut().for_each(|oracle| {
                oracle.code = returnify(&oracle.code);
            });
            newinst
        });
        Ok((
            Composition {
                pkgs: insts.collect(),
                ..self.0.clone()
            },
            (),
        ))
    }
}

pub fn returnify(cb: &CodeBlock) -> CodeBlock {
    match cb.0.last() {
        Some(Statement::IfThenElse(expr, ifcode, elsecode)) => {
            let mut retval = cb.0.clone();
            retval.pop();
            retval.push(Statement::IfThenElse(
                expr.clone(),
                returnify(ifcode),
                returnify(elsecode),
            ));
            CodeBlock(retval)
        }
        Some(Statement::Return(_)) | Some(Statement::Abort) => cb.clone(),
        _ => {
            let mut retval = cb.0.clone();
            retval.push(Statement::Return(None));
            CodeBlock(retval)
        }
    }
}
