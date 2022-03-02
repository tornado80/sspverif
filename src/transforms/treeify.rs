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
                oracle.code = treeify(&oracle.code);
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

fn treeify(cb: &CodeBlock) -> CodeBlock {
    let mut before: Vec<Statement> = vec![];
    let mut after: Vec<Statement> = vec![];
    let mut found = false;

    let mut ifcode = None;
    let mut elsecode = None;
    let mut cond = None;

    for elem in &cb.0 {
        match &*elem {
            Statement::IfThenElse(cond_, CodeBlock(ifcode_), CodeBlock(elsecode_)) => {
                if !found {
                    ifcode = Some(ifcode_.clone());
                    elsecode = Some(elsecode_.clone());
                    cond = Some(cond_);
                    found = true;
                } else {
                    after.push(elem.clone());
                }
            }
            _ => {
                if !found {
                    before.push(elem.clone());
                } else {
                    after.push(elem.clone());
                }
            }
        }
    }

    if found {
        let mut newifcode = ifcode.unwrap();
        newifcode.append(&mut after.clone());
        let mut newelsecode = elsecode.unwrap();
        newelsecode.append(&mut after.clone());
        before.push(Statement::IfThenElse(
            cond.unwrap().clone(),
            treeify(&CodeBlock(newifcode)),
            treeify(&CodeBlock(newelsecode)),
        ));
        CodeBlock(before)
    } else {
        cb.clone()
    }
}
