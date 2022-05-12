use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};

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
                    let mut ctr = 1u32;
                    newinst.pkg.oracles[i].code = unwrapify(&oracle.code, &mut ctr)?;
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

fn replace_unwrap(expr: &Expression, ctr: &mut u32) -> (Expression, Vec<(Expression, String)>) {
    let ((local_ctr, result), newexpr) =
        expr.mapfold((*ctr, Vec::new()), |(map_ctr, mut ac), e| {
            if let Expression::Unwrap(_) = e {
                let varname: String = format!("unwrap-{}", map_ctr);
                ac.push((e, varname.clone()));
                (
                    (map_ctr + 1, ac),
                    Identifier::Scalar(varname).to_expression(),
                )
            } else {
                ((map_ctr, ac), e)
            }
        });
    *ctr = local_ctr;
    (newexpr, result)
}

fn create_unwrap_stmts(unwraps: Vec<(Expression, String)>) -> Vec<Statement> {
    unwraps
        .iter()
        .map(|(expr, varname)| Statement::Assign(Identifier::Scalar(varname.clone()), expr.clone()))
        .collect()
}

/*
[0] foo <- bar(unwrap(x))

replace_unwrap([0])
 -> x, unwrap-x-12

[0] wurde zu foo <- bar(unwrap-12-x)
*/

pub fn unwrapify(cb: &CodeBlock, ctr: &mut u32) -> Result<CodeBlock, Error> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::Abort | Statement::Sample(_, None, _) | Statement::Return(None) => {
                newcode.push(stmt);
            }
            Statement::Return(Some(ref expr)) => {
                let (newexpr, unwraps) = replace_unwrap(&expr, ctr);
                if unwraps.len() == 0 {
                    newcode.push(stmt);
                } else {
                    newcode.extend(create_unwrap_stmts(unwraps));
                    newcode.push(Statement::Return(Some(newexpr)));
                }
            }
            Statement::Assign(ref id, ref expr) => {
                // special case for direct unwraps
                let (newexpr, unwraps) = replace_unwrap(expr, ctr);
                if unwraps.len() == 0 {
                    newcode.push(stmt);
                } else {
                    newcode.extend(create_unwrap_stmts(unwraps));
                    newcode.push(Statement::Assign(id.clone(), newexpr));
                }
            }
            Statement::TableAssign(_, _, _) => {
                panic!("Im too lazy")
            }
            Statement::IfThenElse(expr, ifcode, elsecode) => {
                let (newexpr, unwraps) = replace_unwrap(&expr, ctr);
                newcode.extend(create_unwrap_stmts(unwraps));
                newcode.push(Statement::IfThenElse(
                    newexpr,
                    unwrapify(&ifcode, ctr)?,
                    unwrapify(&elsecode, ctr)?,
                ));
            }
            Statement::Sample(ref id, Some(ref expr), ref tipe) => {
                let (newexpr, unwraps) = replace_unwrap(&expr, ctr);
                if unwraps.len() == 0 {
                    newcode.push(stmt);
                } else {
                    newcode.extend(create_unwrap_stmts(unwraps));
                    newcode.push(Statement::Sample(id.clone(), Some(newexpr), tipe.clone()));
                }
            }
            Statement::InvokeOracle {
                id,
                opt_idx,
                name,
                args,
                target_inst_name,
            } => {
                let opt_idx = opt_idx.map(|expr| {
                    let (newexpr, unwraps) = replace_unwrap(&expr, ctr);
                    newcode.extend(create_unwrap_stmts(unwraps));
                    newexpr
                });
                let args = args
                    .iter()
                    .map(|expr| {
                        let (newexpr, unwraps) = replace_unwrap(&expr, ctr);
                        newcode.extend(create_unwrap_stmts(unwraps));
                        newexpr
                    })
                    .collect();
                newcode.push(Statement::InvokeOracle {
                    id,
                    opt_idx,
                    name,
                    args,
                    target_inst_name,
                });
            }
        }
    }
    Ok(CodeBlock(newcode))
}

#[cfg(test)]
mod test {
    use super::unwrapify;
    use crate::block;
    use crate::expressions::Expression;
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, Statement};

    #[test]
    fn unwrap_assign() {
        let code = block! {
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Unwrap(Box::new(Identifier::new_scalar("e").to_expression())))
        };
        let newcode = block! {
            Statement::Assign(Identifier::new_scalar("unwrap-1"),
                              Expression::Unwrap(Box::new(Identifier::new_scalar("e").to_expression()))),
            Statement::Assign(Identifier::new_scalar("d"), Identifier::new_scalar("unwrap-1").to_expression())
        };
        let mut ctr = 1u32;
        assert_eq!(newcode, unwrapify(&code, &mut ctr).unwrap());
    }

    #[test]
    fn unwrap_two_statements() {
        let code = block! {
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Unwrap(Box::new(Identifier::new_scalar("e").to_expression()))),
            Statement::Assign(Identifier::new_scalar("f"),
                              Expression::Unwrap(Box::new(Identifier::new_scalar("g").to_expression())))
        };
        let newcode = block! {
            Statement::Assign(Identifier::new_scalar("unwrap-1"),
                              Expression::Unwrap(Box::new(Identifier::new_scalar("e").to_expression()))),
            Statement::Assign(Identifier::new_scalar("d"), Identifier::new_scalar("unwrap-1").to_expression()),
            Statement::Assign(Identifier::new_scalar("unwrap-2"),
                              Expression::Unwrap(Box::new(Identifier::new_scalar("g").to_expression()))),
            Statement::Assign(Identifier::new_scalar("f"), Identifier::new_scalar("unwrap-2").to_expression())
        };
        let mut ctr = 1u32;
        assert_eq!(newcode, unwrapify(&code, &mut ctr).unwrap());
    }

    #[test]
    fn netsted_statements() {
        let code = block! {
            Statement::Assign(Identifier::new_scalar("d"),
                              Expression::Unwrap(Box::new(Expression::Unwrap(Box::new(Identifier::new_scalar("e").to_expression())))))
        };
        let newcode = block! {
                    Statement::Assign(Identifier::new_scalar("unwrap-1"),
                                      Expression::Unwrap(Box::new(Identifier::new_scalar("e").to_expression()))),
                    Statement::Assign(Identifier::new_scalar("unwrap-2"),
                                      Expression::Unwrap(Box::new(Identifier::new_scalar("unwrap-1").to_expression()))),
                    Statement::Assign(Identifier::new_scalar("d"), Identifier::new_scalar("unwrap-2").to_expression())


        };
        let mut ctr = 1u32;
        assert_eq!(newcode, unwrapify(&code, &mut ctr).unwrap());
    }
}
