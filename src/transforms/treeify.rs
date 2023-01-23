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

#[cfg(test)]
mod treeify_fn_test {
    use crate::expressions::Expression;
    use crate::identifier::Identifier;
    use crate::statement::{CodeBlock, Statement};

    use super::treeify;

    #[test]
    fn nothing_happens_without_if() {
        let cb = CodeBlock(vec![Statement::Return(None)]);

        assert_eq!(cb.clone(), treeify(&cb));
    }
    #[test]
    fn treeify_one_sided_if_depth_1() {
        let x = Identifier::new_scalar("x");
        let y = Identifier::new_scalar("y");
        let before = CodeBlock(vec![
            Statement::IfThenElse(
                y.to_expression(),
                CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral("4".to_string()),
                )]),
                CodeBlock(vec![]),
            ),
            Statement::Return(Some(x.to_expression())),
        ]);

        let after = CodeBlock(vec![Statement::IfThenElse(
            y.to_expression(),
            CodeBlock(vec![
                Statement::Assign(x.clone(), None, Expression::IntegerLiteral("4".to_string())),
                Statement::Return(Some(x.to_expression())),
            ]),
            CodeBlock(vec![Statement::Return(Some(x.to_expression()))]),
        )]);

        assert_eq!(after.clone(), treeify(&before));

        // make sure it's idempotent
        assert_eq!(after.clone(), treeify(&after));
    }

    #[test]
    fn treeify_one_sided_if_depth_2() {
        let x = Identifier::new_scalar("x");
        let y = Identifier::new_scalar("y");
        let z = Identifier::new_scalar("z");
        let before = CodeBlock(vec![
            Statement::IfThenElse(
                y.to_expression(),
                CodeBlock(vec![Statement::IfThenElse(
                    z.to_expression(),
                    CodeBlock(vec![Statement::Assign(
                        x.clone(),
                        None,
                        Expression::IntegerLiteral("42".to_string()),
                    )]),
                    CodeBlock(vec![]),
                )]),
                CodeBlock(vec![]),
            ),
            Statement::Return(Some(x.to_expression())),
        ]);

        let after = CodeBlock(vec![Statement::IfThenElse(
            y.to_expression(),
            CodeBlock(vec![Statement::IfThenElse(
                z.to_expression(),
                CodeBlock(vec![
                    Statement::Assign(
                        x.clone(),
                        None,
                        Expression::IntegerLiteral("42".to_string()),
                    ),
                    Statement::Return(Some(x.to_expression())),
                ]),
                CodeBlock(vec![Statement::Return(Some(x.to_expression()))]),
            )]),
            CodeBlock(vec![Statement::Return(Some(x.to_expression()))]),
        )]);

        assert_eq!(after.clone(), treeify(&before));

        // make sure it's idempotent
        assert_eq!(after.clone(), treeify(&after));
    }

    #[test]
    fn treeify_subsequent_ifs() {
        let x = Identifier::new_scalar("x");
        let y = Identifier::new_scalar("y");
        let z = Identifier::new_scalar("z");
        let before = CodeBlock(vec![
            Statement::IfThenElse(
                y.to_expression(),
                CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral("1".to_string()),
                )]),
                CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral("2".to_string()),
                )]),
            ),
            Statement::IfThenElse(
                z.to_expression(),
                CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral("3".to_string()),
                )]),
                CodeBlock(vec![Statement::Assign(
                    x.clone(),
                    None,
                    Expression::IntegerLiteral("4".to_string()),
                )]),
            ),
            Statement::Return(Some(x.to_expression())),
        ]);

        let after = CodeBlock(vec![Statement::IfThenElse(
            y.to_expression(),
            CodeBlock(vec![
                Statement::Assign(x.clone(), None, Expression::IntegerLiteral("1".to_string())),
                Statement::IfThenElse(
                    z.to_expression(),
                    CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral("3".to_string()),
                        ),
                        Statement::Return(Some(x.to_expression())),
                    ]),
                    CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral("4".to_string()),
                        ),
                        Statement::Return(Some(x.to_expression())),
                    ]),
                ),
            ]),
            CodeBlock(vec![
                Statement::Assign(x.clone(), None, Expression::IntegerLiteral("2".to_string())),
                Statement::IfThenElse(
                    z.to_expression(),
                    CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral("3".to_string()),
                        ),
                        Statement::Return(Some(x.to_expression())),
                    ]),
                    CodeBlock(vec![
                        Statement::Assign(
                            x.clone(),
                            None,
                            Expression::IntegerLiteral("4".to_string()),
                        ),
                        Statement::Return(Some(x.to_expression())),
                    ]),
                ),
            ]),
        )]);

        assert_eq!(after.clone(), treeify(&before));

        // make sure it's idempotent
        assert_eq!(after.clone(), treeify(&after));
    }
}

#[cfg(test)]
mod treeify_transform_test {
    use super::super::Transformation as TTransformation;
    use super::Transformation;

    use crate::expressions::Expression;
    use crate::package::{Composition, Edge, Export};
    use crate::testdata::{keypkg, modprf};
    use std::collections::HashMap;

    #[test]
    fn runs_for_all_packages_and_oracles() {
        let mut params = HashMap::new();
        params.insert(
            "n".to_string(),
            Expression::IntegerLiteral("256".to_string()),
        );

        let key_real_pkg = keypkg::key_pkg(&params);
        let mod_prf_real_pkg = modprf::mod_prf(&params);

        let mod_prf_game = Composition {
            pkgs: vec![key_real_pkg.clone(), mod_prf_real_pkg.clone()],
            edges: vec![Edge(1, 0, key_real_pkg.pkg.clone().oracles[1].sig.clone())],
            exports: vec![
                Export(0, key_real_pkg.pkg.clone().oracles[0].sig.clone()),
                Export(1, mod_prf_real_pkg.pkg.clone().oracles[0].sig.clone()),
            ],
            name: "real".to_string(),
            consts: vec![],
        };

        let transform = Transformation(&mod_prf_game);
        let (tranformed, _) = transform.transform().expect("error when transforming");

        assert_eq!(
            mod_prf_game.pkgs[0].pkg.oracles[0],
            tranformed.pkgs[0].pkg.oracles[0]
        );
        assert_ne!(
            mod_prf_game.pkgs[0].pkg.oracles[1],
            tranformed.pkgs[0].pkg.oracles[1]
        );
        assert_eq!(
            mod_prf_game.pkgs[1].pkg.oracles[0],
            tranformed.pkgs[1].pkg.oracles[0]
        );
    }
}
