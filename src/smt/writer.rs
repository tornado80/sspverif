use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, OracleSig, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

use crate::smt::{
    exprs::{smt_to_string, SmtExpr, SmtIs, SmtIte, SmtLet, SspSmtVar},
    state_helpers::{SmtCompositionState, SmtPackageState},
};

pub struct CompositionSmtWriter<'a> {
    pub comp: &'a Composition,

    state_helpers: std::collections::HashMap<String, SmtPackageState<'a>>,
    comp_helper: SmtCompositionState<'a>,
}

impl<'a> CompositionSmtWriter<'a> {
    pub fn new(comp: &'a Composition) -> CompositionSmtWriter<'a> {
        let mut csw = CompositionSmtWriter {
            comp,
            state_helpers: Default::default(),
            comp_helper: SmtCompositionState::new(
                &comp.name,
                vec!["__randomness"]
                    .into_iter()
                    .chain(comp.pkgs.iter().map(|inst| &inst.name as &str))
                    .collect(),
            ),
        };

        csw.state_helpers.insert(
            "__randomness".into(),
            SmtPackageState::<'a>::new(
                &csw.comp.name,
                "__randomness",
                vec![("ctr".into(), Type::Integer)],
            ),
        );

        for inst in &csw.comp.pkgs {
            csw.state_helpers.insert(
                inst.name.clone(),
                SmtPackageState::new(&csw.comp.name, &inst.name, inst.pkg.state.clone()),
            );
        }

        csw
    }

    fn get_state_helper(&'a self, instname: &str) -> &'a SmtPackageState<'a> {
        if instname == "__randomness" {}

        self.state_helpers
            .get(instname)
            .unwrap_or_else(|| panic!("error looking up smt state helper: {}", instname))
    }

    /*
    Example:
    (declare-datatype State_right-pkey (
         (mk-state-right-pkey   (state-right-pkey-pk   (Array Int String))
                                (state-right-pkey-sk   (Array Int String))
                                (state-right-pkey-id   (Array String Int))
                                (state-right-pkey-ctr  Int)
                                (state-right-pkey-rand RandState))))

    (declare-datatype State_right (
        (mk-state-right         (state-right-pkey State_right-pkey)

        )
    ))

    */
    fn smt_pkg_state(&self, inst: &PackageInstance) -> SmtExpr {
        self.get_state_helper(&inst.name).smt_declare_datatype()
    }

    pub fn smt_composition_state(&self) -> Vec<SmtExpr> {
        // 1. each package in composition
        let mut states: Vec<SmtExpr> = self
            .comp
            .pkgs
            .clone()
            .iter()
            .map(|pkg| self.smt_pkg_state(pkg))
            .collect();

        states.push(self.comp_helper.smt_declare_datatype());

        states
    }

    /*
    example:
    (declare-datatype Return_key_get (
        (mk-return-key-get         (return-key-get-state State_key)
                                    (return-key_get-value Bits_n))
        (mk-abort-key-get)
    ))


    */

    fn smt_pkg_return(&self, inst: &PackageInstance) -> Vec<SmtExpr> {
        let mut smts = vec![];

        for osig in inst.get_oracle_sigs() {
            let mut constructor = vec![
                SmtExpr::Atom(format!(
                    "mk-return-{}-{}-{}",
                    self.comp.name, inst.name, osig.name
                )),
                SmtExpr::List(vec![
                    SmtExpr::Atom(format!(
                        "return-{}-{}-{}-state",
                        self.comp.name, inst.name, osig.name
                    )),
                    self.comp_helper.smt_sort(),
                ]),
            ];

            if Type::Empty != osig.tipe {
                constructor.push(SmtExpr::List(vec![
                    SmtExpr::Atom(format!(
                        "return-{}-{}-{}-value",
                        self.comp.name, inst.name, osig.name
                    )),
                    osig.tipe.into(),
                ]));
            }

            smts.push(SmtExpr::List(vec![
                SmtExpr::Atom("declare-datatype".to_string()),
                SmtExpr::Atom(format!(
                    "Return_{}_{}_{}",
                    self.comp.name, inst.name, osig.name
                )),
                SmtExpr::List(vec![
                    SmtExpr::List(constructor),
                    SmtExpr::List(vec![SmtExpr::Atom(format!(
                        "mk-abort-{}-{}-{}",
                        self.comp.name, inst.name, osig.name
                    ))]),
                ]),
            ]))
        }
        smts
    }

    pub fn smt_composition_return(&self) -> Vec<SmtExpr> {
        self.comp
            .pkgs
            .clone()
            .iter()
            .flat_map(|inst| self.smt_pkg_return(inst))
            .collect()
    }

    fn code_smt_helper(
        &self,
        block: CodeBlock,
        sig: &OracleSig,
        inst: &PackageInstance,
    ) -> SmtExpr {
        let PackageInstance { name: pkgname, .. } = inst;

        let mut result = None;
        for stmt in block.0.iter().rev() {
            result = Some(match stmt {
                Statement::IfThenElse(cond, ifcode, elsecode) => SmtIte {
                    cond: cond.clone(),
                    then: self.code_smt_helper(ifcode.clone(), sig, inst),
                    els: self.code_smt_helper(elsecode.clone(), sig, inst),
                }
                .into(),
                Statement::Return(None) => {
                    // (mk-return-{name} statevarname)
                    SmtExpr::List(vec![
                        SspSmtVar::OracleReturnConstructor {
                            compname: self.comp.name.clone(),
                            pkgname: pkgname.clone(),
                            oname: sig.name.clone(),
                        }
                        .into(),
                        SspSmtVar::GlobalState.into(),
                    ])
                }
                Statement::Return(Some(expr)) => {
                    // (mk-return-{name} statevarname expr)
                    self.comp_helper.smt_set(
                        &inst.name,
                        &SspSmtVar::SelfState.into(),
                        SmtExpr::List(vec![
                            SspSmtVar::OracleReturnConstructor {
                                compname: self.comp.name.clone(),
                                pkgname: pkgname.clone(),
                                oname: sig.name.clone(),
                            }
                            .into(),
                            SspSmtVar::GlobalState.into(),
                            expr.clone().into(),
                        ]),
                    )
                }
                Statement::Abort => {
                    // mk-abort-{name}
                    SspSmtVar::OracleAbort {
                        compname: self.comp.name.clone(),
                        pkgname: pkgname.clone(),
                        oname: sig.name.clone(),
                    }
                    .into()
                    //SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, sig.name))
                }
                // TODO actually use the type that we sample to know how far to advance the randomness tape
                Statement::Sample(ident, opt_idx, _sample_id, _tipe) => {
                    /*
                     *   1. get counter
                     *   2. assign ident
                     *   3. overwrite state
                     *   4. continue
                     *
                     * let
                     *   ident = sample(ctr)
                     *   __global = mk-compositionState ( mk-randomndess-state (ctr + 1) ... )
                     *
                     *
                     * ,
                     *   let (ident = rand(access(counter)) (
                     *       comp_helper.smt_set(counter, counter+1, body)
                     * ))
                     * )
                     *
                     */
                    let ctr = self.get_state_helper("__randomness").smt_access(
                        "ctr",
                        self.comp_helper
                            .smt_access("__randomness", SspSmtVar::GlobalState.into()),
                    );

                    let rand_val = SmtExpr::List(vec![
                        SmtExpr::Atom(format!("__sample-rand-{}", self.comp.name)),
                        ctr.clone(),
                    ]);

                    let new_val = if opt_idx.is_some() {
                        SmtExpr::List(vec![
                            SmtExpr::Atom("store".into()),
                            ident.to_expression().into(),
                            opt_idx.clone().unwrap().into(),
                            rand_val.clone(),
                        ])
                    } else {
                        rand_val
                    };

                    SmtLet {
                        bindings: vec![(ident.ident(), new_val)],
                        body: self.comp_helper.smt_set(
                            "__randomness",
                            &self.get_state_helper("__randomness").smt_set(
                                "ctr",
                                &SmtExpr::List(vec![
                                    SmtExpr::Atom("+".into()),
                                    SmtExpr::Atom("1".into()),
                                    ctr,
                                ]),
                            ),
                            result.unwrap(),
                        ),
                    }
                    .into()
                }
                Statement::Parse(idents, expr) => {
                    let bindings = idents
                        .iter()
                        .enumerate()
                        .map(|(i, ident)| {
                            let ident = if let Identifier::Local(ident) = ident {
                                ident
                            } else {
                                unreachable!()
                            };

                            (
                                ident.clone(),
                                SmtExpr::List(vec![
                                    SmtExpr::Atom(format!("el{}", i + 1)),
                                    expr.clone().into(),
                                ]),
                            )
                        })
                        .collect();

                    SmtLet {
                        bindings,
                        body: result.unwrap(),
                    }
                    .into()
                }
                Statement::InvokeOracle {
                    target_inst_name: None,
                    ..
                } => {
                    panic!("found an unresolved oracle invocation: {:#?}", stmt);
                }
                Statement::InvokeOracle {
                    id,
                    opt_idx,
                    name,
                    args,
                    target_inst_name: Some(target),
                } => {
                    let smt_expr = SmtLet {
                        bindings: vec![(smt_to_string(SspSmtVar::ReturnValue), {
                            let mut cmdline = vec![
                                SmtExpr::Atom(format!(
                                    "oracle-{}-{}-{}",
                                    self.comp.name, target, name
                                )),
                                SspSmtVar::GlobalState.into(),
                            ];

                            for arg in args {
                                cmdline.push(arg.clone().into())
                            }

                            SmtExpr::List(cmdline)
                        })],
                        body: SmtIte {
                            cond: SmtIs {
                                con: format!("mk-abort-{}-{}-{}", self.comp.name, target, name),
                                expr: SspSmtVar::ReturnValue,
                            },
                            then: SspSmtVar::OracleAbort {
                                compname: self.comp.name.clone(),
                                pkgname: pkgname.into(),
                                oname: sig.name.clone(),
                            },
                            els: SmtLet {
                                bindings: vec![
                                    (
                                        smt_to_string(SspSmtVar::GlobalState),
                                        SmtExpr::List(vec![
                                            SmtExpr::Atom(format!(
                                                "return-{}-{}-{}-state",
                                                self.comp.name, target, name
                                            )),
                                            SspSmtVar::ReturnValue.into(),
                                        ]),
                                    ),
                                    (
                                        id.ident(),
                                        SmtExpr::List(vec![
                                            SmtExpr::Atom(format!(
                                                "return-{}-{}-{}-value",
                                                self.comp.name, target, name
                                            )),
                                            SspSmtVar::ReturnValue.into(),
                                        ]),
                                    ),
                                ],
                                body: result.unwrap(),
                            },
                        },
                    };

                    if opt_idx.is_some() {
                        SmtExpr::List(vec![
                            SmtExpr::Atom("store".into()),
                            id.to_expression().into(),
                            opt_idx.clone().unwrap().into(),
                            smt_expr.into(),
                        ])
                    } else {
                        smt_expr.into()
                    }
                }
                Statement::Assign(ident, opt_idx, expr) => {
                    let (t, expr) = if let Expression::Typed(t, inner) = expr {
                        (t.clone(), *inner.clone())
                    } else {
                        unreachable!("we expect that this is typed")
                    };

                    // first build the unwrap expression, if we have to
                    let outexpr = if let Expression::Unwrap(inner) = &expr {
                        SmtExpr::List(vec![
                            SmtExpr::Atom("maybe-get".into()),
                            SmtExpr::Atom(smt_to_string(*inner.clone())),
                        ])
                    } else {
                        expr.clone().into()
                    };

                    // then build the table store smt expression, in case we have to
                    let outexpr = if let Some(idx) = opt_idx {
                        let oldvalue = match &ident {
                            &Identifier::State { name, pkgname, .. } => self
                                .get_state_helper(pkgname)
                                .smt_access(name, SspSmtVar::SelfState.into()),
                            Identifier::Local(_) => ident.to_expression().into(),
                            _ => {
                                unreachable!("")
                            }
                        };

                        SmtExpr::List(vec![
                            SmtExpr::Atom("store".into()),
                            oldvalue,
                            idx.clone().into(),
                            outexpr,
                        ])
                    } else {
                        outexpr
                    };

                    // build the actual smt assignment
                    let smtout = match ident {
                        Identifier::State { name, pkgname, .. } => SmtLet {
                            bindings: vec![(
                                smt_to_string(SspSmtVar::SelfState),
                                self.get_state_helper(pkgname).smt_set(name, &outexpr),
                            )],
                            body: result.unwrap(),
                        },

                        Identifier::Local(name) => SmtLet {
                            bindings: vec![(name.clone(), outexpr)],
                            body: result.unwrap(),
                        },

                        _ => {
                            unreachable!("can't assign to {:#?}", ident)
                        }
                    };

                    // if it's an unwrap, also wrap it with the unwrap check.
                    if let Expression::Unwrap(inner) = expr {
                        SmtIte {
                            cond: SmtIs {
                                con: format!("(mk-none () {})", {
                                    let t_smt: SmtExpr = Type::Maybe(Box::new(t)).into();
                                    smt_to_string(t_smt)
                                }),
                                expr: *inner.clone(),
                            },
                            then: SspSmtVar::OracleAbort {
                                compname: self.comp.name.clone(),
                                pkgname: pkgname.into(),
                                oname: sig.name.clone(),
                            },
                            els: smtout,
                        }
                        .into()
                    } else {
                        smtout.into()
                    }
                }
            });
        }
        result.unwrap()
    }

    /* example
        (define-fun
            stored_key_equals_k
            ((state_all State_composition) (k Key))
            Return_stored-key-equals-k
            (let
                (state_key (state-composition-key state_all))
                (mk-stored-key-equals-k
                    state-all
                    (=
                        (state-key-k state_key)
                        k
                    )
                )
            )
        )
    */

    fn smt_pkg_code(&self, inst: &PackageInstance) -> Vec<SmtExpr> {
        inst.pkg
            .oracles
            .iter()
            .map(|def| {
                let code = &def.code;
                let mut args = vec![SmtExpr::List(vec![
                    SspSmtVar::GlobalState.into(),
                    self.comp_helper.smt_sort(),
                ])];

                for (name, tipe) in def.sig.args.clone() {
                    args.push(SmtExpr::List(vec![SmtExpr::Atom(name), tipe.into()]))
                }

                SmtExpr::List(vec![
                    SmtExpr::Atom(String::from("define-fun")),
                    SmtExpr::Atom(format!(
                        "oracle-{}-{}-{}",
                        self.comp.name, inst.name, def.sig.name
                    )),
                    SmtExpr::List(args),
                    SmtExpr::Atom(format!(
                        "Return_{}_{}_{}",
                        self.comp.name, inst.name, def.sig.name
                    )),
                    SmtLet {
                        bindings: vec![(
                            smt_to_string(SspSmtVar::SelfState),
                            self.comp_helper
                                .smt_access(&inst.name, SspSmtVar::GlobalState.into()),
                        )],
                        body: self.code_smt_helper(code.clone(), &def.sig, inst),
                    }
                    .into(),
                ])
            })
            .collect()
    }

    fn smt_composition_code(&self) -> Vec<SmtExpr> {
        let comment = vec![SmtExpr::Comment(format!(
            "Composition of {}\n",
            self.comp.name
        ))];
        let ordered_pkgs = self.comp.ordered_pkgs();
        let code = ordered_pkgs.iter().flat_map(|inst| self.smt_pkg_code(inst));

        comment.into_iter().chain(code).collect()
    }

    fn smt_composition_randomness(&self) -> Vec<SmtExpr> {
        vec![
            SmtPackageState::new(
                &self.comp.name,
                "__randomness",
                vec![("ctr".into(), Type::Integer)],
            )
            .smt_declare_datatype(),
            SmtExpr::List(vec![
                SmtExpr::Atom("declare-fun".into()),
                SmtExpr::Atom(format!("__sample-rand-{}", self.comp.name)),
                SmtExpr::List(vec![SmtExpr::Atom("Int".into())]),
                SmtExpr::Atom("Bits_n".to_owned()),
            ]),
        ]
    }

    pub fn smt_composition_all(&self) -> Vec<SmtExpr> {
        let rand = self.smt_composition_randomness();
        let state = self.smt_composition_state();
        let ret = self.smt_composition_return();
        let code = self.smt_composition_code();

        rand.into_iter()
            .chain(state.into_iter())
            .chain(ret.into_iter())
            .chain(code.into_iter())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::string::FromUtf8Error;
    use thiserror::Error;

    use crate::smt::exprs::SmtFmt;

    #[derive(Error, Debug)]
    enum TestError {
        #[error("Error parsing the utf8: {0}")]
        Utf8DecodeError(#[from] FromUtf8Error),
        #[error("Error Writing: {0}")]
        WriteError(#[from] std::io::Error),
    }

    type TestResult = std::result::Result<(), TestError>;

    #[test]
    fn test_smtlet() -> TestResult {
        let l = SmtLet {
            bindings: vec![(
                "x".into(),
                Expression::IntegerLiteral(String::from("42")).into(),
            )],
            body: SmtExpr::Atom(String::from("x")),
        };

        let out: SmtExpr = l.into();
        let mut str = Vec::<u8>::new();
        out.write_smt_to(&mut str)?;

        assert_eq!(String::from_utf8(str)?, "(let ((x 42)) x)");

        Ok(())
    }
}
