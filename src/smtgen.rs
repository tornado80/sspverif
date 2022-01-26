use std::io::{Result, Write};

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::types::Type;

use crate::package::{Composition, OracleSig, PackageInstance};
use crate::statement::{CodeBlock, Statement};

pub fn smt_to_string<T: Into<SmtExpr>>(t: T) -> String {
    let expr: SmtExpr = t.into();
    expr.to_string()
}

pub trait SmtFmt {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()>;

    fn to_string(&self) -> String {
        let mut buf = vec![];
        self.write_smt_to(&mut buf)
            .expect("can't happen, we assume the buffer never errors");

        String::from_utf8(buf).expect("can't happen, we only write utf8")
    }
}

#[derive(Debug, Clone)]
pub enum SmtExpr {
    Comment(String),
    Atom(String),
    List(Vec<SmtExpr>),
}

impl SmtFmt for SmtExpr {
    fn write_smt_to<T: Write>(&self, write: &mut T) -> Result<()> {
        match self {
            SmtExpr::Comment(str) => write!(write, "; {}", str),
            SmtExpr::Atom(str) => write!(write, "{}", str),
            SmtExpr::List(lst) => {
                let mut peek = lst.iter().peekable();

                write!(write, "(")?;
                while let Some(elem) = peek.next() {
                    elem.write_smt_to(write)?;

                    if peek.peek().is_some() {
                        write!(write, " ")?;
                    }
                }
                write!(write, ")")
            }
        }
    }
}

impl From<Expression> for SmtExpr {
    fn from(expr: Expression) -> SmtExpr {
        match expr {
            Expression::BooleanLiteral(litname) => SmtExpr::Atom(litname),
            Expression::IntegerLiteral(litname) => SmtExpr::Atom(litname),
            Expression::Equals(exprs) => {
                let mut acc = vec![SmtExpr::Atom("=".to_string())];
                for expr in exprs {
                    acc.push(expr.clone().into());
                }

                SmtExpr::List(acc)
            }
            Expression::Identifier(Identifier::Scalar(identname)) => SmtExpr::Atom(identname),
            Expression::Identifier(Identifier::Local(identname)) => SmtExpr::Atom(identname),
            Expression::Identifier(Identifier::State {
                name: identname,
                pkgname,
            }) => SmtExpr::List(vec![
                SmtExpr::Atom(format!("state-{}-{}", pkgname, identname)),
                SspSmtVar::SelfState.into(),
            ]),
            Expression::Bot => SmtExpr::Atom("bot".to_string()),
            Expression::Sample(_tipe) => {
                // TODO: fix this later! This is generally speaking not correct!
                SmtExpr::Atom("rand".to_string())
            }
            Expression::FnCall(name, exprs) => {
                let mut call = vec![SmtExpr::Atom(name)];

                for expr in exprs {
                    call.push(expr.into());
                }

                SmtExpr::List(call)
            }
            _ => {
                panic!("not implemented: {:?}", expr);
            }
        }
    }
}

impl From<Type> for SmtExpr {
    fn from(t: Type) -> SmtExpr {
        match t {
            Type::Bits(length) => {
                // TODO make sure we define this somewhere
                SmtExpr::Atom(format!("Bits_{}", length))
            }
            Type::Boolean => SmtExpr::Atom("Bool".to_string()),
            _ => {
                panic!("not implemented!")
            }
        }
    }
}

impl<C, T, E> From<SmtIte<C, T, E>> for SmtExpr
where
    C: Into<SmtExpr>,
    T: Into<SmtExpr>,
    E: Into<SmtExpr>,
{
    fn from(ite: SmtIte<C, T, E>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::Atom("ite".into()),
            ite.cond.into(),
            ite.then.into(),
            ite.els.into(),
        ])
    }
}

impl<C, E> From<SmtIs<C, E>> for SmtExpr
where
    C: Into<String>,
    E: Into<SmtExpr>,
{
    fn from(is: SmtIs<C, E>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::List(vec![
                SmtExpr::Atom("_".into()),
                SmtExpr::Atom("is".into()),
                SmtExpr::Atom(is.con.into()),
            ]),
            is.expr.into(),
        ])
    }
}

impl<B> From<SmtLet<B>> for SmtExpr
where
    B: Into<SmtExpr>,
{
    fn from(l: SmtLet<B>) -> SmtExpr {
        SmtExpr::List(vec![
            SmtExpr::Atom(String::from("let")),
            SmtExpr::List(
                l.bindings
                    .into_iter()
                    .map(|(id, expr)| SmtExpr::List(vec![SmtExpr::Atom(id), expr]))
                    .collect(),
            ),
            l.body.into(),
        ])
    }
}

impl From<SspSmtVar> for SmtExpr {
    fn from(v: SspSmtVar) -> SmtExpr {
        match v {
            SspSmtVar::GlobalState => SmtExpr::Atom("__global_state".into()),
            SspSmtVar::SelfState => SmtExpr::Atom("__self_state".into()),
            SspSmtVar::ReturnValue => SmtExpr::Atom("__ret".into()),
            SspSmtVar::PackageStateConstructor { pkgname } => {
                SmtExpr::Atom(format!("mk-state-{}", pkgname))
            }
            SspSmtVar::OracleReturnConstructor { pkgname, oname } => {
                SmtExpr::Atom(format!("mk-return-{}-{}", pkgname, oname))
            }
            SspSmtVar::OracleAbort { pkgname, oname } => {
                SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, oname))
            }
            SspSmtVar::CompositionStateConstructor { compname } => {
                SmtExpr::Atom(format!("mk-state-composition-{}", compname))
            }
        }
    }
}

pub struct SmtLet<B>
where
    B: Into<SmtExpr>,
{
    pub bindings: Vec<(String, SmtExpr)>,
    pub body: B,
}

pub struct SmtIte<C, T, E>
where
    C: Into<SmtExpr>,
    T: Into<SmtExpr>,
    E: Into<SmtExpr>,
{
    pub cond: C,
    pub then: T,
    pub els: E,
}

pub struct SmtIs<C, E>
where
    C: Into<String>,
    E: Into<SmtExpr>,
{
    pub con: C,
    pub expr: E,
}

pub enum SspSmtVar {
    GlobalState,
    SelfState,
    ReturnValue,
    CompositionStateConstructor { compname: String },
    PackageStateConstructor { pkgname: String },
    OracleReturnConstructor { pkgname: String, oname: String },
    OracleAbort { pkgname: String, oname: String },
}

pub struct CompositionSmtWriter {
    pub comp: Composition,
}

impl CompositionSmtWriter {
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
    fn smt_pkg_state(&self, inst: &PackageInstance) -> Vec<SmtExpr> {
        let mut tmp = vec![SmtExpr::Atom(format!("mk-state-{}", inst.name))];

        for (id, tipe) in inst.pkg.clone().state {
            tmp.push(SmtExpr::List(vec![
                SmtExpr::Atom(format!("state-{}-{}", inst.name, id)),
                tipe.into(),
            ]))
        }

        vec![SmtExpr::List(vec![
            SmtExpr::Atom("declare-datatype".to_string()),
            SmtExpr::Atom(format!("State_{}", inst.name)),
            SmtExpr::List(vec![SmtExpr::List(tmp)]),
        ])]
    }

    pub fn smt_composition_state(&self) -> Vec<SmtExpr> {
        let compname = self.comp.name.clone();

        // 1. each package in composition
        let mut states: Vec<SmtExpr> = self
            .comp
            .pkgs
            .clone()
            .iter()
            .map(|pkg| self.smt_pkg_state(pkg))
            .flatten()
            .collect();

        // 2. composed state
        let mut tmp = vec![SmtExpr::Atom(format!("mk-state-composition-{}", compname))];

        for inst in &self.comp.pkgs {
            tmp.push(SmtExpr::List(vec![
                SmtExpr::Atom(format!("state-composition-{}-{}", compname, inst.name)),
                SmtExpr::Atom(format!("State_{}", inst.name)),
            ]));
        }

        states.push(SmtExpr::List(vec![
            SmtExpr::Atom("declare-datatype".to_string()),
            SmtExpr::Atom(format!("State_composition-{}", compname)),
            SmtExpr::List(vec![SmtExpr::List(tmp)]),
        ]));

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
                SmtExpr::Atom(format!("mk-return-{}-{}", inst.name, osig.name)),
                SmtExpr::List(vec![
                    SmtExpr::Atom(format!("return-{}-{}-state", inst.name, osig.name)),
                    SmtExpr::Atom(format!("State_composition-{}", self.comp.name)),
                ]),
            ];

            if Type::Empty != osig.tipe {
                constructor.push(SmtExpr::List(vec![
                    SmtExpr::Atom(format!("return-{}-{}-value", inst.name, osig.name)),
                    osig.tipe.into(),
                ]));
            }

            smts.push(SmtExpr::List(vec![
                SmtExpr::Atom("declare-datatype".to_string()),
                SmtExpr::Atom(format!("Return_{}_{}", inst.name, osig.name)),
                SmtExpr::List(vec![
                    SmtExpr::List(constructor),
                    SmtExpr::List(vec![SmtExpr::Atom(format!(
                        "mk-abort-{}-{}",
                        inst.name, osig.name
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
            .map(|inst| self.smt_pkg_return(inst))
            .flatten()
            .collect()
    }

    fn code_smt_helper(
        &self,
        block: CodeBlock,
        sig: &OracleSig,
        inst: &PackageInstance,
    ) -> SmtExpr {
        let PackageInstance {
            pkg, name: pkgname, ..
        } = inst;

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
                            pkgname: pkgname.clone(),
                            oname: sig.name.clone(),
                        }
                        .into(),
                        SspSmtVar::GlobalState.into(),
                    ])
                }
                Statement::Return(Some(expr)) => {
                    // (mk-return-{name} statevarname expr)
                    SmtLet {
                        bindings: vec![(smt_to_string(SspSmtVar::GlobalState), {
                            let stuff = self.comp.pkgs.iter().map(|iterinst| {
                                if iterinst.name == inst.name {
                                    SspSmtVar::SelfState.into()
                                } else {
                                    SmtExpr::List(vec![
                                        SmtExpr::Atom(format!(
                                            "state-composition-{}-{}",
                                            self.comp.name, iterinst.name
                                        )),
                                        SspSmtVar::GlobalState.into(),
                                    ])
                                }
                                // (state-composition-xxx-packagename globalstate)
                            });

                            let liststart = vec![SspSmtVar::CompositionStateConstructor {
                                compname: self.comp.name.clone(),
                            }
                            .into()];

                            //SmtExpr::List(vec![SmtExpr::Atom("mist".into())]) // we need the composition info here, let's figure out how to structure this instead...

                            SmtExpr::List(liststart.into_iter().chain(stuff).collect())
                        })],
                        body: SmtExpr::List(vec![
                            SspSmtVar::OracleReturnConstructor {
                                pkgname: pkgname.clone(),
                                oname: sig.name.clone(),
                            }
                            .into(),
                            SspSmtVar::GlobalState.into(),
                            expr.clone().into(),
                        ]),
                    }
                    .into()
                }
                Statement::Abort => {
                    // mk-abort-{name}
                    SspSmtVar::OracleAbort {
                        pkgname: pkgname.clone(),
                        oname: sig.name.clone(),
                    }
                    .into()
                    //SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, sig.name))
                }
                Statement::Assign(
                    ident,
                    Expression::LowLevelOracleInvoc {
                        name,
                        pkgname: dst_pkgname,
                        args,
                    },
                ) => SmtLet {
                    bindings: vec![(smt_to_string(SspSmtVar::ReturnValue), {
                        let mut cmdline = vec![
                            SmtExpr::Atom(format!("oracle-{}-{}", dst_pkgname, name)),
                            SspSmtVar::GlobalState.into(),
                        ];

                        for arg in args {
                            cmdline.push(arg.clone().into())
                        }

                        SmtExpr::List(cmdline)
                    })],
                    body: SmtIte {
                        cond: SmtIs {
                            con: format!("mk-abort-{}-{}", dst_pkgname, name),
                            expr: SspSmtVar::ReturnValue,
                        },
                        then: SspSmtVar::OracleAbort {
                            pkgname: pkgname.into(),
                            oname: sig.name.clone(),
                        },
                        els: SmtLet {
                            bindings: vec![
                                (
                                    smt_to_string(SspSmtVar::GlobalState),
                                    SmtExpr::List(vec![
                                        SmtExpr::Atom(format!(
                                            "return-{}-{}-state",
                                            dst_pkgname, name
                                        )),
                                        SspSmtVar::ReturnValue.into(),
                                    ]),
                                ),
                                (
                                    ident.ident(),
                                    SmtExpr::List(vec![
                                        SmtExpr::Atom(format!(
                                            "return-{}-{}-value",
                                            dst_pkgname, name
                                        )),
                                        SspSmtVar::ReturnValue.into(),
                                    ]),
                                ),
                            ],
                            body: result.unwrap(),
                        },
                    },
                }
                .into(),
                Statement::Assign(ident, expr) => {
                    // State_{name} (quote " state")
                    let assignment = match ident {
                        Identifier::Scalar(name) => panic!("found a {:?}", name),
                        Identifier::Local(name) => {
                            vec![SmtExpr::List(vec![SmtExpr::List(vec![
                                SmtExpr::Atom(name.clone()),
                                expr.clone().into(),
                            ])])]
                        }
                        Identifier::State { name, pkgname } => {
                            let mut tmp = vec![SspSmtVar::PackageStateConstructor {
                                pkgname: pkgname.clone(),
                            }
                            .into()];

                            for (varname, _) in pkg.state.clone() {
                                if varname == *name {
                                    tmp.push(expr.clone().into());
                                } else {
                                    tmp.push(SmtExpr::List(vec![
                                        SmtExpr::Atom(format!("state-{}-{}", pkgname, varname)),
                                        SspSmtVar::SelfState.into(),
                                    ]));
                                }
                            }

                            vec![SmtExpr::List(vec![
                                SspSmtVar::SelfState.into(),
                                SmtExpr::List(tmp),
                            ])]
                        }
                        _ => panic!("not implemented"),
                    };

                    SmtExpr::List(vec![
                        SmtExpr::Atom("let".to_string()),
                        SmtExpr::List(assignment),
                        result.unwrap(),
                    ])
                }
                _ => {
                    panic!("not implemented")
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
    pub fn code_smt(&self) -> Vec<SmtExpr> {
        self.smt_composition_code()
    }

    fn smt_pkg_code(&self, inst: &PackageInstance) -> Vec<SmtExpr> {
        inst.var_specify()
            .pkg
            .oracles
            .iter()
            .map(|def| {
                let code = def.code.treeify().returnify();
                let mut args = vec![SmtExpr::List(vec![
                    SspSmtVar::GlobalState.into(),
                    SmtExpr::Atom(format!("State_composition-{}", self.comp.name)),
                ])];

                for (name, tipe) in def.sig.args.clone() {
                    args.push(SmtExpr::List(vec![SmtExpr::Atom(name), tipe.into()]))
                }

                SmtExpr::List(vec![
                    SmtExpr::Atom(String::from("define-fun")),
                    SmtExpr::Atom(format!("oracle-{}-{}", inst.name, def.sig.name)),
                    SmtExpr::List(args),
                    SmtExpr::Atom(format!("Return_{}_{}", inst.name, def.sig.name)),
                    SmtLet {
                        bindings: vec![(
                            smt_to_string(SspSmtVar::SelfState),
                            SmtExpr::List(vec![
                                SmtExpr::Atom(format!(
                                    "state-composition-{}-{}",
                                    self.comp.name, inst.name
                                )),
                                SspSmtVar::GlobalState.into(),
                            ]),
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
            "Composition of {}",
            self.comp.name
        ))];
        let llcomp = self.comp.lowlevelify_oracleinvocs();
        let code = llcomp
            .pkgs
            .iter()
            .map(|inst| self.smt_pkg_code(inst))
            .flatten();

        comment.into_iter().chain(code).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::string::FromUtf8Error;
    use thiserror::Error;

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
