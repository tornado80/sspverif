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
                compname,
            }) => SmtExpr::List(vec![
                SmtExpr::Atom(format!("state-{}-{}-{}", compname, pkgname, identname)),
                SspSmtVar::SelfState.into(),
            ]),
            Expression::Bot => SmtExpr::Atom("bot".to_string()),
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
            Type::Integer => SmtExpr::Atom("Int".into()),
            _ => {
                panic!("not implemented: {:?}", t)
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
            SspSmtVar::OracleReturnConstructor { pkgname, oname } => {
                SmtExpr::Atom(format!("mk-return-{}-{}", pkgname, oname))
            }
            SspSmtVar::OracleAbort { pkgname, oname } => {
                SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, oname))
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
    OracleReturnConstructor { pkgname: String, oname: String },
    OracleAbort { pkgname: String, oname: String },
}

pub struct CompositionSmtWriter<'a> {
    pub comp: &'a Composition,

    state_helpers: std::collections::HashMap<String, SmtPackageState<'a>>,
    comp_helper: SmtCompositionState<'a>,
}

use std::default::Default;

impl<'a> CompositionSmtWriter<'a> {
    pub fn new(comp: &'a Composition) -> CompositionSmtWriter<'a> {
        let mut csw = CompositionSmtWriter {
            comp: comp,
            state_helpers: Default::default(),
            comp_helper: SmtCompositionState {
                comp_name: &comp.name,
                substate_names: vec!["__randomness"]
                    .into_iter()
                    .chain(comp.pkgs.iter().map(|inst| &inst.name as &str))
                    .collect(),
            },
        };

        csw.state_helpers.insert(
            "__randomness".into(),
            SmtPackageState::<'a> {
                comp_name: &csw.comp.name,
                inst_name: "__randomness",
                state: vec![("ctr".into(), Type::Integer)],
            },
        );

        for inst in &csw.comp.pkgs {
            csw.state_helpers.insert(
                inst.name.clone(),
                SmtPackageState {
                    comp_name: &csw.comp.name,
                    inst_name: &inst.name,
                    state: inst.pkg.state.clone(),
                },
            );
        }

        csw
    }

    fn get_state_helper(&'a self, instname: &str) -> &'a SmtPackageState<'a> {
        if instname == "__randomness" {}

        self.state_helpers
            .get(instname)
            .expect(&format!("error looking up smt state helper: {}", instname))
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
                SmtExpr::Atom(format!("mk-return-{}-{}", inst.name, osig.name)),
                SmtExpr::List(vec![
                    SmtExpr::Atom(format!("return-{}-{}-state", inst.name, osig.name)),
                    self.comp_helper.smt_sort(),
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
                        pkgname: pkgname.clone(),
                        oname: sig.name.clone(),
                    }
                    .into()
                    //SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, sig.name))
                }
                // TODO actually use the type that we sample to know how far to advance the randomness tape
                Statement::Assign(ident, Expression::Sample(_)) => {
                    let ctr = self.get_state_helper("__randomness").smt_access(
                        "ctr",
                        self.comp_helper
                            .smt_access("__randomness", SspSmtVar::GlobalState.into()),
                    );
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
                    SmtLet {
                        bindings: vec![(
                            ident.ident(),
                            SmtExpr::List(vec![
                                SmtExpr::Atom(format!("__sample-rand-{}", self.comp.name)),
                                ctr.clone(),
                            ]),
                        )],
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
                    match ident {
                        Identifier::Scalar(name) => panic!("found a {:?}", name),
                        Identifier::Local(name) => SmtLet {
                            bindings: vec![(name.clone(), expr.clone().into())],
                            body: result.unwrap(),
                        }
                        .into(),
                        Identifier::State { name, pkgname, .. } => SmtLet {
                            bindings: vec![(
                                smt_to_string(SspSmtVar::SelfState),
                                self.get_state_helper(&pkgname)
                                    .smt_set(name, &expr.clone().into()),
                            )],
                            body: result.unwrap(),
                        }
                        .into(),

                        _ => panic!("not implemented"),
                    }
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
                    SmtExpr::Atom(format!("oracle-{}-{}", inst.name, def.sig.name)),
                    SmtExpr::List(args),
                    SmtExpr::Atom(format!("Return_{}_{}", inst.name, def.sig.name)),
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
            "Composition of {}",
            self.comp.name
        ))];
        let code = self
            .comp
            .pkgs
            .iter()
            .map(|inst| self.smt_pkg_code(inst))
            .flatten();

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
                SmtExpr::Atom(format!("Bits_n")),
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

/**
* composition state smt gen helper type
*
* what do we need?
* - composition state sort name
* - composition state constructor name
* - composition state accessor names
* - composition state sort definition
* - composition state accessor helpers
* - overwrite/copy-on-write helper
*
* for that we need...
* - composition name
* - SmtPackageState values for each instance
*
*
   (declare-datatype State_right-pkey (
        (mk-state-right-pkey   (state-right-pkey-pk   (Array Int String))
                               (state-right-pkey-sk   (Array Int String))
                               (state-right-pkey-id   (Array String Int))
                               (state-right-pkey-ctr  Int)
                               (state-right-pkey-rand RandState))))
*
*/

struct SmtCompositionState<'a> {
    comp_name: &'a str,
    substate_names: Vec<&'a str>,
}

impl<'a> SmtCompositionState<'a> {
    pub fn new(comp_name: &'a str, substate_names: Vec<&'a str>) -> SmtCompositionState<'a> {
        SmtCompositionState {
            comp_name,
            substate_names,
        }
    }
    fn smt_sort(&self) -> SmtExpr {
        SmtExpr::Atom(format!("CompositionState-{}", self.comp_name))
    }

    fn smt_constructor(&self) -> SmtExpr {
        SmtExpr::Atom(format!("mk-composition-state-{}", self.comp_name))
    }

    fn smt_accessor(&self, inst_name: &str) -> SmtExpr {
        // TODO should we check that inst_name is in inst_names? same for SmtPackageState
        SmtExpr::Atom(format!(
            "composition-state-{}-{}",
            self.comp_name, inst_name
        ))
    }

    fn smt_access(&self, inst_name: &str, term: SmtExpr) -> SmtExpr {
        SmtExpr::List(vec![self.smt_accessor(inst_name), term])
    }

    fn smt_declare_datatype(&self) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for inst_name in &self.substate_names {
            let pkg_state = SmtPackageState {
                comp_name: self.comp_name,
                inst_name: inst_name,
                state: vec![],
            };
            tmp.push(SmtExpr::List(vec![
                self.smt_accessor(inst_name),
                pkg_state.smt_sort(),
            ]))
        }

        SmtExpr::List(vec![
            SmtExpr::Atom("declare-datatype".to_string()),
            self.smt_sort(),
            SmtExpr::List(vec![SmtExpr::List(tmp)]),
        ])
    }

    fn smt_set(&self, target: &str, new: &SmtExpr, body: SmtExpr) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for inst_name in &self.substate_names {
            tmp.push(if *inst_name == target {
                new.clone()
            } else {
                self.smt_access(inst_name, SspSmtVar::GlobalState.into())
            });
        }

        SmtLet {
            bindings: vec![(smt_to_string(SspSmtVar::GlobalState), SmtExpr::List(tmp))],
            body,
        }
        .into()
    }
}

/**
 * packages state smt gen helper type
 *
 * what do we need?
 * - state type name ✅
 * - state type definition ✅
 * - state type constructor name ✅
 * - state type accessors ✅
 * - overwrite/copy-on-write helper ✅
 *
 * for that we need...
 * - composition name
 * - package instance name
 * - state variables
 */
pub struct SmtPackageState<'a> {
    comp_name: &'a str,
    inst_name: &'a str,
    state: Vec<(String, Type)>,
}

/**
 * comp = mod_prf_game
 * inst = multi_key
 */

impl<'a> SmtPackageState<'a> {
    pub fn new(
        comp_name: &'a str,
        inst_name: &'a str,
        state: Vec<(String, Type)>,
    ) -> SmtPackageState<'a> {
        SmtPackageState {
            comp_name,
            inst_name,
            state,
        }
    }

    fn smt_constructor(&self) -> SmtExpr {
        SmtExpr::Atom(format!("mk-state-{}-{}", self.comp_name, self.inst_name))
    }

    fn smt_sort(&self) -> SmtExpr {
        SmtExpr::Atom(format!("State-{}-{}", self.comp_name, self.inst_name))
    }

    fn smt_accessor(&self, id: &str) -> SmtExpr {
        SmtExpr::Atom(format!(
            "state-{}-{}-{}",
            self.comp_name, self.inst_name, id
        ))
    }

    fn smt_access(&self, id: &str, term: SmtExpr) -> SmtExpr {
        SmtExpr::List(vec![self.smt_accessor(id), term])
    }

    pub fn smt_declare_datatype(&self) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for (id, tipe) in &self.state {
            tmp.push(SmtExpr::List(vec![
                self.smt_accessor(id),
                tipe.clone().into(),
            ]))
        }

        SmtExpr::List(vec![
            SmtExpr::Atom("declare-datatype".to_string()),
            self.smt_sort(),
            SmtExpr::List(vec![SmtExpr::List(tmp)]),
        ])
    }

    fn smt_set(&self, id: &str, new: &SmtExpr) -> SmtExpr {
        let mut tmp = vec![self.smt_constructor()];

        for (varname, _) in self.state.clone() {
            if varname == *id {
                tmp.push(new.clone());
            } else {
                tmp.push(SmtExpr::List(vec![
                    self.smt_accessor(&varname),
                    SspSmtVar::SelfState.into(),
                ]));
            }
        }

        SmtExpr::List(tmp)
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
