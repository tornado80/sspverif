use crate::errors::TypeCheckError;
use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::scope::Scope;
use crate::smtgen::{statevarname, SmtExpr, SmtIs, SmtIte, SmtLet};
use crate::statement::{CodeBlock, Statement, TypedCodeBlock};
use crate::types::Type;

use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleDef {
    pub sig: OracleSig,
    pub code: CodeBlock,
}

impl OracleDef {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        let OracleDef {
            sig:
                OracleSig {
                    name: _name,
                    args,
                    tipe,
                },
            code,
        } = self;
        scope.enter();
        for (name, ntipe) in args {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        }
        let code_block = TypedCodeBlock {
            expected_return_type: tipe.clone(),
            block: code.clone(),
        };

        code_block.typecheck(scope)?;
        scope.leave();
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Package {
    pub params: Vec<(String, Type)>,
    pub state: Vec<(String, Type)>,
    pub oracles: Vec<OracleDef>,
}

impl Package {
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        let Package {
            params,
            state,
            oracles,
        } = self;

        scope.enter();
        for (name, ntipe) in params {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        }
        for (name, ntipe) in state {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        }

        for oracle in oracles {
            oracle.typecheck(scope)?;
        }

        scope.leave();
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackageInstance {
    Atom {
        params: HashMap<String, String>,
        pkg: Package,
        name: String,
    },
    Composition {
        pkgs: Vec<PackageInstance>,
        edges: Vec<(usize, usize, OracleSig)>, // (from, to, oraclesig)
        // TODO: how do we deal with the case where we have
        // e.g. multiple key packages that we Set into?
        // Idea: Add a name to this tuple that is used by
        // the invoking package
        // contemplation: globally unique oracle identifiers vs
        // multiple shades of local uniqueness
        exports: Vec<(usize, OracleSig)>,
        name: String,
    },
}

impl PackageInstance {
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

    fn var_specify_helper(&self, block: CodeBlock) -> CodeBlock {
        if let PackageInstance::Atom {
            name,
            pkg: Package { state, params, .. },
            ..
        } = self
        {
            let fixup = |expr| match expr {
                Expression::Identifier(Identifier::Scalar(id)) => {
                    if state.clone().iter().any(|(id_, _)| id == *id_) {
                        Expression::Identifier(Identifier::State {
                            name: id,
                            pkgname: name.clone(),
                        })
                    } else if params.clone().iter().any(|(id_, _)| id == *id_) {
                        Expression::Identifier(Identifier::Params {
                            name: id,
                            pkgname: name.clone(),
                        })
                    } else {
                        Expression::Identifier(Identifier::Local(id))
                    }
                }
                _ => expr,
            };
            CodeBlock(
                block
                    .0
                    .iter()
                    .map(|stmt| match stmt {
                        Statement::Abort => Statement::Abort,
                        Statement::Return(None) => Statement::Return(None),
                        Statement::Return(Some(expr)) => Statement::Return(Some(expr.map(fixup))),
                        Statement::Assign(id, expr) => {
                            if let Expression::Identifier(id) = fixup(id.to_expression()) {
                                Statement::Assign(id, expr.map(fixup))
                            } else {
                                panic!("unreachable")
                            }
                        }
                        Statement::IfThenElse(expr, ifcode, elsecode) => Statement::IfThenElse(
                            expr.map(fixup),
                            self.var_specify_helper(ifcode.clone()),
                            self.var_specify_helper(elsecode.clone()),
                        ),
                        _ => panic!("not implemented"),
                    })
                    .collect(),
            )
        } else {
            panic!("unreachable")
        }
    }

    pub fn var_specify(&self) -> PackageInstance {
        match &self {
            PackageInstance::Composition {
                pkgs,
                edges,
                exports,
                name,
            } => PackageInstance::Composition {
                name: name.clone(),
                exports: exports.clone(),
                edges: edges.clone(),
                pkgs: pkgs.iter().map(|pkg| pkg.var_specify()).collect(),
            },
            PackageInstance::Atom {
                pkg:
                    Package {
                        params: pkg_params,
                        state,
                        oracles,
                    },
                name,
                params,
            } => PackageInstance::Atom {
                name: name.clone(),
                params: params.clone(),
                pkg: Package {
                    params: pkg_params.clone(),
                    state: state.clone(),
                    oracles: oracles
                        .iter()
                        .map(|def| OracleDef {
                            sig: def.sig.clone(),
                            code: self.var_specify_helper(def.code.clone()),
                        })
                        .collect(),
                },
            },
        }
    }

    pub fn state_smt(&self) -> Vec<SmtExpr> {
        match &self {
            PackageInstance::Atom { pkg, name, .. } => {
                let mut tmp = vec![SmtExpr::Atom(format!("mk-state-{}", name))];

                for (id, tipe) in pkg.clone().state {
                    tmp.push(SmtExpr::List(vec![
                        SmtExpr::Atom(format!("state-{}-{}", name, id)),
                        tipe.into(),
                    ]))
                }

                vec![SmtExpr::List(vec![
                    SmtExpr::Atom("declare-datatype".to_string()),
                    SmtExpr::Atom(format!("State_{}", name)),
                    SmtExpr::List(vec![SmtExpr::List(tmp)]),
                ])]
            }
            PackageInstance::Composition { pkgs, name, .. } => {
                // 1. each package in composition
                let mut states: Vec<SmtExpr> = pkgs
                    .clone()
                    .iter()
                    .map(|x| x.state_smt())
                    .flatten()
                    .collect();

                // 2. composed state
                let mut tmp = vec![SmtExpr::Atom(format!("mk-state-composition-{}", name))];

                for pkg in pkgs {
                    let name = match pkg {
                        PackageInstance::Atom { name, .. } => name,
                        PackageInstance::Composition { name, .. } => name,
                    };

                    tmp.push(SmtExpr::List(vec![
                        SmtExpr::Atom(format!("state-{}", name)),
                        SmtExpr::Atom(format!("State_{}", name)),
                    ]));
                }

                states.push(SmtExpr::List(vec![
                    SmtExpr::Atom("declare-datatype".to_string()),
                    SmtExpr::Atom(format!("State_composition-{}", name)),
                    SmtExpr::List(vec![SmtExpr::List(tmp)]),
                ]));

                states
            }
        }
    }

    /*
    example:
    (declare-datatype Return_key_get (
        (mk-return-key-get         (return-key-get-state State_key)
                                    (return-key_get-value Bits_n))
        (mk-abort-key-get)
    ))


     */
    pub fn return_smt(&self) -> Vec<SmtExpr> {
        match &self {
            PackageInstance::Atom { name, .. } => {
                let mut smts = vec![];

                for osig in self.get_oracle_sigs() {
                    let mut constructor = vec![
                        SmtExpr::Atom(format!("mk-return-{}-{}", name, osig.name)),
                        SmtExpr::List(vec![
                            SmtExpr::Atom(format!("return-{}-{}-state", name, osig.name)),
                            SmtExpr::Atom(format!("State_{}", name)),
                        ]),
                    ];

                    if Type::Empty != osig.tipe {
                        constructor.push(SmtExpr::List(vec![
                            SmtExpr::Atom(format!("return-{}-{}-value", name, osig.name)),
                            osig.tipe.into(),
                        ]));
                    }

                    smts.push(SmtExpr::List(vec![
                        SmtExpr::Atom("declare-datatype".to_string()),
                        SmtExpr::Atom(format!("Return_{}_{}", name, osig.name)),
                        SmtExpr::List(vec![
                            SmtExpr::List(constructor),
                            SmtExpr::List(vec![SmtExpr::Atom(format!(
                                "mk-abort-{}-{}",
                                name, osig.name
                            ))]),
                        ]),
                    ]))
                }
                smts
            }
            PackageInstance::Composition { pkgs, .. } => {
                // 1. each package in composition
                pkgs.clone()
                    .iter()
                    .map(|x| x.return_smt())
                    .flatten()
                    .collect()
            }
        }
    }

    fn code_smt_helper(&self, block: CodeBlock, sig: &OracleSig) -> SmtExpr {
        if let PackageInstance::Atom {
            pkg, name: pkgname, ..
        } = self
        {
            let mut result = None;
            for stmt in block.0.iter().rev() {
                result = Some(match stmt {
                    Statement::IfThenElse(cond, ifcode, elsecode) => SmtExpr::List(vec![
                        SmtExpr::Atom("ite".to_string()),
                        cond.clone().into(),
                        self.code_smt_helper(ifcode.clone(), sig),
                        self.code_smt_helper(elsecode.clone(), sig),
                    ]),
                    Statement::Return(None) => {
                        // (mk-return-{name} statevarname)
                        SmtExpr::List(vec![
                            SmtExpr::Atom(format!("mk-return-{}-{}", pkgname, sig.name)),
                            statevarname(),
                        ])
                    }
                    Statement::Return(Some(expr)) => {
                        // (mk-return-{name} statevarname expr)
                        SmtExpr::List(vec![
                            SmtExpr::Atom(format!("mk-return-{}-{}", pkgname, sig.name)),
                            statevarname(),
                            expr.clone().into(),
                        ])
                    }
                    Statement::Abort => {
                        // mk-abort-{name}
                        SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, sig.name))
                    }
                    Statement::Assign(
                        ident,
                        Expression::LowLevelOracleInvoc {
                            name,
                            pkgname: dst_pkgname,
                            args,
                        },
                    ) => {
                        SmtLet {
                            bindings: vec![("ret".into(), {
                                let mut cmdline = vec![
                                    SmtExpr::Atom(format!("oracle-{}-{}", dst_pkgname, name)),
                                    SmtExpr::Atom(String::from("state_all")),
                                ];

                                for arg in args {
                                    cmdline.push(arg.clone().into())
                                }

                                SmtExpr::List(cmdline)
                            })],
                            body: SmtIte {
                                cond: SmtIs {
                                    con: format!("mk-abort-{}-{}", dst_pkgname, name),
                                    expr: SmtExpr::Atom(String::from("ret")),
                                },
                                then: SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, sig.name)),
                                els: SmtLet {
                                    bindings: vec![
                                        (
                                            "state_all".into(),
                                            SmtExpr::List(vec![
                                                SmtExpr::Atom(format!(
                                                    "return-{}-{}-state",
                                                    dst_pkgname, name
                                                )),
                                                SmtExpr::Atom(String::from("ret")),
                                            ]),
                                        ),
                                        (
                                            ident.ident(),
                                            SmtExpr::List(vec![
                                                SmtExpr::Atom(format!(
                                                    "return-{}-{}-value",
                                                    dst_pkgname, name
                                                )),
                                                SmtExpr::Atom(String::from("ret")),
                                            ]),
                                        ),
                                    ],
                                    body: result.unwrap(),
                                },
                            },
                        }
                        .into()
                        /*
                        SmtExpr::List(vec![
                            // let returnvalue <- oracle call
                            // if return is an abort: abort
                            // else: proceed.
                            SmtExpr::Atom(String::from("let")),
                            SmtExpr::List(vec![SmtExpr::List(vec![
                                SmtExpr::Atom(String::from("ret")),
                                SmtExpr::List({
                                    let mut cmdline = vec![
                                        SmtExpr::Atom(format!("oracle-{}-{}", dst_pkgname, name)),
                                        SmtExpr::Atom(String::from("state_all")),
                                    ];

                                    for arg in args {
                                        cmdline.push(arg.clone().into())
                                    }

                                    cmdline
                                }),
                            ])]),

                            SmtExpr::List(vec![
                                SmtExpr::Atom(String::from("ite")),
                                SmtExpr::List(vec![
                                    SmtExpr::List(vec![
                                        SmtExpr::Atom(String::from("_")),
                                        SmtExpr::Atom(String::from("is")),
                                        SmtExpr::Atom(format!("mk-abort-{}-{}", dst_pkgname, name)),
                                    ]),
                                    SmtExpr::Atom(String::from("ret")),
                                ]),
                                SmtExpr::Atom(format!("mk-abort-{}-{}", pkgname, sig.name)),
                                SmtExpr::List(vec![
                                    SmtExpr::Atom(String::from("let")),
                                    SmtExpr::List(vec![
                                        SmtExpr::List(vec![
                                            SmtExpr::Atom(String::from("state_all")),
                                            SmtExpr::List(vec![
                                                SmtExpr::Atom(format!(
                                                    "return-{}-{}-state",
                                                    dst_pkgname, name
                                                )),
                                                SmtExpr::Atom(String::from("ret")),
                                            ]),
                                        ]),
                                        SmtExpr::List(vec![
                                            ident.to_expression().into(),
                                            SmtExpr::List(vec![
                                                SmtExpr::Atom(format!(
                                                    "return-{}-{}-value",
                                                    dst_pkgname, name
                                                )),
                                                SmtExpr::Atom(String::from("ret")),
                                            ]),
                                        ]),
                                    ]),
                                    result.unwrap(),
                                ]),
                            ]),
                        ])
                        */
                    }
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
                                let mut tmp = vec![SmtExpr::Atom(format!("mk-state-{}", pkgname))];

                                for (varname, _) in pkg.state.clone() {
                                    if varname == *name {
                                        tmp.push(expr.clone().into());
                                    } else {
                                        tmp.push(SmtExpr::List(vec![
                                            SmtExpr::Atom(format!("state-{}-{}", pkgname, varname)),
                                            statevarname(),
                                        ]));
                                    }
                                }

                                vec![SmtExpr::List(vec![statevarname(), SmtExpr::List(tmp)])]
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
        } else {
            panic!("Unreachable Branch")
        }
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
        // HACK we need to pass the name of the composition to the
        // code processing the individual package instances.
        // We decided to, for now, pass this as a function argument.
        // We hide that detail using this function.
        let name = match self {
            PackageInstance::Atom { name, .. } => name,
            PackageInstance::Composition { name, .. } => name,
        };

        self.inner_code_smt(name)
    }

    pub fn inner_code_smt(&self, comp_name: &str) -> Vec<SmtExpr> {
        match &self {
            PackageInstance::Atom { pkg, name, .. } => pkg
                .oracles
                .iter()
                .map(|def| {
                    let code = def.code.treeify().returnify();
                    let mut args = vec![SmtExpr::List(vec![
                        SmtExpr::Atom(String::from("state_all")),
                        SmtExpr::Atom(format!("State_composition-{}", comp_name)),
                    ])];

                    for (name, tipe) in def.sig.args.clone() {
                        args.push(SmtExpr::List(vec![SmtExpr::Atom(name), tipe.into()]))
                    }

                    SmtExpr::List(vec![
                        SmtExpr::Atom(String::from("define-fun")),
                        SmtExpr::Atom(format!("oracle-{}-{}", name, def.sig.name)),
                        SmtExpr::List(args),
                        SmtExpr::Atom(format!("Return_{}_{}", name, def.sig.name)),
                        SmtExpr::List(vec![
                            SmtExpr::Atom(String::from("let")),
                            SmtExpr::List(vec![SmtExpr::List(vec![
                                statevarname(),
                                SmtExpr::List(vec![
                                    SmtExpr::Atom(format!("state-{}", name)),
                                    SmtExpr::Atom(String::from("state_all")),
                                ]),
                            ])]),
                            self.code_smt_helper(code, &def.sig),
                        ]),
                    ])
                })
                .collect(),
            PackageInstance::Composition {
                pkgs, edges, name, ..
            } => {
                let comment = vec![SmtExpr::Comment(format!("Composition of {}", name))];
                let code = pkgs
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        x.lowlevelify_oracleinvocs(i, pkgs, edges)
                            .inner_code_smt(comp_name)
                    })
                    .flatten();

                comment.into_iter().chain(code).collect()
            }
        }
    }

    fn lowlevelify_oracleinvocs(
        &self,
        pos: usize,
        pkgs: &[PackageInstance],
        edges: &[(usize, usize, OracleSig)],
    ) -> Self {
        let (mut pkg, name, params) = match self {
            PackageInstance::Atom { pkg, name, params } => (pkg.clone(), name, params),
            _ => unreachable!(),
        };

        let mut table = HashMap::<String, String>::new();
        let relevant = edges.iter().filter(|(from, _, _)| *from == pos);

        for (_, to, sig) in relevant {
            let pkgname = match &pkgs[*to] {
                PackageInstance::Atom { name, .. } => name,
                PackageInstance::Composition { name, .. } => name,
            };

            table.insert(sig.name.clone(), pkgname.clone());
        }

        let fixup = |expr| match expr {
            Expression::OracleInvoc(name, args) => {
                if let Some(pkgname) = table.get(&name) {
                    Expression::LowLevelOracleInvoc {
                        name,
                        pkgname: pkgname.clone(),
                        args,
                    }
                } else {
                    panic!("couldn't find package for oracle {}", name);
                }
            }
            _ => expr,
        };

        for oracle in &mut pkg.oracles {
            oracle.code.0 = oracle
                .code
                .0
                .iter()
                .map(|stmt| match stmt {
                    Statement::Assign(id, expr) => Statement::Assign(id.clone(), expr.map(fixup)),
                    _ => stmt.clone(),
                })
                .collect();
        }

        PackageInstance::Atom {
            pkg,
            name: name.clone(),
            params: params.clone(),
        }
    }

    pub fn get_pkg(&self) -> Package {
        match self {
            PackageInstance::Atom { pkg, .. } => pkg.clone(),
            _ => panic!(),
        }
    }

    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        match self {
            PackageInstance::Atom { pkg, .. } => {
                pkg.oracles.clone().into_iter().map(|d| d.sig).collect()
            }
            PackageInstance::Composition { exports, .. } => {
                exports.iter().map(|(_, sig)| sig.clone()).collect()
            }
        }
    }

    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        match self {
            PackageInstance::Atom { pkg, .. } => {
                // TODO also check params
                pkg.typecheck(scope)
            }
            PackageInstance::Composition {
                pkgs,
                edges,
                exports,
                ..
            } => {
                // 1. check signature exists in edge destination
                for (_, to, sig_) in edges {
                    let mut found = false;
                    for sig in pkgs[*to].get_oracle_sigs() {
                        if sig == sig_.clone() {
                            found = true
                        }
                    }
                    if !found {
                        return Err(TypeCheckError::TypeCheck(format!(
                            "couldn't find signature for {:?} in package {:?} with id {:}",
                            sig_, pkgs[*to], to
                        )));
                    }
                }

                // 2. check exports exists
                for (id, sig) in exports {
                    if !pkgs[*id].get_oracle_sigs().contains(sig) {
                        return Err(TypeCheckError::TypeCheck(format!(
                            "signature {:?} is not in package {:?} with index {:}",
                            sig,
                            pkgs[*id].clone(),
                            id
                        )));
                    }
                }

                // 3. check all package instances
                for (id, pkg) in pkgs.clone().into_iter().enumerate() {
                    scope.enter();
                    for (from, _, sig) in edges {
                        if *from == id {
                            scope.declare(
                                Identifier::new_scalar(sig.name.as_str()),
                                Type::Oracle(
                                    sig.args.clone().into_iter().map(|(_, tipe)| tipe).collect(),
                                    Box::new(sig.tipe.clone()),
                                ),
                            )?;
                        }
                    }
                    let result = pkg.typecheck(scope)?;
                    scope.leave();

                    result
                }

                Ok(())
            }
        }
    }
}
