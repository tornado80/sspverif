use crate::types::Type;
use crate::identifier::Identifier;
use crate::scope::Scope;
use crate::errors::TypeCheckError;
use crate::statement::{TypedCodeBlock, CodeBlock};
use crate::smtgen::SmtExpr;

use std::collections::HashMap;

/*
 * Next Steps:
 * - type check
 * - normalize/canonicalize nested composition
 * - usable constructors
 * - extract SMT-LIB
 * - pretty-print: both text-only and cryptocode
 */

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
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(),TypeCheckError> {
        let OracleDef{
            sig: OracleSig{name: _name, args, tipe},
            code
        } = self;
        scope.enter();
        for (name, ntipe) in args {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        };
        let code_block = TypedCodeBlock{
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
    pub fn typecheck(&self, scope: &mut Scope) -> Result<(),TypeCheckError> {
        let Package{ params, state, oracles } = self;
        //println!("scope in package typecheck: {:?}", scope);

        scope.enter();
        for (name, ntipe) in params {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        };
        for (name, ntipe) in state {
            scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
        };

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
        edges: Vec<(usize, usize, OracleSig)>,  // (from, to, oraclesig)
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
    pub fn state_smt(&self) -> Vec<SmtExpr> {
        match &self {
            PackageInstance::Atom{pkg, name, ..} => {
                let mut tmp = vec![SmtExpr::Atom(format!("mk-state-{}", name))];

                for (id, tipe) in pkg.clone().state {
                    tmp.push(SmtExpr::List(vec![
                        SmtExpr::Atom(format!("state-{}-{}", name, id)),
                        tipe.into(),
                    ]))
                }

                vec![
                    SmtExpr::List(vec![
                        SmtExpr::Atom("declare-datatype".to_string()),
                        SmtExpr::Atom(format!("State_{}", name)),
                        SmtExpr::List(vec![
                            SmtExpr::List(tmp)
                        ])
                    ])
                ]
            },
            PackageInstance::Composition{pkgs, name, ..} => {

                // 1. each package in composition
                let mut states: Vec<SmtExpr> = pkgs.clone().iter()
                    .map(|x|  x.state_smt())
                    .flatten()
                    .collect();


                // 2. composed state
                let mut tmp = vec![
                    SmtExpr::Atom(format!("mk-state-composition-{}", name))
                ];

                for pkg in pkgs {
                    let name = match pkg {
                        PackageInstance::Atom{name, ..}        => name,
                        PackageInstance::Composition{name, ..} => name,
                    };

                    tmp.push(SmtExpr::List(vec![
                        SmtExpr::Atom(format!("state-{}", name)),
                        SmtExpr::Atom(format!("State_{}", name)),
                    ]));
                }

                states.push(SmtExpr::List(vec![
                    SmtExpr::Atom("declare-datatype".to_string()),
                    SmtExpr::Atom(format!("State_composition-{}", name)),
                    SmtExpr::List(vec![
                        SmtExpr::List(tmp)
                    ])
                ]));

                states
            }
        }
    }


    /*
    (declare-datatype Return_key_get (
        (mk-return-key-get         (return-key-get-state State_key)
                                    (return-key_get-value Bits_n))
        (mk-abort-key-get)
    ))


     */
    pub fn return_smt(&self) -> Vec<SmtExpr> {
        match &self {
            PackageInstance::Atom{pkg, name, ..} => {
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
                        constructor.push(
                            SmtExpr::List(vec![
                                SmtExpr::Atom(format!("return-{}-{}-value", name, osig.name)),
                                osig.tipe.into(),
                            ])
                        );
                    }


                    smts.push(
                        SmtExpr::List(vec![
                            SmtExpr::Atom("declare-datatype".to_string()),
                            SmtExpr::Atom(format!("Return_{}_{}", name, osig.name)),
                            SmtExpr::List(vec![
                                SmtExpr::List(constructor),
                                SmtExpr::List(vec![
                                    SmtExpr::Atom(format!("mk-abort-{}-{}", name, osig.name)),
                                ])
                            ]),
                        ]))
                }
                smts
            },
            PackageInstance::Composition{pkgs, name, ..} => {

                // 1. each package in composition
                pkgs.clone().iter()
                    .map(|x|  x.return_smt())
                    .flatten()
                    .collect()
            }
        }
    }



    pub fn get_pkg(&self) -> Package {
        match self {
            PackageInstance::Atom{pkg, ..} => pkg.clone(),
            _ => panic!(),
        }
    }

    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        match self {
            PackageInstance::Atom{pkg, ..} => {
                pkg.oracles.clone()
                    .into_iter()
                    .map(|d| d.sig)
                    .collect()
            },
            PackageInstance::Composition{exports, ..} => {
                exports.into_iter()
                    .map(|(_, sig)| sig.clone())
                    .collect()
            }
        }
    }

    pub fn typecheck(&self, scope: &mut Scope) -> Result<(), TypeCheckError> {
        match self {
            PackageInstance::Atom{pkg, .. } => {
                // TODO also check params
                pkg.typecheck(scope)
            },
            PackageInstance::Composition{pkgs, edges, exports, ..} => {

                // 1. check signature exists in edge destination
                for (_, to, sig_) in edges {
                    let mut found = false;
                    for sig in pkgs[to.clone()].get_oracle_sigs() {
                        if sig == sig_.clone() {
                            found = true
                        }
                    }
                    if !found {
                        return Err(TypeCheckError::TypeCheck(format!("couldn't find signature for {:?} in package {:?} with id {:}", sig_, pkgs[to.clone()], to)))
                    }
                }

                // 2. check exports exists
                for (id, sig) in exports {
                    if !pkgs[id.clone()].get_oracle_sigs().contains(sig) {
                        return Err(TypeCheckError::TypeCheck(format!("signature {:?} is not in package {:?} with index {:}", sig, pkgs[id.clone()].clone(), id)))
                    }
                }

                // 3. check all package instances
                for (id, pkg) in pkgs.clone().into_iter().enumerate() {
                    scope.enter();
                    for (from, _, sig) in edges {
                        if from.clone() == id {
                            scope.declare(
                                Identifier::new_scalar(sig.name.as_str()),
                                Type::Oracle(
                                    sig.args.clone()
                                        .into_iter()
                                        .map(|(_, tipe)| Box::new(tipe)).collect(),
                                    Box::new(sig.tipe.clone()))
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
