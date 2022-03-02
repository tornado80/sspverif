use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{OracleDef, OracleSig, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashMap;

use crate::{block, fncall};

pub fn mono_prf(params: &HashMap<String, String>) -> PackageInstance {
    PackageInstance {
        name: "mono-prf".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![
                ("n".to_string(), Type::new_scalar("int")),
                (
                    "f".to_string(),
                    Type::new_fn(
                        vec![Type::new_bits("n"), Type::new_bits("*")],
                        Type::new_bits("*"),
                    ),
                ),
            ],
            state: vec![("k".to_string(), Type::Maybe(Box::new(Type::new_bits("n"))))],
            oracles: vec![
                OracleDef {
                    sig: OracleSig {
                        name: "Set".to_string(),
                        args: vec![("k_".to_string(), Type::new_bits("n"))],
                        tipe: Type::Empty,
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::None(Type::new_bits("n")),
                            ]),
                            block! {
                                Statement::Assign(Identifier::new_scalar("k_sample"),
                                                Expression::Sample(Type::new_bits("n")),
                                ),
                                Statement::Assign(Identifier::new_scalar("k"),
                                                Expression::Some(Box::new(Identifier::new_scalar("k_sample").to_expression())),
                                )},
                            block! {
                                Statement::Abort
                            },
                        )
                    },
                },
                OracleDef {
                    sig: OracleSig {
                        name: "Eval".to_string(),
                        args: vec![("msg".to_string(), Type::new_bits("*"))],
                        tipe: Type::new_bits("*"),
                    },
                    code: block! {
                        Statement::IfThenElse(
                            Expression::new_equals(vec![
                                &(Identifier::new_scalar("k").to_expression()),
                                &Expression::None(Type::new_bits("n")),
                            ]),
                            block! {Statement::Abort},
                            block! {},
                        ),
                        Statement::Return(Some(fncall! { "f",
                                                          Expression::Unwrap(Box::new(Identifier::new_scalar("k").to_expression())),
                                                          Identifier::new_scalar("msg").to_expression()
                        }))
                    },
                },
            ],
        },
    }
}
