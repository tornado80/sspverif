use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{OracleDef, OracleSig, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashMap;

use crate::block;

pub fn key_pkg(params: &HashMap<String, String>) -> PackageInstance {
    PackageInstance {
        name: "key".to_string(),
        params: params.clone(),
        pkg: Package {
            params: vec![("n".to_string(), Type::new_scalar("int"))],
            state: vec![("k".to_string(), Type::Maybe(Box::new(Type::new_bits("n"))))],
            imports: vec![],
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
                                Statement::Sample(Identifier::new_scalar("k_sample"), None, Type::new_bits("n"),
                                ),
                                Statement::Assign(Identifier::new_scalar("k"), None,
                                                  Expression::Some(Box::new(Identifier::new_scalar("k_sample").to_expression())),
                                )
                            },
                            block! {
                                Statement::Abort
                            },
                        )
                    },
                },
                OracleDef {
                    sig: OracleSig {
                        name: "Get".to_string(),
                        args: vec![],
                        tipe: Type::new_bits("n"),
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
                        Statement::Assign(Identifier::new_scalar("k_unwrapped"), None, Expression::Unwrap(Box::new(Identifier::new_scalar("k").to_expression()))),
                        Statement::Return(Some(Identifier::new_scalar("k_unwrapped").to_expression()))
                    },
                },
            ],
        },
    }
}
