use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{OracleDef, OracleSig, Package, PackageInstance};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashMap;

use crate::{block, fncall};

pub fn mod_prf(params: &HashMap<String, String>) -> PackageInstance {
    PackageInstance {
        name: "mod-prf".to_string(),
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
            state: vec![],
            oracles: vec![OracleDef {
                sig: OracleSig {
                    name: "Eval".to_string(),
                    args: vec![("msg".to_string(), Type::new_bits("*"))],
                    tipe: Type::new_bits("*"),
                },
                code: block! {
                    Statement::Assign(Identifier::new_scalar("k"), Expression::OracleInvoc("Get".to_string(), vec![])), // TODO figure out why the macro doesn't work (and why it's a macro and not a function)
                    Statement::Return(Some(fncall! { "f",
                                                      Identifier::new_scalar("k").to_expression(),
                                                      Identifier::new_scalar("msg").to_expression()
                    }))
                },
            }],
        },
    }
}
