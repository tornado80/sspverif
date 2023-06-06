use super::codeblock::TypedCodeBlock;
use super::errors::TypeCheckError;
use super::scope::Scope;

use crate::package::{OracleDef, OracleSig};

use crate::identifier::Identifier;

pub fn typecheck_odef(odef: &OracleDef, scope: &mut Scope) -> Result<OracleDef, TypeCheckError> {
    let OracleDef {
        sig:
            OracleSig {
                name: _name,
                args,
                tipe,
                ..
            },
        code,
    } = odef;
    scope.enter();
    for (name, ntipe) in args {
        scope.declare(Identifier::new_scalar(name), ntipe.clone())?;
    }
    let code_block = TypedCodeBlock {
        expected_return_type: tipe.clone(),
        block: code.clone(),
    };

    let code_block_with_typed_statements = code_block.typecheck(scope)?;
    scope.leave();

    Ok(OracleDef {
        code: code_block_with_typed_statements.block,
        ..odef.clone()
    })
}
