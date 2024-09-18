pub mod dispatch_oracle;
mod lemma;
pub mod oracle;
pub mod partial_oracle;

pub use dispatch_oracle::DispatchOraclePattern;
pub use oracle::{OraclePattern, ORACLE_ARG_GAME_STATE, ORACLE_ARG_INTERMEDIATE_STATE};
pub use partial_oracle::PartialOraclePattern;

use crate::{writers::smt::exprs::SmtExpr, writers::smt::sorts::SmtSort};

pub trait FunctionPattern {
    type ReturnSort: SmtSort;

    fn function_name(&self) -> String;
    fn function_args(&self) -> Vec<(String, SmtExpr)>;
    fn function_return_sort(&self) -> Self::ReturnSort;

    fn define_fun<B: Into<SmtExpr>>(&self, body: B) -> SmtExpr {
        (
            "define-fun",
            self.function_name(),
            SmtExpr::List(
                self.function_args()
                    .into_iter()
                    .map(|pair| -> SmtExpr { pair.into() })
                    .collect(),
            ),
            self.function_return_sort(),
            body,
        )
            .into()
    }

    fn define_fun_rec<B: Into<SmtExpr>>(&self, body: B) -> SmtExpr {
        (
            "define-fun-rec",
            self.function_name(),
            SmtExpr::List(
                self.function_args()
                    .into_iter()
                    .map(|pair| -> SmtExpr { pair.into() })
                    .collect(),
            ),
            self.function_return_sort(),
            body,
        )
            .into()
    }

    fn call(&self, args: &[SmtExpr]) -> SmtExpr {
        let mut call: Vec<SmtExpr> = vec![self.function_name().into()];
        call.extend(args.iter().cloned());
        SmtExpr::List(call)
    }
}
