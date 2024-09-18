use crate::writers::smt::{
    exprs::SmtExpr,
    patterns::{FunctionPattern, GameStatePattern},
    sorts::SmtBool,
};

struct LemmaFunction<'a> {
    left_game_inst_name: &'a str,
    right_game_inst_name: &'a str,
    oracle_name: &'a str,
}

impl<'a> FunctionPattern for LemmaFunction<'a> {
    type ReturnSort = SmtBool;

    fn function_name(&self) -> String {
        let Self {
            left_game_inst_name,
            right_game_inst_name,
            oracle_name,
        } = self;
        format!("lemma-auto-{left_game_inst_name}-{right_game_inst_name}-{oracle_name}")
    }

    fn function_args(&self) -> Vec<(String, SmtExpr)> {
        let _state_left_pattern = GameStatePattern {
            game_inst_name: self.left_game_inst_name,
        };
        vec![]
    }

    fn function_return_sort(&self) -> Self::ReturnSort {
        todo!()
    }
}
