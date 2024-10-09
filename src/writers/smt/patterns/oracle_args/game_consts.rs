use crate::writers::smt::patterns::game_consts::GameConstsSort;

use super::*;

pub struct GameConstsPattern<'a> {
    pub game_name: &'a str,
}

impl<'a> OracleArgPattern for GameConstsPattern<'a> {
    type Sort = GameConstsSort<'a>;
    type Variant = ();

    fn global_const_name(&self, game_inst_name: &str, _variant: &()) -> String {
        format!("<<game-state-{game_inst_name}>>")
    }

    fn local_arg_name(&self) -> String {
        "<game-state>".to_string()
    }

    fn sort(&self) -> Self::Sort {
        GameConstsSort {
            game_name: self.game_name,
        }
    }
}
