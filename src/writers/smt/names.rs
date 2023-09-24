use super::exprs::SmtExpr;

pub(crate) fn oracle_function_name(game_name: &str, inst_name: &str, oracle_name: &str) -> String {
    format!("oracle-{game_name}-{inst_name}-{oracle_name}")
}

pub(crate) fn return_sort_name(game_name: &str, inst_name: &str, oracle_name: &str) -> String {
    format!("Return_{game_name}_{inst_name}_{oracle_name}")
}

pub(crate) fn return_constructor_name(
    game_name: &str,
    inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("mk-return-{game_name}-{inst_name}-{oracle_name}")
}

pub(crate) fn return_constructor_abort_name(
    game_name: &str,
    inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("mk-abort-{game_name}-{inst_name}-{oracle_name}")
}

pub(crate) fn return_selector_state_name(
    game_name: &str,
    inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("return-{game_name}-{inst_name}-{oracle_name}-state")
}

pub(crate) fn return_selector_state_length_name(
    game_name: &str,
    inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("return-{game_name}-{inst_name}-{oracle_name}-state-length")
}

pub(crate) fn return_selector_is_abort_name(
    game_name: &str,
    inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("return-{game_name}-{inst_name}-{oracle_name}-is-abort")
}

pub(crate) fn return_selector_value_name(
    game_name: &str,
    inst_name: &str,
    oracle_name: &str,
) -> String {
    format!("return-{game_name}-{inst_name}-{oracle_name}-value")
}

pub(crate) fn gamestate_sort_name(game_name: &str) -> String {
    format!("CompositionState-{game_name}")
}

pub(crate) fn gamestate_selector_pkgstate_name(game_name: &str, inst_name: &str) -> String {
    format!("composition-pkgstate-{game_name}-{inst_name}")
}

pub(crate) fn pkgstate_sort_name(game_name: &str, inst_name: &str) -> String {
    format!("State_{game_name}_{inst_name}")
}

pub(crate) fn pkgstate_selector_name(game_name: &str, inst_name: &str, field_name: &str) -> String {
    format!("state-{game_name}-{inst_name}-{field_name}")
}

pub(crate) fn pkgstate_constructor_name(game_name: &str, inst_name: &str) -> String {
    format!("mk-state-{game_name}-{inst_name}")
}

pub(crate) fn var_selfstate_name() -> String {
    "__self_state".to_string()
}

pub(crate) fn var_globalstate_name() -> String {
    "__global_state".to_string()
}

pub(crate) fn var_ret_name() -> String {
    "__ret".to_string()
}

pub(crate) fn fn_sample_rand_name<S: Into<SmtExpr>>(game_name: &str, rand_sort: S) -> String {
    format!("__sample-rand-{}-{}", game_name, rand_sort.into())
}

pub(crate) fn oracle_nonsplit_arg_name(oracle_name: &str, arg_name: &str) -> String {
    format!("arg-{oracle_name}-{arg_name}")
}

pub(crate) fn oracle_split_arg_name(game_name: &str, oracle_name: &str, arg_name: &str) -> String {
    format!("arg-{game_name}-{oracle_name}-{arg_name}")
}
