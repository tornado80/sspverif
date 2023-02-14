use std::collections::HashMap;

use crate::{
    expressions::Expression,
    package::{Composition, Package},
    parser::Rule,
    project::{GameHop, Reduction},
    proof::Proof,
    types::Type,
};

use pest::{
    iterators::{Pair, Pairs},
    Span,
};

use crate::project::{Assumption, Equivalence};

use super::common;
use super::error::{Error, Result};

pub fn handle_proof(
    ast: Pair<Rule>,
    pkgs: &HashMap<String, Package>,
    games: &HashMap<String, Composition>,
) -> Result<(String, Proof)> {
    let mut iter = ast.into_inner();
    let name = iter.next().unwrap().as_str();
    let proof_ast = iter.next().unwrap();

    let mut assumptions = vec![];
    let mut game_hops = vec![];
    let mut instances = vec![];
    let mut consts = vec![];

    for ast in proof_ast.into_inner() {
        match ast.as_rule() {
            Rule::const_decl => {
                consts.push(common::handle_const_decl(ast));
            }
            Rule::assumptions => {
                handle_assumptions(&mut assumptions, ast.into_inner(), &instances)?;
            }
            Rule::game_hops => {
                handle_game_hops(&mut game_hops, ast.into_inner(), &assumptions)?;
            }
            Rule::instance_decl => {
                instances.push(handle_instance_decl(ast, &consts, pkgs, games)?);
            }
            otherwise => unreachable!("found {:?} in proof", otherwise),
        }
    }

    Ok((
        name.to_string(),
        Proof {
            name: name.to_string(),
        },
    ))
}

fn handle_instance_decl<'a>(
    ast: Pair<Rule>,
    proof_consts: &[(String, Type)],
    pkgs: &HashMap<String, Package>,
    games: &'a HashMap<String, Composition>,
) -> Result<GameInstance<'a>> {
    let span = ast.as_span();

    let mut ast = ast.into_inner();

    let inst_name = ast.next().unwrap().as_str();
    let game_ast = ast.next().unwrap();
    let game_span = game_ast.as_span();
    let game_name = game_ast.as_str();
    let body_ast = ast.next().unwrap();

    let (types, consts) =
        handle_instance_assign_list(inst_name, proof_consts, body_ast, pkgs, games)?;

    let game = games
        .get(game_name)
        .ok_or(Error::UndefinedGame(game_name.to_string()).with_span(game_span))?;

    let game_inst = GameInstance {
        inst_name: inst_name.to_string(),
        game,
        types,
        consts,
    };

    game_inst.check_consts(span)?;

    Ok(game_inst)
}

pub fn handle_params_def_list(
    ast: Pair<Rule>,
    inst_name: &str,
    game: &Composition,
) -> Result<Vec<(String, Expression)>> {
    ast.into_inner()
        .map(|inner| {
            //let inner = inner.into_inner().next().unwrap();

            let mut inner = inner.into_inner();
            let name_ast = inner.next().unwrap();
            let name_span = name_ast.as_span();
            let name = name_ast.as_str();

            if !game.consts.iter().any(|(const_name, _)| const_name == name) {
                return Err(Error::GameConstParameterUndeclared {
                    game_name: game.name.clone(),
                    inst_name: inst_name.to_string(),
                    param_name: name.to_string(),
                }
                .with_span(name_span));
            }

            let left = inner.next().unwrap().as_str();
            let right = inner.next().unwrap();
            let right = common::handle_expression(right);

            Ok((left.to_owned(), right))
        })
        .collect()
}

pub struct GameInstance<'a> {
    inst_name: String,
    game: &'a Composition,
    types: Vec<(Type, Type)>,
    consts: Vec<(String, Expression)>,
}

impl<'a> GameInstance<'a> {
    fn check_types(&self) -> Result<()> {
        // TODO deferred until the game actually has a place for type paramenters
        Ok(())
    }

    fn check_consts(&self, span: Span) -> Result<()> {
        let mut inst_const_names: Vec<_> = self
            .consts
            .iter()
            .map(|(name, _)| name.to_string())
            .collect();
        inst_const_names.sort();

        let mut game_const_names: Vec<_> = self
            .game
            .consts
            .iter()
            .map(|(name, _)| name.to_string())
            .collect();
        game_const_names.sort();

        if inst_const_names != game_const_names {
            return Err(Error::GameConstParameterMismatch {
                game_name: self.game.name.clone(),
                inst_name: self.inst_name.clone(),
                bound_params: self.consts.clone(),
                game_params: self.game.consts.clone(),
            }
            .with_span(span));
        }

        Ok(())
    }
}

fn handle_instance_assign_list(
    inst_name: &str,
    proof_consts: &[(String, Type)],
    ast: Pair<Rule>,
    pkgs: &HashMap<String, Package>,
    games: &HashMap<String, Composition>,
) -> Result<(Vec<(Type, Type)>, Vec<(String, Expression)>)> {
    let ast = ast.into_inner();

    let mut types = vec![];
    let mut consts = vec![];

    for ast in ast {
        match ast.as_rule() {
            Rule::types_def => {
                let ast = ast.into_inner().next().unwrap();
                types.extend(common::handle_types_def_list(ast, inst_name)?);
            }
            Rule::params_def => {
                consts.extend(common::handle_params_def_list(ast, proof_consts)?);
            }
            otherwise => {
                unreachable!("unexpected {:?} at {:?}", otherwise, ast.as_span())
            }
        }
    }

    Ok((types, consts))
}

fn handle_assumptions(
    dest: &mut Vec<(String, Assumption)>,
    ast: Pairs<Rule>,
    instances: &[GameInstance],
) -> Result<()> {
    for pair in ast {
        let (name, left, right) = handle_string_triplet(&mut pair.into_inner());
        let assumption = Assumption { left, right };
        dest.push((name, assumption));
    }

    Ok(())
}

fn handle_game_hops(
    dest: &mut Vec<GameHop>,
    ast: Pairs<Rule>,
    assumptions: &[(String, Assumption)],
) -> Result<()> {
    for hop_ast in ast {
        let game_hop = match hop_ast.as_rule() {
            Rule::equivalence => handle_equivalence(hop_ast),
            Rule::reduction => handle_reduction(hop_ast, assumptions)?,
            otherwise => unreachable!("found {:?} in game_hops", otherwise),
        };
    }

    Ok(())
}

fn handle_equivalence(ast: Pair<Rule>) -> Vec<GameHop> {
    let mut ast = ast.into_inner();
    let (left, right) = handle_string_pair(&mut ast);

    let mut equivalences = vec![];

    let x: Vec<_> = ast.map(handle_equivalence_oracle).collect();

    let trees: HashMap<_, _> = x
        .iter()
        .cloned()
        .map(|(oracle_name, _, lemmas)| (oracle_name, lemmas))
        .collect();
    let inv_paths: Vec<_> = x
        .iter()
        .map(|(_, inv_paths, _)| inv_paths)
        .flatten()
        .collect();

    // TODO once we actually support more than one file, insert it here
    let invariant_path = inv_paths[0].to_owned();

    equivalences.push(GameHop::Equivalence(Equivalence {
        left,
        right,
        invariant_path,
        trees,
    }));

    equivalences
}

fn handle_equivalence_oracle(ast: Pair<Rule>) -> (String, Vec<String>, Vec<(String, Vec<String>)>) {
    let span = ast.as_span();
    let mut ast = ast.into_inner();
    let oracle_name = ast.next().unwrap().as_str().to_string();
    let invariant_paths = handle_invariant_spec(next_pairs(&mut ast));
    let lemmas = handle_lemmas_spec(next_pairs(&mut ast));

    (oracle_name, invariant_paths, lemmas)
}

fn handle_invariant_spec(ast: Pairs<Rule>) -> Vec<String> {
    ast.map(|ast| ast.as_str().to_string()).collect()
}

fn handle_lemmas_spec(ast: Pairs<Rule>) -> Vec<(String, Vec<String>)> {
    ast.map(handle_lemma_line).collect()
}

fn handle_lemma_line(ast: Pair<Rule>) -> (String, Vec<String>) {
    let mut ast = ast.into_inner();
    let name = next_str(&mut ast).to_string();
    let deps = ast.map(|dep| dep.as_str().to_string()).collect();

    (name, deps)
}

fn handle_reduction(ast: Pair<Rule>, assumptions: &[(String, Assumption)]) -> Result<Vec<GameHop>> {
    let mut ast = ast.into_inner();
    let (left_name, right_name) = handle_string_pair(&mut ast);
    let reduction =
        handle_reduction_body(next_pair(&mut ast), assumptions, &left_name, &right_name)?;

    Ok(vec![GameHop::Reduction(reduction)])
}

fn handle_reduction_body(
    ast: Pair<Rule>,
    assumptions: &[(String, Assumption)],
    left_name: &str,
    right_name: &str,
) -> Result<Reduction> {
    let mut ast = ast.into_inner();
    let assumptions_ast = ast.next().unwrap();
    let assumptions_span = assumptions_ast.as_span();
    let mut assumptions_ast = assumptions_ast.into_inner();
    let assumption_name = next_str(&mut assumptions_ast);

    // check that assumption_name turns up in the assumptions list
    // and fetch the assumption definition
    let (_, assumption) = assumptions
        .iter()
        .find(|(name, _)| name == assumption_name)
        .ok_or(
            Error::ReductionMappingMismatch {
                place: "assumptions definition".to_string(),
            }
            .with_span(assumptions_span),
        )?;

    let map1_ast = ast.next().unwrap();
    let map2_ast = ast.next().unwrap();

    let (game_name1, assumption_game_name1, mapping1, is_left1) =
        handle_mapspec(map1_ast, &assumption, left_name, right_name)?;
    let (game_name2, assumption_game_name2, mapping2, is_left2) =
        handle_mapspec(map2_ast, &assumption, left_name, right_name)?;

    // mappings distinct
    if game_name1 == game_name2 {
        // TODO reutrn err
    }

    if assumption_game_name1 == assumption_game_name2 {
        // TODO reutrn err
    }

    assert_eq!(
        is_left1, is_left2,
        "the previous branch should have prevented this from ever occuring"
    );

    let (left, leftmap, right, rightmap) = if is_left1 {
        (game_name1, mapping1, game_name2, mapping2)
    } else {
        (game_name2, mapping2, game_name1, mapping1)
    };

    let assumption = assumption_name.to_string();

    let reduction = Reduction {
        left,
        right,
        assumption,
        leftmap,
        rightmap,
    };

    Ok(reduction)
}

fn handle_mapspec(
    ast: Pair<Rule>,
    assumption: &Assumption,
    left_name: &str,
    right_name: &str,
) -> Result<(String, String, Vec<(String, String)>, bool)> {
    let span = ast.as_span();
    let mut ast = ast.into_inner();

    let (name1, name2) = handle_string_pair(&mut ast);

    let left1 = name1 == left_name;
    let left2 = name2 == left_name;
    let right1 = name1 == right_name;
    let right2 = name2 == right_name;

    // which way to parse (assumpt: game or game: assumpt)
    let (game_name, assumption_game_name, game_is_left) = if left1 {
        (name1, name2, true)
    } else if left2 {
        (name2, name1, false)
    } else if right1 {
        (name1, name2, false)
    } else if right2 {
        (name2, name1, true)
    } else {
        return Err(Error::ReductionMappingMismatch {
            place: "game hop definition".to_string(),
        }
        .with_span(span));
    };

    let is_left_assumption_game = assumption_game_name == assumption.left;
    let is_right_assumption_game = assumption_game_name == assumption.right;

    if !(is_left_assumption_game || is_right_assumption_game) {
        // TODO reutrn an error
    }

    let map_block_pair = ast.next().unwrap();
    let mappings = map_block_pair
        .into_inner()
        .map(|pair| {
            // canonicalize mapping direction
            if game_is_left {
                handle_string_pair(&mut pair.into_inner())
            } else {
                let (game_name, assumption_game_name) = handle_string_pair(&mut pair.into_inner());
                (assumption_game_name, game_name)
            }
        })
        .collect();

    Ok((
        game_name,
        assumption_game_name,
        mappings,
        is_left_assumption_game,
    ))
}

fn handle_string_triplet(ast: &mut Pairs<Rule>) -> (String, String, String) {
    let strs: Vec<_> = ast.take(3).map(|str| str.as_str()).collect();

    (
        strs[0].to_string(),
        strs[1].to_string(),
        strs[2].to_string(),
    )
}

fn handle_string_pair(ast: &mut Pairs<Rule>) -> (String, String) {
    let strs: Vec<_> = ast.take(2).map(|str| str.as_str()).collect();

    (strs[0].to_string(), strs[1].to_string())
}

fn next_pairs<'a>(ast: &'a mut Pairs<Rule>) -> Pairs<'a, Rule> {
    ast.next().unwrap().into_inner()
}

fn next_pair<'a>(ast: &'a mut Pairs<Rule>) -> Pair<'a, Rule> {
    ast.next().unwrap()
}

fn next_pairs_with_span<'a>(ast: &'a mut Pairs<Rule>) -> (Pairs<'a, Rule>, Span<'a>) {
    let pair = ast.next().unwrap();
    (pair.clone().into_inner(), pair.as_span())
}

fn next_str<'a>(ast: &'a mut Pairs<Rule>) -> &'a str {
    ast.next().unwrap().as_str()
}
