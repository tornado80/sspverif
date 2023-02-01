use std::collections::HashMap;

use crate::{
    parser::Rule,
    project::{GameHop, Reduction},
};
use pest::{
    iterators::{Pair, Pairs},
    Span,
};

use crate::project::{Assumption, Equivalence};

use super::error::{Error, Result};

pub struct Proof();

pub fn handle_proof(ast: Pair<Rule>) -> Result<(String, Proof)> {
    let mut iter = ast.into_inner();
    let name = iter.next().unwrap().as_str();
    let proof_ast = iter.next().unwrap();

    let mut assumptions = vec![];
    let mut game_hops = vec![];

    for ast in proof_ast.into_inner() {
        match ast.as_rule() {
            Rule::assumptions => {
                handle_assumptions(&mut assumptions, ast.into_inner())?;
            }
            Rule::game_hops => {
                handle_game_hops(&mut game_hops, ast.into_inner(), &assumptions)?;
            }
            otherwise => unreachable!("found {:?} in proof", otherwise),
        }
    }

    Ok((name.to_string(), Proof()))
}

fn handle_assumptions(dest: &mut Vec<(String, Assumption)>, ast: Pairs<Rule>) -> Result<()> {
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
