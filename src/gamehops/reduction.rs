use crate::{parser::reduction::NewReductionMapping, project::error::Result, proof::Proof};
use miette::Diagnostic;
use thiserror::Error;

/*
approach:

1. find the diff of left/right games and assumptions, recoding the path of signatures
2. for both left and right:
2.1. in the game, walk the path given by these signatures
2.2. check that the subgame starting by that root is identical


22-09-21 conceptualization
1. find diffs
2. check that diffs are the same package and params
    -> actually it might make sense to make this a separate function
3. in the game hop games, walk back the paths (diff->roots) from the assumption
4. use these as roots to a new composition (both left and right) and generate that (take care of exports)
5. compare to assumption

- a lot of this is comparing parts of the composition. Maybe we should add that as a function on the composition.
- what makes these comparisons tricky is that they don't need to be equal, they just need to be at least as strict as the assumption. It's okay if it offers less oracles to the adversary.
  -> this only concerns the exports


impl Composition {
    fn
}
 */

#[derive(Clone, Debug)]
pub struct Mapping {
    game_inst_name: String,
    assumption_game_inst_name: String,

    // these also need validation
    // but let's not resolve them
    pkg_maps: Vec<(String, String)>,
}

impl Mapping {
    pub fn new(
        assumption_game_inst_name: String,
        game_inst_name: String,
        pkg_maps: Vec<(String, String)>,
    ) -> Mapping {
        Mapping {
            game_inst_name,
            assumption_game_inst_name,
            pkg_maps,
        }
    }

    pub fn as_game_inst_name(&self) -> &str {
        &self.game_inst_name
    }

    pub fn as_assumption_game_inst_name(&self) -> &str {
        &self.assumption_game_inst_name
    }

    pub fn pkg_maps(&self) -> &[(String, String)] {
        &self.pkg_maps
    }
}

#[derive(Debug, Clone)]
pub struct Assumption {
    pub name: String,
    pub left_name: String,
    pub right_name: String,
}

#[derive(Debug, Clone)]
pub struct Reduction {
    left: Mapping,
    right: Mapping,

    assumption_name: String,
}

impl Reduction {
    pub fn new(left: Mapping, right: Mapping, assumption_name: String) -> Self {
        Self {
            left,
            right,
            assumption_name,
        }
    }

    pub fn left(&self) -> &Mapping {
        &self.left
    }

    pub fn right(&self) -> &Mapping {
        &self.right
    }

    pub fn assumption_name(&self) -> &str {
        &self.assumption_name
    }
}

#[derive(Debug, Clone)]
pub struct NewReduction<'a> {
    left: NewReductionMapping<'a>,
    right: NewReductionMapping<'a>,

    assumption_name: String,
}

impl<'a> NewReduction<'a> {
    pub fn new(
        left: NewReductionMapping<'a>,
        right: NewReductionMapping<'a>,
        assumption_name: String,
    ) -> Self {
        Self {
            left,
            right,
            assumption_name,
        }
    }

    pub fn left(&self) -> &NewReductionMapping<'a> {
        &self.left
    }

    pub fn right(&self) -> &NewReductionMapping<'a> {
        &self.right
    }

    pub fn assumption_name(&self) -> &str {
        &self.assumption_name
    }
}

#[derive(Debug, Error, Diagnostic)]
pub enum ReductionError {}
