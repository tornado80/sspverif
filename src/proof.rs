use std::collections::HashMap;

use crate::{
    expressions::Expression,
    package::{Composition, Package},
    types::Type,
};

pub trait Resolver<T> {
    fn resolve(&self, name: &str) -> Option<&T>;
}

pub trait Named {
    fn as_name(&self) -> &str;
}

pub struct SliceResolver<'a, T>(pub &'a [T]);

impl<'a, T: Named> Resolver<T> for SliceResolver<'a, T> {
    fn resolve(&self, name: &str) -> Option<&T> {
        self.0.iter().find(|v| v.as_name() == name)
    }
}

macro_rules! impl_Named {
    ($tipe:ident) => {
        impl Named for $tipe {
            fn as_name(&self) -> &str {
                &self.name
            }
        }
    };
}

impl_Named!(Package);
impl_Named!(Composition);
impl_Named!(GameInstance);
impl_Named!(Assumption);
//impl_Named!(Reduction);
//impl_Named!(Equivalence);

impl<'a> Resolver<Expression> for SliceResolver<'a, (String, Expression)> {
    fn resolve(&self, name: &str) -> Option<&Expression> {
        self.0
            .iter()
            .find(|(item_name, _)| item_name == name)
            .map(|(_, v)| v)
    }
}

////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub struct GameInstance {
    name: String,
    game_name: String,
    types: Vec<(Type, Type)>,
    consts: Vec<(String, Expression)>,
}

impl GameInstance {
    pub fn new(
        name: String,
        game_name: String,
        types: Vec<(Type, Type)>,
        consts: Vec<(String, Expression)>,
    ) -> GameInstance {
        GameInstance {
            name,
            game_name,
            types,
            consts,
        }
    }
    pub fn as_name(&self) -> &str {
        &self.name
    }

    pub fn as_consts(&self) -> &[(String, Expression)] {
        &self.consts
    }

    pub fn as_game_name(&self) -> &str {
        &self.game_name
    }
}

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
}

// Equivalence contains the composisitions/games and the invariant data,
// whereas the pure Equivalence just contains the names and file paths.
// TODO: explore if we can keep references to the games in the project hashmap
#[derive(Debug, Clone)]
pub struct Equivalence {
    pub left_name: String,
    pub right_name: String,

    pub invariant: (),

    // TODO The value should be a ProofTreeSpec, bvut we don't parse that yet I think
    pub trees: (),
}

// TODO: add a HybridArgument variant
#[derive(Debug, Clone)]
pub enum GameHop {
    Reduction(Reduction),
    Equivalence(Equivalence),
}

#[derive(Clone, Debug)]
pub struct Proof {
    name: String,
    consts: Vec<(String, Type)>,
    instances: Vec<GameInstance>,
    assumptions: Vec<Assumption>,
    game_hops: Vec<GameHop>,
}

impl Proof {
    pub fn new(
        name: String,
        consts: Vec<(String, Type)>,
        instances: Vec<GameInstance>,
        assumptions: Vec<Assumption>,
        game_hops: Vec<GameHop>,
    ) -> Proof {
        Proof {
            name,
            consts,
            instances,
            assumptions,
            game_hops,
        }
    }

    pub fn as_name(&self) -> &str {
        return &self.name;
    }

    pub fn game_hops(&self) -> &[GameHop] {
        return &self.game_hops;
    }
}
