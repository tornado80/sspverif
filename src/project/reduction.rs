use itertools::Itertools;
use serde_derive::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;

use crate::package::{Composition, Edge, PackageInstance};
use crate::project::Result;

use super::assumption::ResolvedAssumption;
use super::Error;

use crate::proof::{Named, Proof, Reduction, Resolver, SliceResolver};

// TODO: add a HybridArgument variant
#[derive(Debug, Serialize, Deserialize)]
pub enum Direction {
    LeftToRight,
    RightToLeft,
    Unspecified,
}
/*
// TODO: add a HybridArgument variant
#[derive(Debug, Serialize, Deserialize)]
pub struct Reduction {
    pub left: String,
    pub right: String,
    //pub direction: Direction, // unclear if we need it
    pub assumption: String,
    pub leftmap: Vec<(String, String)>,
    pub rightmap: Vec<(String, String)>,
    // we probably have to provide more information here,
    // in order to easily figure out how to perform the rewrite
}
 */

pub struct ResolvedReduction {
    pub left: Composition,
    pub right: Composition,
    pub assumption: ResolvedAssumption,
    pub assumption_name: String,
    pub leftmap: Vec<(usize, usize)>,
    pub rightmap: Vec<(usize, usize)>,
}

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

fn same_package(left: &PackageInstance, right: &PackageInstance) -> bool {
    left.pkg == right.pkg
}

/*

impl ResolvedReduction {
    /// Prove needs to verify four aspects
    /// - Mapping is Valid
    ///   - PackageInstances are only mentioned once
    ///   - Mapping may only occure with the same package type
    /// - Every PackageInstance in the assumptions is mapped
    /// - Every PackageInstance in the game, which is mapped
    ///   only calls other mapped package instances
    /// - The PackageInstances in the games which are *not* mapped need to be identical
    pub fn prove(&self) -> Result<()> {
        let ResolvedReduction {
            left,
            right,
            assumption,
            leftmap,
            rightmap,
            ..
        } = self;

        // apply transformations
        let (ref left, _, _types_left, _samp_left) = crate::transforms::transform_all(&left)?;
        let (ref right, _, _types_right, _samp_right) = crate::transforms::transform_all(&right)?;
        let (ref left_assumption, _, _, _) = crate::transforms::transform_all(&assumption.left)?;
        let (ref right_assumption, _, _, _) = crate::transforms::transform_all(&assumption.right)?;

        // PackageInstances are only mentioned once
        if !(leftmap.iter().map(|(from, _to)| from).all_unique()) {
            return Err(Error::ProofCheck(format!("leftmap has duplicate from")));
        }
        if !(leftmap.iter().map(|(_from, to)| to).all_unique()) {
            return Err(Error::ProofCheck(format!("leftmap has duplicate to")));
        }
        if !(rightmap.iter().map(|(from, _to)| from).all_unique()) {
            return Err(Error::ProofCheck(format!("rightmap has duplicate from")));
        }
        if !(rightmap.iter().map(|(_from, to)| to).all_unique()) {
            return Err(Error::ProofCheck(format!("rightmap has duplicate to")));
        }

        // Mapping may only occure with the same package type
        let mismatches_left: Vec<_> = leftmap
            .iter()
            .filter(|(from, to)| !same_package(&left.pkgs[*from], &left_assumption.pkgs[*to]))
            .map(|(from, to)| {
                format!(
                    "{} and {} have different types",
                    left.pkgs[*from].name, assumption.left.pkgs[*to].name
                )
            })
            .collect();
        if !mismatches_left.is_empty() {
            return Err(Error::ProofCheck(format!(
                "leftmap has incompatible package instances: {}",
                mismatches_left.join(", ")
            )));
        }
        let mismatches_right: Vec<_> = rightmap
            .iter()
            .filter(|(from, to)| !same_package(&right.pkgs[*from], &right_assumption.pkgs[*to]))
            .map(|(from, to)| {
                format!(
                    "{} and {} have different types",
                    right.pkgs[*from].name, assumption.right.pkgs[*to].name
                )
            })
            .collect();
        if !mismatches_right.is_empty() {
            return Err(Error::ProofCheck(format!(
                "rightmap has incompatible package instances: {}",
                mismatches_right.join(", ")
            )));
        }

        // Every PackageInstance in the assumptions is mapped
        if assumption.left.pkgs.len() != leftmap.len() {
            return Err(Error::ProofCheck(format!(
                "Some package instances in leftasusmption are not mapped"
            )));
        }
        if assumption.right.pkgs.len() != rightmap.len() {
            return Err(Error::ProofCheck(format!(
                "Some package instances in rightasusmption are not mapped"
            )));
        }

        // Every PackageInstance in the game, which is mapped
        // only calls other mapped package instances
        for Edge(from, to, _sig) in &left.edges {
            if leftmap.iter().find(|(gameidx, _)| gameidx == to).is_none()
                && !leftmap
                    .iter()
                    .find(|(gameidx, _)| gameidx == from)
                    .is_none()
            {
                return Err(Error::ProofCheck(format!(
                    "Left Game: Mapped package {} calls unmappedpackage {}",
                    left.pkgs[*from].name, left.pkgs[*to].name
                )));
            }
        }
        for Edge(from, to, _sig) in &right.edges {
            if rightmap.iter().find(|(gameidx, _)| gameidx == to).is_none()
                && !rightmap
                    .iter()
                    .find(|(gameidx, _)| gameidx == from)
                    .is_none()
            {
                return Err(Error::ProofCheck(format!(
                    "Right Game: Mapped package {} calls unmappedpackage {}",
                    right.pkgs[*from].name, right.pkgs[*to].name
                )));
            }
        }

        // The PackageInstances in the games which are *not* mapped need to be identical
        let unmapped_left: HashMap<_, _> = left
            .pkgs
            .iter()
            .enumerate()
            .filter(|(i, _)| leftmap.iter().find(|(gameidx, _)| gameidx == i).is_none())
            .map(|(_, pkginst)| (pkginst.name.clone(), pkginst))
            .collect();
        let unmapped_right: HashMap<_, _> = right
            .pkgs
            .iter()
            .enumerate()
            .filter(|(i, _)| rightmap.iter().find(|(gameidx, _)| gameidx == i).is_none())
            .map(|(_, pkginst)| (pkginst.name.clone(), pkginst))
            .collect();

        if HashSet::<_>::from_iter(unmapped_left.keys())
            != HashSet::<_>::from_iter(unmapped_right.keys())
        {
            return Err(Error::ProofCheck(format!(
                "unmapped mapckage instances not equal: {:?} and {:?}",
                unmapped_left.keys(),
                unmapped_right.keys()
            )));
        }

        for name in unmapped_left.keys() {
            if unmapped_left[name] != unmapped_right[name] {
                return Err(Error::ProofCheck(format!(
                    "Packages with name {} have different sort",
                    name
                )));
            }
        }

        Ok(())
    }
}
*/

pub fn verify(red: &Reduction, proof: &Proof) -> Result<()> {
    let left_mapping = red.left();
    let right_mapping = red.right();
    let assumption_name = red.assumption_name();

    // resolve game instances
    let game_instance_resolver = SliceResolver(proof.instances());

    let left = left_mapping.as_game_inst_name();
    let left = game_instance_resolver
        .resolve(left)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {left:?}"
        )))?;
    let right = right_mapping.as_game_inst_name();
    let right = game_instance_resolver
        .resolve(right)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {right:?}"
        )))?;

    let assumption_resolver = SliceResolver(proof.assumptions());
    let assumption = assumption_resolver
        .resolve(assumption_name)
        .ok_or(Error::ProofCheck(format!(
            "could not find assumption {assumption_name:?}"
        )))?;

    let assumption_left = &assumption.left_name;
    let assumption_left = game_instance_resolver
        .resolve(&assumption.left_name)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {assumption_left:?}"
        )))?;

    let assumption_right = &assumption.right_name;
    let assumption_right = game_instance_resolver
        .resolve(&assumption.right_name)
        .ok_or(Error::ProofCheck(format!(
            "could not find game instance {assumption_right:?}"
        )))?;

    let leftmap = left_mapping.pkg_maps();
    let rightmap = right_mapping.pkg_maps();

    // PackageInstances are only mentioned once
    if !(leftmap.iter().map(|(from, _to)| from).all_unique()) {
        return Err(Error::ProofCheck(format!("leftmap has duplicate from")));
    }
    if !(leftmap.iter().map(|(_from, to)| to).all_unique()) {
        return Err(Error::ProofCheck(format!("leftmap has duplicate to")));
    }
    if !(rightmap.iter().map(|(from, _to)| from).all_unique()) {
        return Err(Error::ProofCheck(format!("rightmap has duplicate from")));
    }
    if !(rightmap.iter().map(|(_from, to)| to).all_unique()) {
        return Err(Error::ProofCheck(format!("rightmap has duplicate to")));
    }

    // TODO check that all names are well-defined (or has that already happened?)

    let right_package_resolver = SliceResolver(&right.as_game().pkgs);
    let left_package_resolver = SliceResolver(&left.as_game().pkgs);
    let assumption_right_package_resolver = SliceResolver(&assumption_right.as_game().pkgs);
    let assumption_left_package_resolver = SliceResolver(&assumption_left.as_game().pkgs);

    // Mapping may only occure with the same package type
    let mismatches_left: Vec<_> = leftmap
        .iter()
        .map(|(from, to)| {
            let assumption_left_pkg_inst =
                assumption_left_package_resolver
                    .resolve(from)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {from} in left game {}",
                        assumption_left.as_name()
                    )))?;

            let left_pkg_inst =
                left_package_resolver
                    .resolve(to)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {to} in left assumption game {}",
                        left.as_name()
                    )))?;

            Ok((left_pkg_inst, assumption_left_pkg_inst))
        })
        .filter(|to| match to {
            Ok((from, to)) => !same_package(from, to),
            Err(_) => true,
        })
        .map(|res| {
            res.map(|(from, to)| {
                format!(
                    "{} and {} have different types",
                    from.as_name(),
                    to.as_name()
                )
            })
        })
        .collect::<Result<_>>()?;

    if !mismatches_left.is_empty() {
        return Err(Error::ProofCheck(format!(
            "leftmap has incompatible package instances: {}",
            mismatches_left.join(", ")
        )));
    }

    let mismatches_right: Vec<_> = rightmap
        .iter()
        .map(|(from, to)| {
            let assumption_right_pkg_inst =
                assumption_right_package_resolver
                    .resolve(from)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {from} in right game {}",
                        assumption_right.as_name()
                    )))?;

            let right_pkg_inst =
                right_package_resolver
                    .resolve(to)
                    .ok_or(Error::ProofCheck(format!(
                        "error resolving package {to} in right assumption game {}",
                        right.as_name()
                    )))?;

            Ok((right_pkg_inst, assumption_right_pkg_inst))
        })
        .filter(|to| match to {
            Ok((from, to)) => !same_package(from, to),
            Err(_) => true,
        })
        .map(|res| {
            res.map(|(from, to)| {
                format!(
                    "{} and {} have different types",
                    from.as_name(),
                    to.as_name()
                )
            })
        })
        .collect::<Result<_>>()?;

    if !mismatches_right.is_empty() {
        return Err(Error::ProofCheck(format!(
            "rightmap has incompatible package instances: {}",
            mismatches_right.join(", ")
        )));
    }

    // Every PackageInstance in the assumptions is mapped
    if assumption_left.as_game().pkgs.len() != leftmap.len() {
        return Err(Error::ProofCheck(format!(
            "Some package instances in left assumption are not mapped: {} != {:?}",
            assumption_left.as_game().pkgs.len(),
            leftmap
        )));
    }
    if assumption_right.as_game().pkgs.len() != rightmap.len() {
        return Err(Error::ProofCheck(format!(
            "Some package instances in right assumption are not mapped"
        )));
    }

    // Every PackageInstance in the game, which is mapped
    // only calls other mapped package instances
    for Edge(from, to, _sig) in &left.as_game().edges {
        let from = &left.as_game().pkgs[*from].name;
        let from_is_mapped = leftmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == from)
            .is_some();

        let to = &left.as_game().pkgs[*to].name;
        let to_is_mapped = leftmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == to)
            .is_some();

        if from_is_mapped && !to_is_mapped {
            return Err(Error::ProofCheck(format!(
                "Left Game: Mapped package {from} calls unmappedpackage {to}",
            )));
        }
    }
    for Edge(from, to, _sig) in &right.as_game().edges {
        let from = &right.as_game().pkgs[*from].name;
        let from_is_mapped = rightmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == from)
            .is_some();

        let to = &right.as_game().pkgs[*to].name;
        let to_is_mapped = rightmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == to)
            .is_some();

        if from_is_mapped && !to_is_mapped {
            return Err(Error::ProofCheck(format!(
                "Right Game: Mapped package {from} calls unmappedpackage {to}",
            )));
        }
    }

    // The PackageInstances in the games which are *not* mapped need to be identical
    let unmapped_left: HashSet<_> =
        HashSet::from_iter(left.as_game().pkgs.iter().filter(|pkg_inst| {
            leftmap
                .iter()
                .find(|(_, game_inst_name)| game_inst_name == &pkg_inst.name)
                .is_none()
        }));
    let unmapped_right = HashSet::from_iter(right.as_game().pkgs.iter().filter(|pkg_inst| {
        rightmap
            .iter()
            .find(|(_, game_inst_name)| game_inst_name == &pkg_inst.name)
            .is_none()
    }));

    if unmapped_left != unmapped_right {
        let mut left_summary = unmapped_left
            .iter()
            .map(|pkg_inst| {
                let mut hasher = DefaultHasher::new();
                pkg_inst.hash(&mut hasher);
                (pkg_inst.as_name(), hasher.finish())
            })
            .collect::<Vec<_>>();

        let mut right_summary = unmapped_right
            .iter()
            .map(|pkg_inst| {
                let mut hasher = DefaultHasher::new();
                pkg_inst.hash(&mut hasher);
                (pkg_inst.as_name(), hasher.finish())
            })
            .collect::<Vec<_>>();

        left_summary.sort();
        right_summary.sort();

        let example_left: &PackageInstance = unmapped_left
            .iter()
            .filter(|inst| inst.as_name() == "xor")
            .take(1)
            .collect::<Vec<_>>()[0];

        let example_right: &PackageInstance = unmapped_right
            .iter()
            .filter(|inst| inst.as_name() == "xor")
            .take(1)
            .collect::<Vec<_>>()[0];

        return Err(Error::ProofCheck(format!(
            "unmapped package instances not equal: \n{:#?} and \n{:#?}.\nexample: \n {:#?}\n {:#?}",
            left_summary, right_summary, example_left, example_right
        )));
    }

    Ok(())
}

/*
#[cfg(test)]
mod tests {
    use crate::package::{
        Composition, Edge, Export, OracleDef, OracleSig, Package, PackageInstance,
    };
    use crate::project::assumption::ResolvedAssumption;
    use crate::statement::CodeBlock;
    use crate::types::Type;

    use super::ResolvedReduction;

    #[test]
    fn check_assumption() {
        let osig_a = OracleSig {
            name: "doA".to_string(),
            args: vec![],
            tipe: Type::Empty,
        };

        let osig_b = OracleSig {
            name: "doB".to_string(),
            args: vec![],
            tipe: Type::Empty,
        };

        let pkg_a = Package {
            name: "A".to_string(),
            params: vec![],
            types: vec![],
            state: vec![],
            oracles: vec![OracleDef {
                sig: osig_a.clone(),
                code: CodeBlock(vec![]),
            }],
            imports: vec![],
        };

        let pkg_b = Package {
            name: "B".to_string(),
            types: vec![],
            params: vec![],
            state: vec![],
            oracles: vec![OracleDef {
                sig: osig_b.clone(),
                code: CodeBlock(vec![]),
            }],
            imports: vec![],
        };

        let left = Composition {
            pkgs: vec![
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "leftA1".to_string(),
                },
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "leftA2".to_string(),
                },
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "leftA3".to_string(),
                },
            ],
            exports: vec![Export(0, osig_a.clone())],
            edges: vec![Edge(0, 1, osig_a.clone()), Edge(0, 2, osig_a.clone())],
            name: "left".to_string(),
            consts: vec![],
        };

        let right = Composition {
            pkgs: vec![
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "rightA1".to_string(),
                },
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "rightA2".to_string(),
                },
                PackageInstance {
                    pkg: pkg_b.clone(),
                    params: vec![],
                    types: vec![],
                    name: "rightB3".to_string(),
                },
            ],

            exports: vec![Export(0, osig_a.clone())],
            edges: vec![Edge(0, 1, osig_a.clone()), Edge(0, 2, osig_b.clone())],
            name: "right".to_string(),
            consts: vec![],
        };

        let assumption_left = Composition {
            pkgs: vec![
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "leftA1".to_string(),
                },
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "leftA3".to_string(),
                },
            ],
            exports: vec![Export(0, osig_a.clone())],
            edges: vec![Edge(0, 1, osig_a.clone())],
            name: "assumption_left".to_string(),
            consts: vec![],
        };
        let assumption_right = Composition {
            pkgs: vec![
                PackageInstance {
                    pkg: pkg_a.clone(),
                    params: vec![],
                    types: vec![],
                    name: "rightA1".to_string(),
                },
                PackageInstance {
                    pkg: pkg_b.clone(),
                    params: vec![],
                    types: vec![],
                    name: "rightB3".to_string(),
                },
            ],
            exports: vec![Export(0, osig_a.clone())],
            edges: vec![Edge(0, 1, osig_b.clone())],
            name: "assumption_right".to_string(),
            consts: vec![],
        };

        let reduction = ResolvedReduction {
            left,
            right,
            leftmap: vec![(0, 0), (2, 1)],
            rightmap: vec![(0, 0), (2, 1)],
            assumption: ResolvedAssumption {
                left: assumption_left,
                right: assumption_right,
            },
            assumption_name: "assumption_name".to_string(),
        };

        reduction
            .prove()
            .expect_err("expect proving err but prove passed");
    }
}
 */
