use super::{common::*, Rule};

use pest::iterators::{Pair, Pairs};
use std::collections::HashMap;
use std::iter::FromIterator;

use crate::package::{Composition, Edge, Export, Package, PackageInstance};
use crate::types::Type;

pub fn handle_const_decl(ast: Pair<Rule>) -> (String, Type) {
    let mut inner = ast.into_inner();
    let name = inner.next().unwrap().as_str().to_owned();
    let tipe = handle_type(inner.next().unwrap());

    (name, tipe)
}

pub fn handle_compose_assign_list(ast: Pairs<Rule>) -> Vec<(String, String)> {
    ast.map(|assignment| {
        let mut inner = assignment.into_inner();
        let oracle_name = inner.next().unwrap().as_str();
        let dst_inst_name = inner.next().unwrap().as_str();

        (oracle_name.to_owned(), dst_inst_name.to_owned())
    })
    .collect()
}

pub fn handle_types_def(ast: Pair<Rule>) -> Vec<(Type, Type)> {
    match ast.into_inner().next() {
        None => vec![],
        Some(ast) => handle_types_def_list(ast),
    }
}

pub fn handle_types_def_list(ast: Pair<Rule>) -> Vec<(Type, Type)> {
    ast.into_inner()
        .map(|def_spec| handle_types_def_spec(def_spec))
        .collect()
}

pub fn handle_types_def_spec(ast: Pair<Rule>) -> (Type, Type) {
    let mut iter = ast.into_inner();

    let fst = iter.next().unwrap();
    let snd = iter.next().unwrap();

    (handle_type(fst), handle_type(snd))
}

/*
This functions parses the body of a compose block. It returns internal edges and exports.
 */
pub fn handle_compose_assign_body_list(
    ast: Pair<Rule>,
    instances: &HashMap<String, (usize, PackageInstance)>,
) -> (Vec<Edge>, Vec<Export>) {
    let mut edges = vec![];
    let mut exports = vec![];
    for body in ast.into_inner() {
        let mut inner = body.into_inner();
        let inst_name = inner.next().unwrap().as_str();
        if inst_name == "adversary" {
            for (oracle_name, dst_inst_name) in handle_compose_assign_list(inner) {
                let (dst_offset, dst_inst) = match instances.get(&dst_inst_name) {
                    None => {
                        panic!(
                            "instance {} not declared but used in compose block for {}",
                            dst_inst_name, inst_name
                        );
                    }
                    Some(inst) => inst,
                };
                let oracle_sig = match dst_inst
                    .pkg
                    .oracles
                    .iter()
                    .find(|oracle_def| oracle_def.sig.name == oracle_name)
                {
                    None => {
                        panic!(
                            "oracle {} not found in package instance {}",
                            oracle_name, dst_inst_name
                        );
                    }
                    Some(def) => def.sig.clone(),
                };
                exports.push(Export(*dst_offset, oracle_sig));
            }

            continue;
        }

        let (offset, _inst) = match instances.get(inst_name) {
            None => {
                panic!("instance {} not found in compose block", inst_name);
            }
            Some(x) => x,
        };

        for (oracle_name, dst_inst_name) in handle_compose_assign_list(inner) {
            let (dst_offset, dst_inst) = match instances.get(&dst_inst_name) {
                None => {
                    panic!(
                        "instance {} not declared but used in compose block for {}",
                        dst_inst_name, inst_name
                    );
                }
                Some(inst) => inst,
            };

            let oracle_sig = match dst_inst
                .pkg
                .oracles
                .iter()
                .find(|oracle_def| oracle_def.sig.name == oracle_name)
            {
                None => {
                    panic!(
                        "oracle {} not found in package instance {}",
                        oracle_name, dst_inst_name
                    );
                }
                Some(def) => def.sig.clone(),
            };

            edges.push(Edge(*offset, *dst_offset, oracle_sig));
        }
    }

    (edges, exports)
}

pub fn handle_comp_spec_list(
    ast: Pair<Rule>,
    comp_name: &str,
    pkg_map: &HashMap<String, Package>,
) -> Composition {
    let mut consts = HashMap::new();
    let mut instances = vec![];
    let mut instance_table = HashMap::new();

    let mut edges = None;
    let mut exports = None;
    //let mut compose = None;

    /*
    Note: the grammar enforces that we first have the const declarations,
    then the instance declarations and only then the composition block.
    This means that we can assume that the last step is done processing.
    */
    for comp_spec in ast.into_inner() {
        match comp_spec.as_rule() {
            Rule::const_decl => {
                let (name, tipe) = handle_const_decl(comp_spec);
                consts.insert(name, tipe);
            }
            Rule::instance_decl => {
                let inst = handle_instance_decl(comp_spec, pkg_map, &consts);
                instances.push(inst.clone());
                let offset = instances.len() - 1;
                instance_table.insert(inst.name.clone(), (offset, inst));
            }
            Rule::compose_decl => {
                let (edges_, exports_) =
                    handle_compose_assign_body_list(comp_spec, &instance_table);
                edges = Some(edges_);
                exports = Some(exports_);
            }
            _ => {
                unreachable!();
            }
        }
    }

    let (edges, exports) = match (edges, exports) {
        (None, None) => {
            panic!(
                "looks like composition {} doesn't have a compose block",
                comp_name
            );
        }
        (Some(edges), Some(exports)) => (edges, exports),
        _ => {
            unreachable!();
        }
    };

    let mut consts = Vec::from_iter(consts);
    consts.sort();

    Composition {
        edges,
        exports,
        name: comp_name.to_owned(),
        pkgs: instances,
        consts,
    }
}

pub fn handle_instance_param_assign_list(ast: Pair<Rule>) -> Vec<(String, String)> {
    ast.into_inner()
        .map(|inner| {
            //let inner = inner.into_inner().next().unwrap();

            let mut inner = inner.into_inner();
            let left = inner.next().unwrap().as_str();
            let right = inner.next().unwrap().as_str();

            (left.to_owned(), right.to_owned())
        })
        .collect()
}

pub fn handle_params_def_list(ast: Pair<Rule>) -> Vec<(String, String)> {
    handle_instance_param_assign_list(ast)
}

pub fn handle_instance_assign_list(ast: Pair<Rule>) -> (Vec<(String, String)>, Vec<(Type, Type)>) {
    let mut params = vec![];
    let mut types = vec![];

    for elem in ast.into_inner() {
        match elem.as_rule() {
            Rule::params_def => {
                let mut defs = handle_params_def_list(elem.into_inner().next().unwrap());
                params.append(&mut defs);
            }
            Rule::types_def => {
                let mut defs = handle_types_def_list(elem.into_inner().next().unwrap());
                types.append(&mut defs);
            }
            _ => unreachable!("{:#?}", elem),
        }
    }

    (params, types)
}

pub fn handle_instance_decl(
    ast: Pair<Rule>,
    pkg_map: &HashMap<String, Package>,
    consts: &HashMap<String, Type>,
) -> PackageInstance {
    let span = ast.as_span();

    let mut inner = ast.into_inner();
    let inst_name = inner.next().unwrap().as_str();
    let pkg_name = inner.next().unwrap().as_str();
    let data = inner.next().unwrap();

    let pkg = match pkg_map.get(pkg_name) {
        None => {
            panic!("package {} is unknown", pkg_name);
        }
        Some(pkg) => pkg,
    };

    let (param_list, type_list) = handle_instance_assign_list(data);
    //let param_list = handle_instance_param_assign_list(params);

    // check that param lists match (including types)
    let mut typed_params: Vec<_> = param_list
        .iter()
        .map(|(pkg_param, comp_param)| {
            let maybe_type = consts.get(comp_param);

            assert!(
                maybe_type.is_some(),
                "constant not specified: {} at {:?}",
                comp_param,
                span
            );
            (pkg_param.to_owned(), maybe_type.unwrap().clone())
        })
        .collect();
    typed_params.sort();

    let mut pkg_params = pkg.params.clone();
    pkg_params.sort();

    assert_eq!(
        typed_params, pkg_params,
        "params specified in composition don't match params specified in package for package {}",
        pkg_name
    );

    let mut assigned_types: Vec<_> = type_list
        .iter()
        .map(|(pkg_type, _)| pkg_type)
        .cloned()
        .collect();
    assigned_types.sort();

    let mut pkg_types = pkg.types.clone();
    pkg_types.sort();

    assert_eq!(
        assigned_types, pkg_types,
        "types specified in composition don't match types specified in package for package {}",
        pkg_name
    );

    PackageInstance {
        name: inst_name.to_owned(),
        params: HashMap::from_iter(param_list.into_iter()),
        types: HashMap::from_iter(type_list.into_iter()),
        pkg: pkg.clone(),
    }
}

pub fn handle_composition(ast: Pair<Rule>, pkg_map: &HashMap<String, Package>) -> Composition {
    let mut inner = ast.into_inner();
    let name = inner.next().unwrap().as_str();
    let spec = inner.next().unwrap();
    handle_comp_spec_list(spec, name, pkg_map)
}
