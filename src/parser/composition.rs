use super::package::handle_expression;
use super::{common::*, error, Rule};

use pest::iterators::{Pair, Pairs};
use std::collections::HashMap;
use std::iter::FromIterator;

use crate::expressions::Expression;
use crate::package::{Composition, Edge, Export, Package, PackageInstance};
use crate::transforms::resolvetypes::ResolveTypesPackageInstanceTransform;
use crate::transforms::PackageInstanceTransform;

use crate::types::Type;

pub fn handle_compose_assign_list(ast: Pairs<Rule>) -> Vec<(String, String)> {
    ast.map(|assignment| {
        let mut inner = assignment.into_inner();
        let oracle_name = inner.next().unwrap().as_str();
        let dst_inst_name = inner.next().unwrap().as_str();

        (oracle_name.to_owned(), dst_inst_name.to_owned())
    })
    .collect()
}

pub fn handle_types_def(ast: Pair<Rule>, inst_name: &str) -> error::Result<Vec<(Type, Type)>> {
    match ast.into_inner().next() {
        None => Ok(vec![]),
        Some(ast) => handle_types_def_list(ast, inst_name),
    }
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

            let mut oracle_sig = match dst_inst
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

            for (i, (name, arg_type)) in oracle_sig.args.iter().enumerate() {}

            edges.push(Edge(*offset, *dst_offset, oracle_sig));
        }
    }

    (edges, exports)
}

pub fn handle_comp_spec_list(
    ast: Pair<Rule>,
    comp_name: &str,
    pkg_map: &HashMap<String, Package>,
) -> error::Result<Composition> {
    let span = ast.as_span();
    let mut consts = HashMap::new();
    let mut consts_as_list = vec![];
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
                consts_as_list.push((name.clone(), tipe.clone()));
                consts.insert(name, tipe);
            }
            Rule::instance_decl => {
                let inst = handle_instance_decl(comp_spec, pkg_map, &consts)?;
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

    println!("handled const, instance, compose.");

    let (edges, exports) = match (edges, exports) {
        (None, None) => Err(error::Error::MissingComposeBlock {
            game_name: comp_name.to_string(),
        }
        .with_span(span)),
        (Some(edges), Some(exports)) => Ok((edges, exports)),
        _ => {
            unreachable!();
        }
    }?;

    let mut consts = Vec::from_iter(consts);
    consts.sort();

    Ok(Composition {
        edges,
        exports,
        name: comp_name.to_owned(),
        pkgs: instances,
        consts,
    })
}

pub fn handle_instance_assign_list(
    ast: Pair<Rule>,
    inst_name: &str,
    defined_consts: &[(String, Type)],
) -> error::Result<(Vec<(String, Expression)>, Vec<(Type, Type)>)> {
    let mut params = vec![];
    let mut types = vec![];

    for elem in ast.into_inner() {
        match elem.as_rule() {
            Rule::params_def => {
                let mut defs =
                    handle_params_def_list(elem.into_inner().next().unwrap(), defined_consts)?;
                params.append(&mut defs);
            }
            Rule::types_def => {
                let mut defs = handle_types_def_list(elem.into_inner().next().unwrap(), inst_name)?;
                types.append(&mut defs);
            }
            _ => unreachable!("{:#?}", elem),
        }
    }

    Ok((params, types))
}

pub fn handle_instance_decl(
    ast: Pair<Rule>,
    pkg_map: &HashMap<String, Package>,
    consts: &HashMap<String, Type>,
) -> error::Result<PackageInstance> {
    let span = ast.as_span();

    let mut inner = ast.into_inner();
    let inst_name = inner.next().unwrap().as_str();
    let pkg_name = inner.next().unwrap().as_str();
    let data = inner.next().unwrap();

    let pkg = match pkg_map.get(pkg_name) {
        None => {
            panic!("package {} is unknown", pkg_name);
        }
        Some(pkg) => Ok(pkg),
    }?;

    let defined_consts: Vec<_> = consts
        .iter()
        .map(|(name, tipe)| (name.clone(), tipe.clone()))
        .collect();

    let (param_list, type_list) = handle_instance_assign_list(data, inst_name, &defined_consts)?;

    // check that const param lists match
    let mut typed_params: Vec<_> = param_list
        .iter()
        .map(|(pkg_param, comp_param)| match comp_param {
            Expression::Identifier(id) => {
                let maybe_type = consts.get(&id.ident());

                assert!(
                    maybe_type.is_some(),
                    "constant not specified: {} at {:?}",
                    id.ident(),
                    span
                );
                (pkg_param.to_owned(), maybe_type.unwrap().clone())
            }
            Expression::BooleanLiteral(_) => (pkg_param.to_string(), Type::Boolean),
            Expression::IntegerLiteral(_) => (pkg_param.to_string(), Type::Integer),
            otherwise => {
                panic!("unhandled expression: {:?}", otherwise)
            }
        })
        .collect();
    typed_params.sort();

    let mut pkg_params = pkg.params.clone();
    pkg_params.sort();

    if typed_params != pkg_params {
        // TODO: include the difference in here
        return Err(error::Error::PackageConstParameterMismatch {
            pkg_name: pkg_name.to_string(),
            inst_name: inst_name.to_string(),
            bound_params: typed_params,
            pkg_params,
        }
        .with_span(span));
    }

    // check that type param lists match
    let mut assigned_types: Vec<_> = type_list
        .iter()
        .map(|(pkg_type, _)| pkg_type)
        .cloned()
        .collect();
    assigned_types.sort();

    for (left, right) in &type_list {}

    let mut pkg_types = pkg.types.clone();
    pkg_types.sort();

    if assigned_types != pkg_types {
        // TODO include the difference in here
        return Err(error::SpanError::new_with_span(
            error::Error::TypeParameterMismatch {
                pkg_name: pkg_name.to_string(),
            },
            span,
        ));
    }

    let inst = PackageInstance {
        name: inst_name.to_owned(),
        params: HashMap::from_iter(param_list.into_iter()),
        types: HashMap::from_iter(type_list.into_iter()),
        pkg: pkg.clone(),
    };

    match ResolveTypesPackageInstanceTransform.transform_package_instance(&inst) {
        Ok((inst, _)) => Ok(inst),
        Err(err) => Err(error::Error::from(err).with_span(span)),
    }
}

pub fn handle_composition(
    ast: Pair<Rule>,
    pkg_map: &HashMap<String, Package>,
) -> error::Result<Composition> {
    let mut inner = ast.into_inner();
    let name = inner.next().unwrap().as_str();
    let spec = inner.next().unwrap();
    handle_comp_spec_list(spec, name, pkg_map)
}
