use std::collections::HashMap;
use std::fs;

use crate::package::{Composition, Package};
use crate::parser::{composition::handle_composition, package::handle_pkg, SspParser};

pub fn read_directory(dir_path: &str) -> (Vec<(String, String)>, Vec<(String, String)>) {
    let mut pkgs_list = vec![];
    let mut comp_list = vec![];

    let dir_list = fs::read_dir(dir_path).expect("cannot list directory");

    for dir_entry in dir_list {
        let dir_entry = dir_entry.unwrap();
        match dir_entry.file_name().to_str() {
            None => {
                continue;
            }
            Some(name) => {
                if name.ends_with(".ssp") {
                    let filecontent = fs::read_to_string(dir_entry.path());
                    assert!(filecontent.is_ok(), "cannot read file {}", name);

                    let filecontent = filecontent.unwrap().clone();
                    if name.ends_with(".pkg.ssp") {
                        pkgs_list.push((name.to_owned(), filecontent));
                    } else if name.ends_with(".comp.ssp") {
                        comp_list.push((name.to_owned(), filecontent));
                    }
                }
            }
        }
    }
    (pkgs_list, comp_list)
}

pub fn parse_packages(
    pkgs_list: &[(String, String)],
) -> (HashMap<String, Package>, HashMap<String, &String>) {
    let pkgs_list: Vec<_> = pkgs_list
        .iter()
        .map(|(filename, contents)| {
            let mut ast = SspParser::parse_package(contents)
                .unwrap_or_else(|e| panic!("error parsing file {}: {:#?}", filename, e));
            let (pkg_name, pkg) = handle_pkg(ast.next().unwrap());
            (filename, contents, ast, pkg_name, pkg)
        })
        .collect();

    let mut pkgs_map = HashMap::new();
    let mut pkgs_filenames = HashMap::new();

    for (filename, _, _, pkg_name, pkg) in pkgs_list {
        if let Some(other_filename) = pkgs_filenames.get(&pkg_name) {
            panic!(
                "Package {:?} redefined in {} (originally defined in {})",
                pkg_name, filename, other_filename
            )
        }

        pkgs_map.insert(pkg_name.clone(), pkg);
        pkgs_filenames.insert(pkg_name, filename);
    }

    (pkgs_map, pkgs_filenames)
}

pub fn parse_composition(
    comp_list: &[(String, String)],
    pkgs_map: &HashMap<String, Package>,
) -> HashMap<String, Composition> {
    let comp_list: Vec<_> = comp_list
        .iter()
        .map(|(filename, contents)| {
            let mut ast = match SspParser::parse_package(contents) {
                Ok(ast) => ast,
                Err(e) => {
                    panic!("error parsing file {}: {:#?}", filename, e);
                }
            };

            let comp = handle_composition(ast.next().unwrap(), pkgs_map);
            let comp_name = comp.name.clone();
            (filename, contents, ast, comp_name, comp)
        })
        .collect();

    let mut comp_map = HashMap::new();
    for (_, _, _, comp_name, comp) in comp_list {
        comp_map.insert(comp_name, comp);
    }

    comp_map
}
