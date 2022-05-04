extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use std::collections::HashMap;
use std::env;
use std::fs;

use sspds::parser::{composition::handle_composition, package::handle_pkg, Rule, SspParser};
use sspds::smt::exprs::{SmtExpr, SmtFmt};
use sspds::smt::writer::CompositionSmtWriter;

fn main() {
    let args: Vec<String> = env::args().collect();
    let dir_path = args[1].clone();

    let mut pkgs_list = vec![];
    let mut comp_list = vec![];

    let mut dir_list = fs::read_dir(dir_path).expect("cannot list directory");

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

    let pkgs_list: Vec<_> = pkgs_list
        .iter()
        .map(|(filename, contents)| {
            let mut ast = SspParser::parse(Rule::package, contents)
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

    let comp_list: Vec<_> = comp_list
        .iter()
        .map(|(filename, contents)| {
            let mut ast = match SspParser::parse(Rule::composition, contents) {
                Ok(ast) => ast,
                Err(e) => {
                    panic!("error parsing file {}: {:#?}", filename, e);
                }
            };

            let comp = handle_composition(ast.next().unwrap(), &pkgs_map);
            let name = comp.name.clone();
            (filename, contents, ast, comp, name)
        })
        .collect();

    for (_, _, _, comp, name) in comp_list {
        println!("; {}", name);

        //println!("{:#?}", comp);
        let (comp, _) = match sspds::transforms::transform_all(&comp) {
            Ok(x) => x,
            Err(e) => {
                panic!("found an error in composition {}: {:?}", name, e)
            }
        };
        let writer = CompositionSmtWriter::new(&comp);
        for line in writer.smt_composition_all() {
            line.write_smt_to(&mut std::io::stdout()).unwrap();
        }
    }

    //println!("pkgs: {:#?}", pkgs_list);
    //println!("compositions: {:#?}", comp_list);
}
