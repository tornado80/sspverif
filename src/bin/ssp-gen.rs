extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use std::env;
use std::fs;

#[derive(Parser)]
#[grammar = "parser/ssp.pest"]
pub struct SspParser;

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
        .map(|(name, contents)| {
            let ast = SspParser::parse(Rule::package, contents).unwrap();
            (name, contents, ast)
        })
        .collect();

    let comp_list: Vec<_> = comp_list
        .iter()
        .map(|(name, contents)| {
            let ast = match SspParser::parse(Rule::composition, contents) {
                Ok(ast) => ast,
                Err(e) => {
                    panic!("{:#?}", e);
                }
            };
            println!("ast: {:#?}", ast);
            (name, contents, ast)
        })
        .collect();

    //println!("pkgs: {:#?}", pkgs_list);
    //println!("compositions: {:#?}", comp_list);
}
