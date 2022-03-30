extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use std::env;
use std::fs;

#[derive(Parser)]
#[grammar = "parser/pkg.pest"]
pub struct SspParser;

fn main() {
    let args: Vec<String> = env::args().collect();
    let filecontent = fs::read_to_string(args[1].clone()).expect("cannot read file");
    let result = SspParser::parse(Rule::package, &filecontent);
    println!("{:#?}", result);
}
