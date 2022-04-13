use std::env;
use std::fs;

use pest::Parser;

use sspds::parser::{package::handle_pkg, Rule, SspParser};

fn main() {
    let args: Vec<String> = env::args().collect();
    let filecontent = fs::read_to_string(args[1].clone()).expect("cannot read file");
    let result = SspParser::parse(Rule::package, &filecontent);

    for elt in result.unwrap() {
        handle_pkg(elt);
    }
}
