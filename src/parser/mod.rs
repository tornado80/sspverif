pub mod common;
pub mod composition;
pub mod package;

use pest::Parser;
extern crate pest;

use pest::error::Error;
use pest::iterators::Pairs;

#[derive(Parser)]
#[grammar = "parser/ssp.pest"]
pub struct SspParser;

impl SspParser {
    pub fn parse_package(contents: &str) -> Result<Pairs<Rule>, Error<Rule>> {
        SspParser::parse(Rule::package, contents)
    }

    pub fn parse_composition(contents: &str) -> Result<Pairs<Rule>, Error<Rule>> {
        SspParser::parse(Rule::composition, contents)
    }
}
