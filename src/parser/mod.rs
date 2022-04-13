pub mod common;
pub mod composition;
pub mod package;

extern crate pest;

use pest::Parser;

#[derive(Parser)]
#[grammar = "parser/ssp.pest"]
pub struct SspParser;
