#[macro_use]
extern crate pest_derive;

pub mod expressions;
pub mod gamehops;
pub mod identifier;
pub mod package;
pub mod split;
pub mod statement;
pub mod types;

pub mod transforms;
pub mod writers;

pub mod hacks;

pub mod parser;

pub mod testdata;

pub mod project;

pub mod util;

pub mod proof;

pub mod error {
    use crate::statement::FilePosition;

    pub trait LocationError: std::error::Error {
        fn file_pos<'a>(&'a self) -> &'a FilePosition;
    }
}
