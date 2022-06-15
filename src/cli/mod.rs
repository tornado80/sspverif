use std::string;

pub mod filesystem;
pub mod project;

use serde_derive::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct ProofFile {
    Left: String,
    Right: String,
}
