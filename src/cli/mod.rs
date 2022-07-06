use std::collections::HashMap;

pub mod filesystem;
pub mod project;

use serde_derive::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct CompositionSpec {
    composition: String,
    params: HashMap<String, String>,
}

#[derive(Serialize, Deserialize)]
pub struct ProofFile {
    params: Vec<String>,
    left: CompositionSpec,
    right: CompositionSpec,
}
