use crate::statement::CodeBlock;
use crate::types::Type;

use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleSig {
    pub name: String,
    pub args: Vec<(String, Type)>,
    pub tipe: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleDef {
    pub sig: OracleSig,
    pub code: CodeBlock,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Package {
    pub params: Vec<(String, Type)>,
    pub state: Vec<(String, Type)>,
    pub oracles: Vec<OracleDef>,
}

impl Package {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageInstance {
    pub params: HashMap<String, String>,
    pub pkg: Package,
    pub name: String,
}

impl PackageInstance {
    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        self.pkg
            .oracles
            .clone()
            .into_iter()
            .map(|d| d.sig)
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Composition {
    pub pkgs: Vec<PackageInstance>,
    pub edges: Vec<(usize, usize, OracleSig)>, // (from, to, oraclesig)
    // TODO: how do we deal with the case where we have
    // e.g. multiple key packages that we Set into?
    // Idea: Add a name to this tuple that is used by
    // the invoking package
    // contemplation: globally unique oracle identifiers vs
    // multiple shades of local uniqueness
    pub exports: Vec<(usize, OracleSig)>,
    pub name: String,
}

impl Composition {
    pub fn get_oracle_sigs(&self) -> Vec<OracleSig> {
        self.exports.iter().map(|(_, sig)| sig.clone()).collect()
    }

    fn pkg_map<F>(&self, f: F) -> Composition
    where
        F: Fn(&PackageInstance) -> PackageInstance,
    {
        Composition {
            pkgs: self.pkgs.iter().map(f).collect(),
            edges: self.edges.clone(),
            exports: self.exports.clone(),
            name: self.name.clone(),
        }
    }
}
