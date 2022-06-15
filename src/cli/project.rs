use std::fmt::Display;
use std::io::{Error as IOError, ErrorKind, Result};
use std::iter::FromIterator;
use std::{collections::HashMap, path::PathBuf};

use thiserror::Error;

use crate::package::{Composition, Package};

use super::filesystem::{
    find_project_root, parse_composition, parse_packages, read_compositions_directory,
    read_packages_directory, read_proofs_directory,
};
use super::ProofFile;

use std::fs;

#[derive(Debug, Error)]
enum Error {
    ProofExists(String),
    ProofCheck(String),
    CompositionMissing(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug)]
pub struct Project {
    root_dir: PathBuf,
    packages: HashMap<String, Package>,
    compositions: HashMap<String, Composition>,
    proofs: HashMap<String, PathBuf>,
}

impl Project {
    pub fn load() -> Result<Project> {
        let root = find_project_root()?;

        let mut pkgs_dir = root.clone();
        pkgs_dir.push("packages");
        let pkgs_dir_str = pkgs_dir.to_str().unwrap();
        let pkgs_list = read_packages_directory(pkgs_dir_str);

        let mut comp_dir = root.clone();
        comp_dir.push("compositions");
        let comp_dir_str = comp_dir.to_str().unwrap();
        let comp_list = read_compositions_directory(comp_dir_str);

        let (pkgs_map, _) = parse_packages(&pkgs_list);
        let comp_map = parse_composition(&comp_list, &pkgs_map);

        let mut proofs_dir = root.clone();
        proofs_dir.push("proofs");
        let proofs_dir_str = proofs_dir.to_str().unwrap();
        let proofs_list = read_proofs_directory(proofs_dir_str);

        println!("comps before proof check: {:#?}", comp_map.keys());
        println!("proofs before proof check: {:#?}", proofs_list);
        check_proofs(&proofs_list, &comp_map)?;

        Ok(Project {
            root_dir: root,
            packages: pkgs_map,
            compositions: comp_map,
            proofs: HashMap::from_iter(proofs_list.into_iter()),
        })
    }

    pub fn init_proof(
        &mut self,
        proof_name: &str,
        left_comp_name: &str,
        right_comp_name: &str,
    ) -> std::io::Result<()> {
        if self.proofs.contains_key(proof_name) {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::ProofExists(proof_name.into()),
            ));
        }

        if !self.compositions.contains_key(left_comp_name) {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::CompositionMissing(left_comp_name.into()),
            ));
        }
        if !self.compositions.contains_key(right_comp_name) {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::CompositionMissing(right_comp_name.into()),
            ));
        }

        let mut path = self.root_dir.clone();
        path.push("proofs");
        path.push(proof_name);
        fs::create_dir_all(&path)?;

        let mut proof_file_path = path.clone();
        proof_file_path.push("proof.toml");

        let data = ProofFile {
            Left: left_comp_name.into(),
            Right: right_comp_name.into(),
        };

        let toml_string = toml::to_string_pretty(&data).unwrap();
        fs::write(proof_file_path, toml_string)?;

        self.proofs.insert(proof_name.into(), path);

        Ok(())
    }

    pub fn build_proof(&self, proofname: &str) -> Result<()> {
        todo!();
    }
}

fn check_proofs(
    proof_list: &[(String, PathBuf)],
    comps: &HashMap<String, Composition>,
) -> Result<()> {
    for (_, proof_path) in proof_list {
        let mut proof_file_path = proof_path.clone();
        proof_file_path.push("proof.toml");
        let proof_file_contents = fs::read(proof_file_path).unwrap();
        let proof_file = toml::from_slice::<ProofFile>(&proof_file_contents).unwrap();
        if comps.get(&proof_file.Left).is_none() {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::ProofCheck(proof_file.Left),
            ));
        }

        if comps.get(&proof_file.Right).is_none() {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::ProofCheck(proof_file.Right),
            ));
        }
    }

    Ok(())
}
