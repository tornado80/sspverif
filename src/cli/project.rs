use std::collections::hash_map::RandomState;
use std::collections::HashSet;
use std::fmt::Display;
use std::io::{Error as IOError, ErrorKind, Result, Write};
use std::iter::FromIterator;
use std::path::Path;
use std::{collections::HashMap, path::PathBuf};

use thiserror::Error;

use crate::hacks;
use crate::package::{Composition, Package};
use crate::writers::smt::writer::CompositionSmtWriter;
use crate::writers::smt::SmtFmt;

use super::filesystem::{
    find_project_root, parse_composition, parse_packages, read_compositions_directory,
    read_packages_directory, read_proofs_directory,
};
use super::{CompositionSpec, ProofFile};

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
    proofs: Vec<String>,
}

fn build_proof_file(left: &Composition, right: &Composition) -> ProofFile {
    let left_params_set: HashSet<_, RandomState> =
        HashSet::from_iter(left.consts.iter().map(|(name, _)| name).cloned());
    let right_params_set: HashSet<_, RandomState> =
        HashSet::from_iter(right.consts.iter().map(|(name, _)| name).cloned());

    let proof_params: Vec<_> = left_params_set.union(&right_params_set).cloned().collect();

    ProofFile {
        params: proof_params,
        left: CompositionSpec {
            composition: left.name.clone(),
            params: Default::default(),
        },
        right: CompositionSpec {
            composition: right.name.clone(),
            params: Default::default(),
        },
    }
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

        let project = Project {
            root_dir: root,
            packages: pkgs_map,
            compositions: comp_map,
            proofs: proofs_list,
        };

        check_proofs(
            &project.proofs_path(),
            &project.proofs,
            &project.compositions,
        )?;

        Ok(project)
    }

    fn proofs_path(&self) -> PathBuf {
        let mut path = self.root_dir.clone();
        path.push("proofs");

        path
    }

    fn proof_toml_path(&self, proof_name: &str) -> PathBuf {
        let mut path = self.root_dir.clone();
        path.push("proofs");
        path.push(format!("{proof_name}.toml"));

        path
    }

    fn proof_dir_path(&self, proof_name: &str) -> PathBuf {
        let mut path = self.root_dir.clone();
        path.push("proofs");
        path.push(proof_name);

        path
    }

    pub fn init_proof(
        &mut self,
        proof_name: &str,
        left_comp_name: &str,
        right_comp_name: &str,
    ) -> std::io::Result<()> {
        if self.proofs.contains(&proof_name.to_string()) {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::ProofExists(proof_name.into()),
            ));
        }

        let left = match self.compositions.get(left_comp_name) {
            Some(comp) => comp,
            None => {
                return Err(IOError::new(
                    ErrorKind::Other,
                    Error::CompositionMissing(left_comp_name.into()),
                ));
            }
        };

        let right = match self.compositions.get(right_comp_name) {
            Some(comp) => comp,
            None => {
                return Err(IOError::new(
                    ErrorKind::Other,
                    Error::CompositionMissing(right_comp_name.into()),
                ));
            }
        };

        let data = build_proof_file(left, right);
        let toml_string = toml::to_string_pretty(&data).unwrap();

        /* Directory Layout:
            proofs/
            proofs/{proof_name}.toml
            proofs/{proof_name}/[...]
        */

        let proof_file_path = self.proof_toml_path(proof_name);
        fs::write(proof_file_path, toml_string)?;

        let dir_path = self.proof_dir_path(proof_name);
        fs::create_dir_all(&dir_path)?;

        self.proofs.push(proof_name.into());

        Ok(())
    }

    /*
    TODO in this function:
        - respect the parameter/constants mapping
            - generate paramter functions
            - fail if types don't match across compositions
        - concat the snips into full smt file
            - alternatively, don't concat but step by step feed into prover.
              that way, we know about the progress and proof status and can report meaningful data to the user
    */
    pub fn build_proof(&self, proof_name: &str) -> Result<()> {
        let proof_file_path = self.proof_toml_path(proof_name);
        let toml_string = fs::read(proof_file_path)?;
        let data: ProofFile = toml::from_slice(&toml_string)?;

        let left_comp = match self.compositions.get(&data.left.composition) {
            Some(comp) => comp,
            None => {
                return Err(IOError::new(
                    ErrorKind::NotFound,
                    Error::CompositionMissing(data.left.composition),
                ));
            }
        };

        let right_comp = match self.compositions.get(&data.right.composition) {
            Some(comp) => comp,
            None => {
                return Err(IOError::new(
                    ErrorKind::NotFound,
                    Error::CompositionMissing(data.right.composition),
                ));
            }
        };

        let mut dst_file_path = self.proof_dir_path(proof_name);
        dst_file_path.push("00_preamble.smt2snip");
        let mut dst_file = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .open(dst_file_path)?;

        hacks::declare_par_Maybe(&mut dst_file)?;
        hacks::declare_Tuple(&mut dst_file, 2)?;
        write!(dst_file, "(declare-sort Bits_n 0)")?;
        write!(dst_file, "(declare-sort Bits_* 0)")?;
        write!(dst_file, "(declare-fun f (Bits_n Bits_n) Bits_n)")?;

        for comp in [left_comp, right_comp] {
            let (comp, _, samp) = crate::transforms::transform_all(&comp)?;
            let mut writer = CompositionSmtWriter::new(&comp, samp);
            for line in writer.smt_composition_all() {
                line.write_smt_to(&mut dst_file)?;
            }
        }

        write!(dst_file, "(check-sat)")?;

        Ok(())
    }
}

fn check_proofs(
    proofs_path: &Path,
    proof_list: &[String],
    comps: &HashMap<String, Composition>,
) -> Result<()> {
    for proof_name in proof_list {
        let mut proof_file_path: PathBuf = proofs_path.to_path_buf();
        proof_file_path.push(format!("{proof_name}.toml"));
        let proof_file_contents = fs::read(proof_file_path).unwrap();
        let proof_file = toml::from_slice::<ProofFile>(&proof_file_contents).unwrap();
        if comps.get(&proof_file.left.composition).is_none() {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::ProofCheck(proof_file.left.composition),
            ));
        }

        if comps.get(&proof_file.right.composition).is_none() {
            return Err(IOError::new(
                ErrorKind::Other,
                Error::ProofCheck(proof_file.right.composition),
            ));
        }
    }

    Ok(())
}
