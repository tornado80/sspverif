use std::fs::File;
use std::path::Path;

use crate::package::{Composition, OracleDef, PackageInstance};

pub fn tex_write_oracle(oracle: &OracleDef, pkgname: &str, target: &Path) {
    let fname = target.join(format!("{}_{}.tex", pkgname, oracle.sig.name));
    let mut _file = File::create(fname);
}

pub fn tex_write_package(package: &PackageInstance, target: &Path) {
    for oracle in &package.pkg.oracles {
        tex_write_oracle(oracle, &package.name, target)
    }
}

pub fn tex_write_composition(composition: &Composition, target: &Path) {
    for pkg in &composition.pkgs {
        tex_write_package(pkg, target)
    }
}
