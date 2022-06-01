extern crate pest;
extern crate pest_derive;

use std::env;

use sspds::cli::filesystem::{parse_composition, parse_packages, read_directory};
use sspds::hacks;
use sspds::smt::exprs::SmtFmt;
use sspds::smt::writer::CompositionSmtWriter;

fn main() {
    let args: Vec<String> = env::args().collect();
    let dir_path = args[1].clone();

    let (pkgs_list, comp_list) = read_directory(&dir_path);
    let (pkgs_map, _pkgs_filenames) = parse_packages(&pkgs_list);
    let comp_map = parse_composition(&comp_list, &pkgs_map);

    hacks::declare_par_Maybe();
    hacks::declare_Tuple(2);
    println!("(declare-sort Bits_n 0)");
    println!("(declare-fun f (Bits_n Bits_n) Bits_n)");

    for (name, comp) in comp_map {
        println!("; {}", name);

        //println!("{:#?}", comp);
        let (comp, _) = match sspds::transforms::transform_all(&comp) {
            Ok(x) => x,
            Err(e) => {
                panic!("found an error in composition {}: {:?}", name, e)
            }
        };
        let writer = CompositionSmtWriter::new(&comp);
        for line in writer.smt_composition_all() {
            line.write_smt_to(&mut std::io::stdout()).unwrap();
        }
    }

    println!("(check-sat)");
}
