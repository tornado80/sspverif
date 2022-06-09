use std::fs::File;
use std::io::Write;
use std::path::Path;

use clap::{Parser, Subcommand};

use sspds::{
    cli::filesystem::{parse_composition, parse_packages, read_directory},
    
    package::{Composition, Edge, Export},

    writers::{
        smt::{
            exprs::SmtFmt,
            writer::CompositionSmtWriter
        },
        pseudocode::writer::Writer,
        tex::writer::{tex_write_composition}
    },
    hacks,
};


#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Cli {
    #[clap(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Verifies the code of packages
    Check { name: String },

    /// Generates SMT
    Smt { name: String },

    /// Generate latex (cryptocode) files
    Latex(LaTeX),

    /// Generate graph representation of the composition
    Graph(Graph),

    /// Give information about the provided code
    Explain(Explain)
}


#[derive(clap::Args)]
#[clap(author, version, about, long_about = None)]
struct Explain {
    dirname: String,
    #[clap(short, long)]
    output: String,
}

#[derive(clap::Args)]
#[clap(author, version, about, long_about = None)]
struct Graph {
    dirname: String,
    #[clap(short, long)]
    output: String,
}

#[derive(clap::Args)]
#[clap(author, version, about, long_about = None)]
struct LaTeX {
    dirname: String,
    #[clap(short, long)]
    output: String,
}

fn graph(args: &Graph) {
    let (pkgs_list, comp_list) = read_directory(&args.dirname);
    let (pkgs_map, _pkgs_filenames) = parse_packages(&pkgs_list);
    let comp_map = parse_composition(&comp_list, &pkgs_map);

    for (name, comp) in comp_map {
        let mut file = File::create(format!("{}/{}.dot", args.output, name)).unwrap();
        writeln!(
            &mut file,
            "digraph test {{\n  rankdir=LR;\n  node [shape=\"box\"];\n"
        )
        .unwrap();

        let Composition {
            pkgs,
            edges,
            exports,
            name: _,
        } = comp;
        for Edge(source, target, sig) in edges {
            writeln!(
                &mut file,
                "  {} -> {} [label=\"{}\"]",
                pkgs[source].name,
                pkgs[target].name,
                format!("{}", sig).replace('"', "\\\"")
            )
            .unwrap();
        }

        for Export(target, sig) in exports {
            writeln!(
                &mut file,
                "  adversary -> {} [label=\"{}\"]",
                pkgs[target].name,
                format!("{}", sig).replace('"', "\\\"")
            )
            .unwrap();
        }

        writeln!(file, "}}").unwrap();
        println!("Wrote {} to {}/{}.dot", name, args.output, name);
    }
}

fn smt(name:&str) {
    let (pkgs_list, comp_list) = read_directory(name);
    let (pkgs_map, _pkgs_filenames) = parse_packages(&pkgs_list);
    let comp_map = parse_composition(&comp_list, &pkgs_map);

    hacks::declare_par_Maybe();
    hacks::declare_Tuple(2);
    println!("(declare-sort Bits_n 0)");
    println!("(declare-fun f (Bits_n Bits_n) Bits_n)");

    for (name, comp) in comp_map {
        println!("; {}", name);

        //println!("{:#?}", comp);
        let (comp, _, samp) = match sspds::transforms::transform_all(&comp) {
            Ok(x) => x,
            Err(e) => {
                panic!("found an error in composition {}: {:?}", name, e)
            }
        };
        let mut writer = CompositionSmtWriter::new(&comp, samp);
        for line in writer.smt_composition_all() {
            line.write_smt_to(&mut std::io::stdout()).unwrap();
        }
    }

    println!("(check-sat)");
}


fn check(args: &str) {
    let (pkgs_list, comp_list) = read_directory(args);
    let (pkgs_map, _pkgs_filenames) = parse_packages(&pkgs_list);
    let comp_map = parse_composition(&comp_list, &pkgs_map);
    println!("Found {} Compositions", comp_map.len());
    for (name, comp) in comp_map {
        print!("Verifying Composition: {}", name);

        match sspds::transforms::transform_all(&comp) {
            Ok(_) => print!(": OK\n"),
            Err(e) => print!(": FAIL {:?}", e)
        }
    }
}


fn latex(args:&LaTeX) {
    let (pkgs_list, comp_list) = read_directory(&args.dirname);
    let (pkgs_map, _pkgs_filenames) = parse_packages(&pkgs_list);
    let comp_map = parse_composition(&comp_list, &pkgs_map);

    for (name, comp) in comp_map {
        println!("{}", name);
        tex_write_composition(&comp, Path::new(&args.output));
    }
}

fn explain(args: &Explain) {
    let (pkgs_list, comp_list) = read_directory(&args.dirname);
    let (pkgs_map, _pkgs_filenames) = parse_packages(&pkgs_list);
    let comp_map = parse_composition(&comp_list, &pkgs_map);

    let mut  w = Writer::new(std::io::stdout());

    for (name, comp) in comp_map {
        let (comp, _, _) = match sspds::transforms::transform_explain(&comp) {
            Ok(x) => x,
            Err(e) => {
                panic!("found an error in composition {}: {:?}", name, e)
            }
        };

        println!("{}", name);
        for inst in comp.pkgs {
            let pkg = inst.pkg;
            w.write_package(&pkg).unwrap();
        }

        //tex_write_composition(&comp, Path::new(&args.output));
    }
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Check { name } => check(name),
        Commands::Smt { name } => smt(name),
        Commands::Latex(args) => latex(args),
        Commands::Graph(args) => graph(args),
        Commands::Explain(args) => explain(args,)
    }
}
