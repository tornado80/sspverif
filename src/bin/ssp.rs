use clap::{Parser, Subcommand};

use sspds::cli::filesystem::{parse_packages,parse_composition,read_directory};
use sspds::package::Composition;
use std::fs::File;
use std::io::Write;

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
    Check { name: Option<String> },
    /// Generate latex (cryptocode) files
    Latex { name: Option<String> },
    /// Generate graph representation of the composition
    Graph(Graph),
}

#[derive(clap::Args)]
#[clap(author, version, about, long_about = None)]
struct Graph {
    dirname: String,
    #[clap(short, long)]
    output: String
}

fn graph(args: &Graph) {
    let (pkgs_list, comp_list) = read_directory(&args.dirname);
    let (pkgs_map, _pkgs_filenames) = parse_packages(&pkgs_list);
    let comp_map = parse_composition(&comp_list, &pkgs_map);

    for (name, comp) in comp_map {
        let mut file = File::create(format!("{}/{}.dot", args.output, name)).unwrap();
        writeln!(&mut file, "{}",
            "digraph test {\n  rankdir=LR;\n  node [shape=\"box\"];\n").unwrap();

        let Composition{pkgs, edges, exports, name:_} = comp;
        for (source, target, sig) in edges {
            writeln!(&mut file, "  {} -> {} [label=\"{}\"]",
                     pkgs[source].name,
                     pkgs[target].name,
                     format!("{}", sig).replace("\"", "\\\"")
            ).unwrap(); 
        }

        for (target, sig) in exports {
            writeln!(&mut file, "  adversary -> {} [label=\"{}\"]",
                     pkgs[target].name,
                     format!("{}", sig).replace("\"", "\\\"")
            ).unwrap(); 
        }
        
        file.write(b"}\n").unwrap();
    }
}


fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Check { name } => {
            println!("'myapp add' was used, name is: {:?}", name)
        } 
        Commands::Latex { name } => {
            println!("'myapp add' was used, name is: {:?}", name)
        }
        Commands::Graph(args) => {
            graph(args)
        }
   }
}
