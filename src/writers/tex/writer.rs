use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::collections::HashSet;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, Edge, Export, OracleDef, PackageInstance};
use crate::proof::GameHop;
use crate::proof::Proof;
use crate::statement::{CodeBlock, InvokeOracleStatement, Statement};
use crate::types::Type;
use crate::util::prover_process::ProverBackend;
use crate::util::prover_process::{Communicator, ProverResponse};
use crate::util::smtmodel::{SmtModel, SmtModelEntry};


/// TODO: Move to struct so we can have verbose versions (e.g. writing types to expressions)

fn genindentation(cnt: u8) -> String {
    let mut acc = String::new();
    for _ in 0..cnt {
        acc = format!("{}\\pcind", acc);
    }
    acc
}

struct BlockWriter<'a> {
    file: &'a mut File,
}

impl<'a> BlockWriter<'a> {
    fn new(file: &'a mut File) -> BlockWriter<'a> {
        BlockWriter { file }
    }

    fn ident_to_tex(&self, ident: &Identifier) -> String {
        format!("\\n{{{}}}", ident.ident().replace('_', "\\_"))
    }

    fn type_to_tex(&self, tipe: &Type) -> String {
        format!("\\O{{{:?}}}", tipe)
    }

    fn expression_to_tex(&self, expr: &Expression) -> String {
        match expr {
            Expression::Bot => "\\bot".to_string(),
            Expression::Identifier(ident) => self.ident_to_tex(ident),
            Expression::Not(expr) => format!("\\neg {}", self.expression_to_tex(expr)),
            Expression::Unwrap(expr) => format!("\\O{{unwrap}}({})", self.expression_to_tex(expr)),
            Expression::Some(expr) => format!("\\O{{some}}({})", self.expression_to_tex(expr)),
            Expression::None(tipe) => format!("\\O{{none}}({})", self.type_to_tex(tipe)),
            Expression::Add(lhs, rhs) => format!(
                "({} + {})",
                self.expression_to_tex(lhs),
                self.expression_to_tex(rhs)
            ),
            Expression::TableAccess(ident, expr) => format!(
                "{}[{}]",
                self.ident_to_tex(ident),
                self.expression_to_tex(expr)
            ),
            Expression::Equals(exprs) => exprs
                .iter()
                .map(|expr| self.expression_to_tex(expr))
                .collect::<Vec<_>>()
                .join(" = "),
            Expression::Tuple(exprs) => {
                format!(
                    "({})",
                    exprs
                        .iter()
                        .map(|expr| self.expression_to_tex(expr))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Expression::FnCall(name, args) => {
                format!(
                    "\\O{{{}}}({})",
                    name.ident(),
                    args.iter()
                        .map(|expr| self.expression_to_tex(expr))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            _ => {
                format!("{:?}", expr)
            }
        }
    }

    fn write_statement(&mut self, statement: &Statement, indentation: u8) -> std::io::Result<()> {
        match &statement {
            Statement::Abort(_) => {
                writeln!(self.file, "{} \\pcabort\\\\", genindentation(indentation))?;
            }
            Statement::Return(None, _) => {
                writeln!(self.file, "{} \\pcreturn\\\\", genindentation(indentation))?;
            }
            Statement::Return(Some(expr), _) => {
                writeln!(
                    self.file,
                    "{} \\pcreturn {}\\\\",
                    genindentation(indentation),
                    self.expression_to_tex(expr)
                )?;
            }
            Statement::Assign(ident, None, expr, _) => {
                writeln!(
                    self.file,
                    "{} {} \\gets {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    self.expression_to_tex(expr)
                )?;
            }
            Statement::Assign(ident, Some(idxexpr), expr, _) => {
                writeln!(
                    self.file,
                    "{} {}[{}] \\gets {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    self.expression_to_tex(idxexpr),
                    self.expression_to_tex(expr)
                )?;
            }
            Statement::Parse(ids, expr, _) => {
                writeln!(
                    self.file,
                    "{}\\pcparse {} \\pcas {}\\\\",
                    genindentation(indentation),
                    self.expression_to_tex(expr),
                    ids.iter()
                        .map(|ident| self.ident_to_tex(ident))
                        .collect::<Vec<_>>()
                        .join(", ")
                )?;
            }
            Statement::IfThenElse(expr, ifcode, elsecode, _) => {
                writeln!(
                    self.file,
                    "{}\\pcif {} \\pcthen\\\\",
                    genindentation(indentation),
                    self.expression_to_tex(expr)
                )?;
                self.write_codeblock(ifcode, indentation + 1)?;
                if !elsecode.0.is_empty() {
                    writeln!(self.file, "{}\\pcelse\\\\", genindentation(indentation))?;
                    self.write_codeblock(elsecode, indentation + 1)?;
                }
            }
            Statement::For(_, _, _, _, _) => todo!(),
            Statement::Sample(ident, None, maybecnt, tipe, _) => {
                let cnt = maybecnt.expect("Expected samplified input");

                writeln!(
                    self.file,
                    "{}{} \\stackrel{{{}}}{{\\sample}} {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    cnt,
                    self.type_to_tex(tipe)
                )?;
            }
            Statement::Sample(ident, Some(idxexpr), maybecnt, tipe, _) => {
                let cnt = maybecnt.expect("Expected samplified input");

                writeln!(
                    self.file,
                    "{}{}[{}] \\stackrel{{{}}}{{\\samples}} {}\\\\",
                    genindentation(indentation),
                    self.ident_to_tex(ident),
                    self.expression_to_tex(idxexpr),
                    cnt,
                    self.type_to_tex(tipe)
                )?;
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id: ident,
                opt_idx: None,
                name,
                args,
                target_inst_name: Some(target_inst_name),
                tipe: _,
                ..
            }) => {
                writeln!(self.file,
                         "{}{} \\stackrel{{\\mathsf{{\\tiny{{invoke}}}}}}{{\\gets}} \\O{{{}}}({}) \\pccomment{{Pkg: {}}} \\\\",
                         genindentation(indentation),
                         self.ident_to_tex(ident), name,
                         args.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", "),
                         target_inst_name.replace('_',"\\_")
                )?;
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                id: ident,
                opt_idx: Some(idxexpr),
                name,
                args,
                target_inst_name: Some(target_inst_name),
                tipe: _,
                ..
            }) => {
                writeln!(self.file,
                         "{}{}[{}] \\stackrel{{\\mathsf{{\\tiny invoke}}}}{{\\gets}} \\O{{{}}}({}) \\pccomment{{Pkg: {}}} \\\\",
                         genindentation(indentation),
                         self.ident_to_tex(ident),
                         self.expression_to_tex(idxexpr),
                         name,
                         args.iter().map(|expr| self.expression_to_tex(expr)).collect::<Vec<_>>().join(", "),
                         target_inst_name.replace('_',"\\_")
                )?;
            }
            Statement::InvokeOracle(InvokeOracleStatement {
                target_inst_name: None,
                ..
            }) => {
                unreachable!("Expect oracle-lowlevelified input")
            }
        }
        Ok(())
    }

    fn write_codeblock(&mut self, codeblock: &CodeBlock, indentation: u8) -> std::io::Result<()> {
        for stmt in &codeblock.0 {
            self.write_statement(stmt, indentation)?
        }
        Ok(())
    }
}

pub fn tex_write_oracle(
    oracle: &OracleDef,
    pkgname: &str,
    target: &Path,
) -> std::io::Result<String> {
    let fname = target.join(format!("Oracle_{}_{}.tex", pkgname, oracle.sig.name));
    let mut file = File::create(fname.clone())?;
    let mut writer = BlockWriter::new(&mut file);

    writeln!(
        writer.file,
        "\\procedure{{\\O{{{}}}({})}}{{",
        oracle.sig.name,
        oracle
            .sig
            .args
            .iter()
            .map(|(a, _)| a.clone())
            .collect::<Vec<_>>()
            .join(", ")
    )?;

    let codeblock = &oracle.code;
    writer.write_codeblock(codeblock, 0)?;

    writeln!(writer.file, "}}")?;
    Ok(fname.to_str().unwrap().to_string())
}

pub fn tex_write_package(package: &PackageInstance, target: &Path) -> std::io::Result<String> {
    let fname = target.join(format!("Package_{}.tex", package.name));
    let mut file = File::create(fname.clone())?;

    writeln!(
        file,
        "\\begin{{pcvstack}}\\underline{{\\underline{{\\M{{{}}}}}}}\\\\\\begin{{pchstack}}",
        package.name.replace('_', "\\_")
    )?;

    for oracle in &package.pkg.oracles {
        let oraclefname = tex_write_oracle(oracle, &package.name, target)?;
        let oraclefname = Path::new(&oraclefname)
            .strip_prefix(fname.clone().parent().unwrap())
            .unwrap()
            .to_str();
        writeln!(file, "\\input{{{}}}\\pchspace", oraclefname.unwrap())?;
    }
    writeln!(file, "\\end{{pchstack}}\\end{{pcvstack}}")?;

    Ok(fname.to_str().unwrap().to_string())
}

fn tex_write_document_header(mut file: &File) -> std::io::Result<()> {
    writeln!(file, "\\documentclass[a4paper,landscape]{{article}}")?;
    writeln!(file, "\\usepackage[margin=1in]{{geometry}}")?;
    writeln!(file, "\\usepackage[operators]{{cryptocode}}")?;
    writeln!(file, "\\usepackage{{tikz}}")?;
    writeln!(
        file,
        "\\renewcommand\\O[1]{{\\ensuremath{{\\mathsf{{#1}}}}}}"
    )?;
    writeln!(
        file,
        "\\newcommand{{\\M}}[1]{{\\ensuremath{{\\text{{\\texttt{{#1}}}}}}}}"
    )?;
    writeln!(
        file,
        "\\newcommand{{\\n}}[1]{{\\ensuremath{{\\mathit{{#1}}}}}}"
    )?;
    writeln!(file, "\\tikzstyle{{package}} = [inner sep=1pt,align=center,rounded corners,draw,minimum width=2cm,minimum height=1cm,font=\\small]")?;
    writeln!(file, "\\tikzstyle{{onarrow}} = [inner sep=1pt,font=\\scriptsize,anchor=west,at start,align=left,fill=white]")?;
    Ok(())
}

fn tex_solve_composition_graph(
    backend: &Option<ProverBackend>,
    composition: &Composition,
) -> Option<SmtModel> {
    use std::fmt::Write;

    let mut model = String::new();

    for height in 2..50 {
        let mut edges:HashSet<(usize, usize)> = HashSet::new();
        let mut comm = Communicator::new(backend.unwrap()).unwrap();

        writeln!(comm, "(declare-const num-pkgs Int)").unwrap();
        writeln!(comm, "(declare-const width Int)").unwrap();
        writeln!(comm, "(declare-const height Int)").unwrap();
        writeln!(comm, "(assert (= num-pkgs {}))", composition.pkgs.len()).unwrap();

        // Adversary
        writeln!(comm, "(declare-const --column Int)").unwrap();
        writeln!(comm, "(assert (= 0 --column))").unwrap();
        writeln!(comm, "(declare-const --top Int)").unwrap();
        writeln!(comm, "(declare-const --bottom Int)").unwrap();
        writeln!(comm, "(assert (< 0 --bottom (- --top 1) height))").unwrap();

        for i in 0..composition.pkgs.len() {
            let pkg = &composition.pkgs[i].name;
            writeln!(comm, "(declare-const {pkg}-column Int)").unwrap();
            writeln!(comm, "(assert (< 0 {pkg}-column width))").unwrap();
            writeln!(comm, "(declare-const {pkg}-top Int)").unwrap();
            writeln!(comm, "(declare-const {pkg}-bottom Int)").unwrap();
            writeln!(comm, "(assert (< 0 {pkg}-bottom (- {pkg}-top 1) height))").unwrap();
        }

        for Edge(from, to, _oracle) in &composition.edges {
            if edges.contains(&(*from, *to)) {continue};
            edges.insert((*from,*to));
            let pkga = &composition.pkgs[*from].name;
            let pkgb = &composition.pkgs[*to].name;

            writeln!(comm, "(declare-const edge-{pkga}-{pkgb}-height Int)").unwrap();
            writeln!(
                comm,
                "(assert (< {pkga}-bottom edge-{pkga}-{pkgb}-height {pkga}-top))"
            )
            .unwrap();
            writeln!(
                comm,
                "(assert (< {pkgb}-bottom edge-{pkga}-{pkgb}-height {pkgb}-top))"
            )
            .unwrap();
            writeln!(comm, "(assert (< {pkga}-column {pkgb}-column))").unwrap();
        }
        
        for Export(to, _oracle) in &composition.exports {
            if edges.contains(&(usize::MAX, *to)) {continue};
            edges.insert((usize::MAX,*to));
            let pkga = "-";
            let pkgb = &composition.pkgs[*to].name;

            writeln!(comm, "(declare-const edge-{pkga}-{pkgb}-height Int)").unwrap();
            writeln!(
                comm,
                "(assert (< {pkga}-bottom edge-{pkga}-{pkgb}-height {pkga}-top))"
            )
            .unwrap();
            writeln!(
                comm,
                "(assert (< {pkgb}-bottom edge-{pkga}-{pkgb}-height {pkgb}-top))"
            )
            .unwrap();
            writeln!(comm, "(assert (< {pkga}-column {pkgb}-column))").unwrap();
        }

        for i in 0..composition.pkgs.len() {
            for j in 0..i {
                let pkga = &composition.pkgs[i].name;
                let pkgb = &composition.pkgs[j].name;
                writeln!(
                    comm,
                    "
(assert (not (exists ((l Int))
               (and
                 (<= {pkga}-bottom l {pkga}-top)
                 (<= {pkgb}-bottom l {pkgb}-top)
                 (= {pkga}-column {pkgb}-column)))))"
                )
                .unwrap();
            }
        }

        for i in 0..composition.pkgs.len() {
            for Edge(from, to, _oracle) in &composition.edges {
                let pkga = &composition.pkgs[*from].name;
                let pkgb = &composition.pkgs[*to].name;
                let pkgc = &composition.pkgs[i].name;

                writeln!(
                    comm,
                    "
(assert (not (exists ((l Int))
               (and 
                 (=  edge-{pkga}-{pkgb}-height l)
                 (<  {pkga}-column {pkgc}-column {pkgb}-column)
                 (<= (- {pkgc}-bottom 1) l (+ {pkgc}-top 1))))))"
                )
                .unwrap();
            }
            for Export(to, _oracle) in &composition.exports {
                let pkga = "-";
                let pkgb = &composition.pkgs[*to].name;
                let pkgc = &composition.pkgs[i].name;

                writeln!(
                    comm,
                    "
(assert (not (exists ((l Int))
               (and 
                 (=  edge-{pkga}-{pkgb}-height l)
                 (<  {pkga}-column {pkgc}-column {pkgb}-column)
                 (<= (- {pkgc}-bottom 1) l (+ {pkgc}-top 1))))))"
                )
                .unwrap();
            }
        }

        writeln!(comm, "(assert (< height {height}))").unwrap();

        if comm.check_sat().unwrap() == ProverResponse::Sat {
            model = comm.get_model().unwrap();
            break;
        }
    }

    let model = SmtModel::from_string(&model);
    println!("{:#?}", model);
    Some(model)
}

fn tex_write_composition_graph(
    backend: &Option<ProverBackend>,
    mut file: &File,
    composition: &Composition,
    pkgmap: &[(std::string::String, std::string::String)],
) -> std::io::Result<()> {

    let mut write_node =
        |mut file:&File, pkgname:&str, compname:&str, idx, top, bottom, column| -> std::io::Result<()> {
        let fill =
            if pkgmap
            .iter()
            .any(|(pname, _)| pkgname == *pname) {
                "red!50"
            } else {
                "white"
            };

        writeln!(
            file,
            "\\node[anchor=south west,align=center,package,minimum height={}cm,fill={fill}]
    (node{}) at ({},{})
    {{\\M{{{}}}\\\\\\M{{{}}}}};",
            f64::from(top-bottom)/2.0,
            idx,
            column*4,
            f64::from(bottom)/2.0,
            compname.replace('_', "\\_"),
            pkgname.replace('_', "\\_")
        )?;
        Ok(())
    };

    
    let solution = tex_solve_composition_graph(backend, composition);

    if let Some(model) = solution {
        writeln!(file, "\\begin{{tikzpicture}}")?;
        //writeln!(file, "\\draw (-1,-1) grid (10,5);")?;
        for i in 0..composition.pkgs.len() {
            let pkgname = &composition.pkgs[i].name;
            let SmtModelEntry::IntEntry{value: top, .. } =
                model.get_value(&format!("{pkgname}-top")).unwrap();
            let SmtModelEntry::IntEntry{value: bottom, .. } =
                model.get_value(&format!("{pkgname}-bottom")).unwrap();
            let SmtModelEntry::IntEntry{value: column, .. } =
                model.get_value(&format!("{pkgname}-column")).unwrap();

            write_node(file, pkgname, &composition.name, i, top, bottom, column)?;
        }
        for from in 0..composition.pkgs.len() {
            for to in 0..composition.pkgs.len() {
                let oracles:Vec<_> = composition.edges.iter().filter_map(|Edge(f, t, oracle)|{
                    if from == *f && to == *t {
                        Some(oracle.name.clone())
                    } else { None }
                }).collect();
                if oracles.is_empty() {continue;}
                
                let pkga = &composition.pkgs[from].name;
                let pkgb = &composition.pkgs[to].name;

                let SmtModelEntry::IntEntry{value: height, .. } =
                    model.get_value(&format!("edge-{pkga}-{pkgb}-height")).unwrap();
                let SmtModelEntry::IntEntry{value: acolumn, .. } =
                    model.get_value(&format!("{pkga}-column")).unwrap();
                let SmtModelEntry::IntEntry{value: bcolumn, .. } =
                    model.get_value(&format!("{pkgb}-column")).unwrap();


                let height = f64::from(height)/2.0;
                let oracles = oracles.into_iter().map(|o| format!("\\O{{{o}}}")).collect::<Vec<_>>().join("\\\\");
                writeln!(file, "\\draw[-latex,rounded corners]
    ({},{}) -- node[onarrow] {{{}}} ({},{});",
                         acolumn*4+2, height, oracles, bcolumn*4, height)?;
                
            }
        }
        for to in 0..composition.pkgs.len() {
            let oracles:Vec<_> = composition.exports.iter().filter_map(|Export(t, oracle)|{
                if to == *t {
                    Some(oracle.name.clone())
                } else { None }
            }).collect();
            if oracles.is_empty() {continue;}

            let pkgb = &composition.pkgs[to].name;

            let SmtModelEntry::IntEntry{value: height, .. } =
                model.get_value(&format!("edge---{pkgb}-height")).unwrap();
            let SmtModelEntry::IntEntry{value: acolumn, .. } =
                model.get_value(&format!("--column")).unwrap();
            let SmtModelEntry::IntEntry{value: bcolumn, .. } =
                model.get_value(&format!("{pkgb}-column")).unwrap();


            let height = f64::from(height)/2.0;
            let oracles = oracles.into_iter().map(|o| format!("\\O{{{o}}}")).collect::<Vec<_>>().join("\\\\");
            writeln!(file, "\\draw[-latex,rounded corners]
    ({},{}) -- node[onarrow] {{{}}} ({},{});",
                     acolumn*4+2, height, oracles, bcolumn*4, height)?;
                    
        }
        //writeln!(file, "\\draw[red,fill=red] (0,0) circle (.2);")?;
        writeln!(file, "\\end{{tikzpicture}}")?;
    } else {    
        let mut printed = Vec::new();
        let mut newly = Vec::new();
        
        let mut tikzx = 0;
        let mut tikzy = 0;

        writeln!(file, "\\begin{{tikzpicture}}")?;
        while printed.len() < composition.pkgs.len() {
            for i in 0..composition.pkgs.len() {
                if printed.contains(&i) {
                    continue;
                }

                if !composition
                    .edges
                    .iter()
                    .any(|Edge(from, to, _oracle)| i == *from && !printed.contains(to))
                {
                    write_node(file, &composition.pkgs[i].name, &composition.name, i,
                               tikzy+1, tikzy, tikzx)?;
                    newly.push(i);
                    tikzy -= 2;

                    for Edge(from, to, oracle) in &composition.edges {
                        if i == *from {
                            writeln!(file, "\\draw[-latex,rounded corners] (node{}) -- ($(node{}.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", from, from, oracle.name, to)?;
                        }
                    }
                }
            }
            printed.append(&mut newly);
            tikzx -= 4;
            tikzy = tikzx / 4;
        }

        writeln!(
            file,
            "\\node[package] (nodea) at ({}, {}) {{$A$}};",
            tikzx, tikzy
        )?;
        for Export(to, oracle) in &composition.exports {
            writeln!(file, "\\draw[-latex,rounded corners] (nodea) -- ($(nodea.east) + (1,0)$) |- node[onarrow] {{\\O{{{}}}}} (node{});", oracle.name, to)?;
        }
        writeln!(file, "\\end{{tikzpicture}}")?;
    }
    Ok(())
}

fn tex_write_composition_graph_file(
    backend: &Option<ProverBackend>,
    composition: &Composition,
    name: &str,
    target: &Path,
) -> std::io::Result<String> {
    let fname = target.join(format!("CompositionGraph_{}.tex", name));
    let file = File::create(fname.clone())?;

    tex_write_composition_graph(backend, &file, composition, &Vec::new())?;

    Ok(fname.to_str().unwrap().to_string())
}

pub fn tex_write_composition(
    backend: &Option<ProverBackend>,
    composition: &Composition,
    name: &str,
    target: &Path,
) -> std::io::Result<()> {
    let fname = target.join(format!("Composition_{}.tex", name));
    let mut file = File::create(fname.clone())?;

    tex_write_document_header(&file)?;

    writeln!(file, "\\title{{{} Game}}", name)?;
    writeln!(file, "\\begin{{document}}")?;
    writeln!(file, "\\maketitle")?;

    let graphfname = tex_write_composition_graph_file(backend, composition, name, target)?;
    let graphfname = Path::new(&graphfname)
        .strip_prefix(fname.clone().parent().unwrap())
        .unwrap()
        .to_str();
    writeln!(file, "\\begin{{center}}")?;
    writeln!(file, "\\input{{{}}}", graphfname.unwrap())?;
    writeln!(file, "\\end{{center}}")?;

    for pkg in &composition.pkgs {
        let pkgfname = tex_write_package(pkg, target)?;
        let pkgfname = Path::new(&pkgfname)
            .strip_prefix(fname.clone().parent().unwrap())
            .unwrap()
            .to_str();
        writeln!(file, "\\begin{{center}}")?;
        writeln!(file, "\\input{{{}}}", pkgfname.unwrap())?;
        writeln!(file, "\\end{{center}}")?;
    }

    writeln!(file, "\\end{{document}}")?;

    Ok(())
}

pub fn tex_write_proof(backend: &Option<ProverBackend>, proof: &Proof, name: &str, target: &Path) -> std::io::Result<()> {
    let fname = target.join(format!("Proof_{}.tex", name));
    let mut file = File::create(fname)?;

    tex_write_document_header(&file)?;

    writeln!(file, "\\title{{Proof: {}}}", name)?;
    writeln!(file, "\\begin{{document}}")?;
    writeln!(file, "\\maketitle")?;

    writeln!(file, "\\section{{Games}}")?;

    for instance in &proof.instances {
        writeln!(file, "\\subsection{{{} Game}}", instance.name())?;

        let graphfname = format!("CompositionGraph_{}.tex", instance.name());
        writeln!(file, "\\begin{{center}}")?;
        writeln!(file, "\\input{{{}}}", graphfname)?;
        writeln!(file, "\\end{{center}}")?;

        for package in &instance.game().pkgs {
            let pkgfname = format!("Package_{}.tex", package.name);
            writeln!(file, "\\begin{{center}}")?;
            writeln!(file, "\\input{{{}}}", pkgfname)?;
            writeln!(file, "\\end{{center}}")?;
        }
    }

    for game_hop in &proof.game_hops {
        match &game_hop {
            GameHop::Reduction(red) => {
                writeln!(file, "\\section{{Reduction to {}}}", red.assumption_name())?;

                writeln!(
                    file,
                    "\\subsection{{Game {} with Assumption Game {} highlighted in red}}",
                    red.left().as_game_inst_name(),
                    red.left().as_assumption_game_inst_name()
                )?;
                writeln!(file, "\\begin{{center}}")?;
                let left_game_instance = proof
                    .instances
                    .iter()
                    .find(|instance| instance.name() == red.left().as_game_inst_name())
                    .unwrap();
                tex_write_composition_graph(
                    backend,
                    &file,
                    left_game_instance.game(),
                    red.left().pkg_maps(),
                )?;
                writeln!(file, "\\end{{center}}")?;

                writeln!(
                    file,
                    "\\subsection{{Game {} with Assumption Game {} highlighted  in red}}",
                    red.right().as_game_inst_name(),
                    red.right().as_assumption_game_inst_name()
                )?;
                writeln!(file, "\\begin{{center}}")?;
                let right_game_instance = proof
                    .instances
                    .iter()
                    .find(|instance| instance.name() == red.right().as_game_inst_name())
                    .unwrap();
                tex_write_composition_graph(
                    backend,
                    &file,
                    right_game_instance.game(),
                    red.right().pkg_maps(),
                )?;
                writeln!(file, "\\end{{center}}")?;
            }
            GameHop::Equivalence(equiv) => {
                writeln!(
                    file,
                    "\\section{{Equivalence between {} and {}}}",
                    equiv.left_name(),
                    equiv.right_name()
                )?;
            }
        }
    }

    writeln!(file, "\\end{{document}}")?;
    Ok(())
}
