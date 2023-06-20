use std::collections::HashMap;

use crate::identifier::Identifier;
use crate::package::{Composition, Edge, Export, OracleDef, OracleSig};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::fmt::Write;

pub struct SplitPartial;

#[derive(Debug)]
pub enum Error {}

type Result<T> = std::result::Result<T, Error>;

#[derive(Clone,Copy,Debug)]
enum SplitType {
    Plain,  // before anything interesting happens
    Invoc,   // called a child oracle
    Step,    // in a loop
    If,
    Else,
}

impl std::fmt::Display for SplitType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone,Debug)]
struct SplitPathComponent {
    pkginstname: String,
    oraclename: String,
    splittype: SplitType,
    splitrange: std::ops::Range<usize>,
}

impl SplitPathComponent {
    pub fn new(pkginstname: &str, oraclename: &str, splittype: SplitType, splitrange:std::ops::Range<usize>) -> Self {
        SplitPathComponent{
            pkginstname: pkginstname.to_string(),
            oraclename: oraclename.to_string(),
            splittype,
            splitrange
        }
    }
}

#[derive(Clone,Debug)]
struct SplitPath (
    Vec<SplitPathComponent>
);

impl SplitPath {
    pub fn extended(&self, component: SplitPathComponent) -> Self {
        let mut result = self.clone();
        result.0.push(component);
        result
    }

    pub fn smt_name(&self) -> String {
        let mut result = String::new();
        for component in self.0 {
            if result != "" {
                write!(result, "/");
            } 
            write!(result, "{}!{}!{}{:?}",
                   component.pkginstname, component.oraclename, component.splittype, component.splitrange);
        }
        result
    }
}
    
impl super::GameTransform for SplitPartial {
    type Err = Error;

    type Aux = Vec<SplitPath>;

    fn transform_game(
        &self,
        game: &Composition,
    ) -> std::result::Result<(crate::package::Composition, Self::Aux), Self::Err> {
        let mut new_game = game.clone();
        let mut sig_mapping: HashMap<(String, OracleSig), Vec<(SplitPath, OracleSig)>> = Default::default();

        let mut dependencies: HashMap<(usize, OracleSig), Vec<usize>> = HashMap::new();

        for Edge(from, to, sig) in &game.edges {
            dependencies
                .entry((*to, sig.clone()))
                .or_default()
                .push(*from);
        }

        for Export(pkg_offs, sig) in &game.exports {
            dependencies.entry((*pkg_offs, sig.clone())).or_default();
        }

        while !dependencies.is_empty() {
            let keys: Vec<_> = dependencies.keys().cloned().collect();

            for key in &keys {
                let (to, sig) = key;
                if dependencies[key].is_empty() {
                    transform_oracle(&mut new_game, *to, sig, &mut sig_mapping)?;

                    for idx in &keys {
                        if let Some(pos) = dependencies[idx].iter().position(|x| x == to) {
                            dependencies.entry(idx.clone()).or_default().remove(pos);
                        }
                    }
                    dependencies.remove(key);
                }
            }
        }

        Ok((new_game, vec![]))
    }
}

impl Statement {
    fn needs_split(&self, sig_mapping: &HashMap<(String, OracleSig), Vec<(SplitPath, OracleSig)>>) -> bool {
        match self {
            Statement::For(_, _, _, _) => true,
            Statement::IfThenElse(_cond, ifcode, elsecode) => {
                ifcode.0.iter().any(|stmt| stmt.needs_split(sig_mapping))
                    || elsecode.0.iter().any(|stmt| stmt.needs_split(sig_mapping))
            }
            Statement::InvokeOracle {
                name,
                target_inst_name: Some(target_inst_name),
                ..
            } => sig_mapping
                .keys()
                .any(|(inst_name, osig)| inst_name == target_inst_name && &osig.name == name),
            Statement::InvokeOracle {
                target_inst_name: None,
                ..
            } => unreachable!(),
            _ => false,
        }
    }
}

fn transform_oracle(
    game: &mut Composition,
    pkg_offs: usize,
    osig: &OracleSig,
    sig_mapping: &mut HashMap<(String, OracleSig), Vec<(SplitPath, OracleSig)>>,
) -> Result<()> {
    let pkg = &mut game.pkgs[pkg_offs];
    let game_name = &game.name;
    let inst_name = &pkg.name;
    let oracle_offs = pkg
        .pkg
        .oracles
        .iter()
        .position(|OracleDef { sig, .. }| sig == osig)
        .expect("there should be an oracle with this signature");
    let odef = &pkg.pkg.oracles[oracle_offs];
    let oracle_name = &odef.sig.name;

    println!(
        "transforming {game_name}.{inst_name}.{oracle_name}: {:?}",
        odef.code
    );

    let mut result = vec![];

    let mut transformed = transform_codeblock(&odef.code, SplitPath(vec![]), vec![], sig_mapping);

    let inst_name = &pkg.name;
    let entry = sig_mapping
        .entry((inst_name.to_string(), osig.clone()))
        .or_default();

    // we treat the last item differently:
    // intermediate items get an empty return type,
    // the last item gets the original return type.
    let (last_splitpath, last_code, last_locals) = transformed.pop().unwrap();

    for (splitpath, oracle_code, oracle_locals) in transformed.into_iter() {
        let sig = OracleSig {
            name: splitpath.smt_name(),
            args: osig.args.clone(),
            tipe: Type::Empty, // <-- note the difference
            partial_vars: oracle_locals.clone(),
        };
        result.push(OracleDef {
            sig: sig.clone(),
            code: oracle_code,
        });
        entry.push((SplitPath(vec![]), sig))
    }

    let sig = OracleSig {
        name: last_splitpath.smt_name(),
        args: osig.args.clone(),
        tipe: osig.tipe.clone(), // <-- note the difference
        partial_vars: last_locals.clone(),
    };
    result.push(OracleDef {
        sig: sig.clone(),
        code: last_code,
    });
    entry.push((SplitPath(vec![]), sig));

    pkg.pkg.oracles.remove(oracle_offs);
    pkg.pkg.oracles.extend(result);

    Ok(())
}

fn transform_codeblock(
    code: &CodeBlock,
    prefix: SplitPath,
    mut locals: Vec<(String, Type)>,
    sig_mapping: &mut HashMap<(String, OracleSig), Vec<(SplitPath, OracleSig)>>,
) -> Vec<(SplitPath, CodeBlock, Vec<(String, Type)>)> {
    let mut result = vec![];

    let mut split_indices = vec![];
    for i in 0..code.0.len() {
        if code.0[i].needs_split(sig_mapping) {
            split_indices.push((i, locals.clone()));
        }
        match &code.0[i] {
            Statement::Parse(ids, expr) => {
                todo!()
            }
            Statement::Assign(Identifier::Local(id_name), Some(idx), expr) => {
                locals.push((
                    id_name.to_string(),
                    Type::Table(
                        Box::new(idx.get_type().unwrap().clone()),
                        Box::new(expr.get_type().unwrap().clone()),
                    ),
                ));
            }
            Statement::Assign(Identifier::Local(id_name), None, expr) => {
                locals.push((id_name.to_string(), expr.get_type().unwrap().clone()));
            }
            Statement::InvokeOracle {
                id: Identifier::Local(id_name),
                tipe: Some(tipe),
                opt_idx: Some(idx),
                ..
            }
            | Statement::Sample(Identifier::Local(id_name), Some(idx), _, tipe) => {
                locals.push((
                    id_name.to_string(),
                    Type::Table(
                        Box::new(idx.get_type().unwrap().clone()),
                        Box::new(tipe.clone()),
                    ),
                ));
            }
            Statement::InvokeOracle {
                id: Identifier::Local(id_name),
                tipe: Some(tipe),
                opt_idx: None,
                ..
            }
            | Statement::Sample(Identifier::Local(id_name), None, _, tipe) => {
                locals.push((id_name.to_string(), tipe.clone()))
            }
            _ => {}
        }
    }

    let mut cur_idx = 0;
    let mut did_split = false;

    for (split_idx, split_locals) in split_indices {
        did_split = true;
        if split_idx != cur_idx {
            let range = cur_idx..split_idx;
            result.push((
                prefix.extended(SplitPathComponent::new("", "", SplitType::Plain, range)),
                CodeBlock(code.0[range].to_vec()),
                split_locals.clone(),
            ))
        }

        match &code.0[split_idx] {
            Statement::IfThenElse(_cond, ifcode, elsecode) => {
                result.extend(transform_codeblock(
                    ifcode,
                    prefix.extended(SplitPathComponent::new("", "", SplitType::If, split_idx..(split_idx+1))),
                    split_locals.clone(),
                    sig_mapping,
                ));
                result.extend(transform_codeblock(
                    elsecode,
                    prefix.extended(SplitPathComponent::new("", "", SplitType::Else, split_idx..(split_idx+1))),
                    split_locals.clone(),
                    sig_mapping,
                ));
            }
            Statement::For(_id_iter, _from, _to, code) => {
                result.extend(transform_codeblock(
                    code,
                    prefix.extended(SplitPathComponent::new("", "", SplitType::Else, split_idx..(split_idx+1))),
                    split_locals,
                    sig_mapping,
                ));
            }
            Statement::InvokeOracle {
                id,
                opt_idx,
                name,
                target_inst_name: Some(target_inst_name),
                args,
                tipe,
                ..
            } => {
                let (_, splits) = sig_mapping
                    .iter()
                    .find(|((inst_name, sig), _)| {
                        inst_name == target_inst_name && &sig.name == name
                    })
                    .unwrap();

                let last_split = splits.last().unwrap();

                result.extend(splits.into_iter().take(splits.len() - 1).map(
                    |(splitpath, OracleSig { name, .. })| {
                        let mut newpath = prefix.extended(SplitPathComponent::new("", "", SplitType::Invoc, split_idx..(split_idx+1))) ;
                        newpath.0.extend(splitpath.0);
                        (
                            newpath,
                            CodeBlock(vec![Statement::InvokeOracle {
                                id: Identifier::new_scalar("_"),
                                name: name.to_string(),
                                opt_idx: None,
                                args: args.clone(),
                                target_inst_name: Some(target_inst_name.to_string()),
                                tipe: None,
                            }]),
                            split_locals.clone(),
                        )
                    },
                ));

                result.push((
                    prefix.extended(SplitPathComponent::new("", "", SplitType::Invoc, split_idx..(split_idx+1))),
                    CodeBlock(vec![Statement::InvokeOracle {
                        id: id.clone(),
                        opt_idx: opt_idx.clone(),
                        name: last_split.1.name.clone(),
                        args: args.clone(),
                        target_inst_name: Some(target_inst_name.to_string()),
                        tipe: tipe.clone(),
                    }]),
                    split_locals,
                ))
            }
            _ => unreachable!(),
        }

        cur_idx = split_idx;
    }

    if did_split {
        let rest = &code.0[cur_idx + 1..];
        if !rest.is_empty() {
            result.push((
                prefix.extended(SplitPathComponent::new("", "", SplitType::Plain, (cur_idx+1)..code.0.len())),
                CodeBlock(rest.to_vec()), locals));
        }
    } else {
        result.push((prefix.extended(SplitPathComponent::new("", "", SplitType::Plain, 0..code.0.len())),
                     CodeBlock(code.0.clone()), locals));
    }

    result
}

#[cfg(test)]
mod test {
    use std::default::Default;

    use crate::{
        expressions::Expression,
        identifier::Identifier,
        statement::{CodeBlock, Statement},
    };

    use super::transform_codeblock;

    #[test]
    fn oracle_transform_splits_around_for() {
        let id_i = Identifier::new_scalar("i");
        let id_foo = Identifier::new_scalar("foo");
        let expr_i = Expression::Identifier(id_i.clone());
        let expr_foo = Expression::Identifier(id_foo.clone());

        let code = CodeBlock(vec![
            Statement::Assign(
                id_foo.clone(),
                None,
                Expression::IntegerLiteral("2".to_string()),
            ),
            Statement::For(
                id_i.clone(),
                Expression::IntegerLiteral("0".to_string()),
                Expression::IntegerLiteral("10".to_string()),
                CodeBlock(vec![Statement::Assign(
                    Identifier::new_scalar("foo"),
                    None,
                    Expression::Add(Box::new(expr_i.clone()), Box::new(expr_foo.clone())),
                )]),
            ),
            Statement::Return(Some(expr_foo.clone())),
        ]);

        let mut sig_mapping = Default::default();

        let out = transform_codeblock(&code, "Eval", vec![], &mut sig_mapping);

        println!("{out:#?}");
    }
}
