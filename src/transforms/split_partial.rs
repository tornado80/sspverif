use std::collections::HashMap;

use crate::identifier::Identifier;
use crate::package::{Composition, Edge, OracleDef, OracleSig};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

pub struct SplitPartial;

#[derive(Debug)]
pub enum Error {}

type Result<T> = std::result::Result<T, Error>;

impl super::GameTransform for SplitPartial {
    type Err = Error;

    type Aux = ();

    fn transform_game(
        &self,
        game: &Composition,
    ) -> std::result::Result<(crate::package::Composition, Self::Aux), Self::Err> {
        let mut new_game = game.clone();
        let mut sig_mapping: HashMap<(String, OracleSig), Vec<OracleSig>> = Default::default();

        let mut dependencies: HashMap<(usize, OracleSig), Vec<usize>> = HashMap::new();

        for Edge(from, to, sig) in &game.edges {
            dependencies
                .entry((*to, sig.clone()))
                .or_default()
                .push(*from);
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

        Ok((new_game, ()))
    }
}

impl Statement {
    fn needs_split(&self, sig_mapping: &HashMap<(String, OracleSig), Vec<OracleSig>>) -> bool {
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
    sig_mapping: &mut HashMap<(String, OracleSig), Vec<OracleSig>>,
) -> Result<()> {
    let pkg = &mut game.pkgs[pkg_offs];
    let oracle_offs = pkg
        .pkg
        .oracles
        .iter()
        .position(|OracleDef { sig, .. }| sig == osig)
        .expect("there should be an oracle with this signature");
    let odef = &pkg.pkg.oracles[oracle_offs];

    let mut result = vec![];

    let mut transformed = transform_codeblock(&odef.code, sig_mapping);
    let (last_name, last_code) = transformed.remove(transformed.len() - 1);

    let inst_name = &pkg.name;
    let entry = sig_mapping
        .entry((inst_name.to_string(), osig.clone()))
        .or_default();

    for (oracle_name, oracle_code) in transformed.into_iter() {
        let sig = OracleSig {
            name: oracle_name,
            args: osig.args.clone(),
            tipe: Type::Empty,
        };
        result.push(OracleDef {
            sig: sig.clone(),
            code: oracle_code,
        });
        entry.push(sig)
    }

    let sig = OracleSig {
        name: last_name,
        args: osig.args.clone(),
        tipe: osig.tipe.clone(),
    };
    result.push(OracleDef {
        sig: sig.clone(),
        code: last_code,
    });
    entry.push(sig);

    pkg.pkg.oracles.remove(oracle_offs);
    pkg.pkg.oracles.extend(result);

    Ok(())
}

fn transform_codeblock(
    code: &CodeBlock,
    sig_mapping: &mut HashMap<(String, OracleSig), Vec<OracleSig>>,
) -> Vec<(String, CodeBlock)> {
    let mut result = vec![];

    let split_indices: Vec<usize> = code
        .0
        .iter()
        .enumerate()
        .filter_map(|(i, stmt)| {
            if stmt.needs_split(sig_mapping) {
                Some(i)
            } else {
                None
            }
        })
        .collect();

    let mut cur_idx = 0;
    let mut did_split = false;

    for split_idx in split_indices {
        did_split = true;
        if split_idx != cur_idx {
            let range = cur_idx..split_idx;
            result.push((
                format!("range{cur_idx}-{split_idx}"),
                CodeBlock(code.0[range].to_vec()),
            ))
        }

        match &code.0[split_idx] {
            Statement::IfThenElse(_cond, ifcode, elsecode) => {
                result.extend(
                    transform_codeblock(ifcode, sig_mapping)
                        .into_iter()
                        .map(|(name, code)| (format!("ifbranch{split_idx}-{name}"), code)),
                );
                result.extend(
                    transform_codeblock(elsecode, sig_mapping)
                        .into_iter()
                        .map(|(name, code)| (format!("elsebranch{split_idx}-{name}"), code)),
                );
            }
            Statement::For(_id_iter, _from, _to, code) => {
                result.extend(
                    transform_codeblock(code, sig_mapping)
                        .into_iter()
                        .map(|(name, code)| (format!("forstep{split_idx}-{name}"), code)),
                );
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
                    |OracleSig { name, .. }| {
                        (
                            format!("oracle{split_idx}-{name}"),
                            CodeBlock(vec![Statement::InvokeOracle {
                                id: Identifier::new_scalar("_"),
                                name: name.to_string(),
                                opt_idx: None,
                                args: args.clone(),
                                target_inst_name: Some(target_inst_name.to_string()),
                                tipe: None,
                            }]),
                        )
                    },
                ));

                result.push((
                    format!("oracle{split_idx}-{name}"),
                    CodeBlock(vec![Statement::InvokeOracle {
                        id: id.clone(),
                        opt_idx: opt_idx.clone(),
                        name: last_split.name.clone(),
                        args: args.clone(),
                        target_inst_name: Some(target_inst_name.to_string()),
                        tipe: tipe.clone(),
                    }]),
                ))
            }
            _ => unreachable!(),
        }

        cur_idx = split_idx;
    }

    let rest = if did_split {
        &code.0[cur_idx + 1..]
    } else {
        &code.0[cur_idx..]
    };
    if !rest.is_empty() {
        result.push((format!("rest"), CodeBlock(rest.to_vec())));
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

        let out = transform_codeblock(&code, &mut sig_mapping);

        println!("{out:#?}");
    }
}
