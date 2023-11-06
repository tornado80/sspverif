use crate::expressions::Expression;
use crate::package::Composition;
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::collections::HashSet;
use std::iter::FromIterator;

#[derive(Debug, Clone)]
pub struct Error(pub String);

pub struct Transformation<'a>(pub &'a Composition);

#[derive(Clone, Debug)]
pub struct Position {
    pub game_name: String,
    pub inst_name: String,
    pub pkg_name: String,

    pub dst_name: String,
    pub dst_index: Option<Expression>,

    pub sample_id: usize,
    pub tipe: Type,
}

#[derive(Clone, Debug)]
pub struct SampleInfo {
    pub tipes: Vec<Type>,
    pub count: usize,
    pub positions: Vec<Position>,
}

impl<'a> super::Transformation for Transformation<'a> {
    type Err = Error;
    type Aux = SampleInfo;

    fn transform(&self) -> Result<(Composition, SampleInfo), Error> {
        let mut ctr = 1usize;
        let mut samplings = HashSet::new();
        let mut positions = vec![];

        let game_name = self.0.name.as_str();

        let insts: Result<Vec<_>, _> = self
            .0
            .pkgs
            .iter()
            .map(|inst| {
                let inst_name = inst.name.as_str();
                let pkg_name = inst.pkg.name.as_str();

                let mut newinst = inst.clone();
                for (i, oracle) in newinst.pkg.oracles.clone().iter().enumerate() {
                    newinst.pkg.oracles[i].code = samplify(
                        &oracle.code,
                        game_name,
                        pkg_name,
                        inst_name,
                        &mut ctr,
                        &mut samplings,
                        &mut positions,
                    )?;
                }
                Ok(newinst)
            })
            .collect();
        Ok((
            Composition {
                pkgs: insts?,
                ..self.0.clone()
            },
            SampleInfo {
                tipes: Vec::from_iter(samplings),
                count: ctr,
                positions,
            },
        ))
    }
}

pub fn samplify(
    cb: &CodeBlock,
    game_name: &str,
    pkg_name: &str,
    inst_name: &str,
    ctr: &mut usize,
    sampletypes: &mut HashSet<Type>,
    positions: &mut Vec<Position>,
) -> Result<CodeBlock, Error> {
    let mut newcode = Vec::new();
    for stmt in cb.0.clone() {
        match stmt {
            Statement::IfThenElse(expr, ifcode, elsecode, file_pos) => {
                newcode.push(Statement::IfThenElse(
                    expr,
                    samplify(
                        &ifcode,
                        game_name,
                        pkg_name,
                        inst_name,
                        ctr,
                        sampletypes,
                        positions,
                    )?,
                    samplify(
                        &elsecode,
                        game_name,
                        pkg_name,
                        inst_name,
                        ctr,
                        sampletypes,
                        positions,
                    )?,
                    file_pos.clone(),
                ));
            }
            Statement::For(iter, start, end, code, file_pos) => newcode.push(Statement::For(
                iter,
                start,
                end,
                samplify(
                    &code,
                    game_name,
                    pkg_name,
                    inst_name,
                    ctr,
                    sampletypes,
                    positions,
                )?,
                file_pos.clone(),
            )),

            Statement::Sample(id, expr, None, tipe, file_pos) => {
                let pos = Position {
                    game_name: game_name.to_string(),
                    inst_name: inst_name.to_string(),
                    pkg_name: pkg_name.to_string(),
                    dst_name: id.ident(),
                    dst_index: expr.clone(),
                    sample_id: *ctr,
                    tipe: tipe.clone(),
                };
                sampletypes.insert(tipe.clone());
                positions.push(pos);
                newcode.push(Statement::Sample(
                    id.clone(),
                    expr,
                    Some(*ctr),
                    tipe.clone(),
                    file_pos.clone(),
                ));
                *ctr += 1;
            }
            _ => newcode.push(stmt),
        }
    }
    Ok(CodeBlock(newcode))
}
