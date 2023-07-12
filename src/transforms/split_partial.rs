use std::collections::HashMap;

use crate::expressions::Expression;
use crate::identifier::Identifier;
use crate::package::{Composition, Edge, Export, OracleDef, OracleSig};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;
use std::fmt::Write;

pub struct SplitPartial;

#[derive(Debug)]
pub enum Error {}

type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SplitType {
    Plain,                           // before anything interesting happens
    Phantom,                         // Empty auxilliary function
    Invoc,                           // called a child oracle
    ForStep(Expression, Expression), // in a loop
    IfCondition(Expression),
    IfBranch,
    ElseBranch,
}

/*

adv -> A:O1 -> B:O2 -> C:O3

A:O1:Invoc(locals)
A:O1:Invoc(locals)/B:O2:Invoc(locals)

 */

/*
 * ForStep/ForStep/IfBranch/{locals1}Invoc , {inner_locals}
 * |---------locals1-------|
 */

impl std::fmt::Display for SplitType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            SplitType::ForStep(_, _) => write!(f, "ForStep"),
            SplitType::IfCondition(_) => write!(f, "IfCondition"),
            _ => write!(f, "{:?}", &self),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SplitPathComponent {
    pkginstname: String,
    oraclename: String,
    splittype: SplitType,
    splitrange: std::ops::Range<usize>,
}

impl SplitPathComponent {
    pub fn new(
        pkginstname: &str,
        oraclename: &str,
        splittype: SplitType,
        splitrange: std::ops::Range<usize>,
    ) -> Self {
        SplitPathComponent {
            pkginstname: pkginstname.to_string(),
            oraclename: oraclename.to_string(),
            splittype,
            splitrange,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SplitPath {
    gamename: String,
    path: Vec<SplitPathComponent>,
}

impl SplitPath {
    pub fn empty(gamename: String) -> Self {
        Self {
            path: vec![],
            gamename,
        }
    }

    pub fn has_prefix(&self, prefix: &SplitPath) -> bool {
        if self.gamename != prefix.gamename {
            return false;
        }

        if prefix.path.len() > self.path.len() {
            return false;
        }

        for i in 0..prefix.path.len() {
            if prefix.path[i] != self.path[i] {
                return false;
            }
        }

        true
    }

    pub fn basename(&self) -> (Option<SplitPathComponent>, Self) {
        let mut result = self.clone();
        let tail = result.path.pop();
        (tail, result)
    }

    pub fn extended(&self, component: SplitPathComponent) -> Self {
        let mut result = self.clone();
        result.path.push(component);
        result
    }

    pub fn smt_name(&self) -> String {
        let mut result = String::new();
        write!(result, "{}", self.gamename).unwrap();
        for component in &self.path {
            write!(result, "/").unwrap();
            write!(
                result,
                "{}!{}!{}{:?}",
                component.pkginstname,
                component.oraclename,
                component.splittype,
                component.splitrange
            )
            .unwrap();
        }
        result
    }
}

pub struct SplitInfoEntry {
    path: SplitPath,
    locals: Vec<(String, Type)>,
    next: Option<SplitPath>,
    elsenext: Option<SplitPath>,
}

impl SplitInfoEntry {
    pub fn path(&self) -> &SplitPath {
        &self.path
    }
    pub fn locals(&self) -> &Vec<(String, Type)> {
        &self.locals
    }
}

pub type SplitInfo = Vec<SplitInfoEntry>;

impl super::GameTransform for SplitPartial {
    type Err = Error;

    type Aux = SplitInfo;

    fn transform_game(
        &self,
        game: &Composition,
    ) -> std::result::Result<(crate::package::Composition, Self::Aux), Self::Err> {
        let mut new_game = game.clone();
        let mut sig_mapping: HashMap<(String, OracleSig), Vec<(SplitPath, OracleSig)>> =
            Default::default();

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

        let mut partials = vec![];
        for Export(pkg_offs, sig) in &game.exports {
            let pkg_inst_name = game.pkgs[*pkg_offs].name.clone();
            let mut one_oracle_partials: Vec<_> = sig_mapping[&(pkg_inst_name, sig.clone())]
                .iter()
                .map(|(path, sig)| SplitInfoEntry {
                    path: path.clone(),
                    locals: sig.partial_vars.clone(),
                    next: None,
                    elsenext: None,
                })
                .collect();

            for i in 0..(one_oracle_partials.len() - 1) {
                let (head, basename) = one_oracle_partials[i].path.basename();
                let head = head.unwrap();
                let split_type = head.splittype.clone();

                match split_type {
                    SplitType::IfBranch
                    | SplitType::ElseBranch
                    | SplitType::Plain
                    | SplitType::ForStep(_, _)
                    | SplitType::Invoc => {
                        one_oracle_partials[i].next = Some(one_oracle_partials[i + 1].path.clone())
                    }
                    SplitType::Phantom => {
                        // Decide if we are leaving a for loop at this point
                        //  - At the end of the path is a ForStep , i.e. .../ForStep/Phantom
                        //  - i+1 does not have *that* ForStep
                        if let SplitType::ForStep(_, _) =
                            basename.path.iter().last().unwrap().splittype
                        {
                            // Forward search first element with *this* forstep
                            for j in 0..i {
                                if one_oracle_partials[j].path.has_prefix(&basename) {
                                    one_oracle_partials[i].next =
                                        Some(one_oracle_partials[j].path.clone())
                                }
                            }
                            one_oracle_partials[i].elsenext =
                                Some(one_oracle_partials[i + 1].path.clone())
                        } else {
                            // Non-for-loop-related phantom
                            one_oracle_partials[i].next =
                                Some(one_oracle_partials[i + 1].path.clone())
                        }
                    }
                    SplitType::IfCondition(_) => {
                        one_oracle_partials[i].next = Some(one_oracle_partials[i + 1].path.clone());
                        let prefix = basename.extended(SplitPathComponent {
                            splittype: SplitType::ElseBranch,
                            ..head.clone()
                        });

                        for j in i..one_oracle_partials.len() {
                            if one_oracle_partials[j].path.has_prefix(&prefix) {
                                one_oracle_partials[i].elsenext =
                                    Some(one_oracle_partials[j].path.clone());
                                break;
                            }
                        }
                    }
                }
            }
            partials.extend(one_oracle_partials.into_iter());
        }

        // InvokeOracle/InvokeOracle/ForStep {locals of innermost oracle}
        // InvokeOracle/InvokeOracle/ForStep {stack of locals of oracles}

        /* (a) InvokeOracle/Plain                // latest
         * (b) InvokeOracle/InvokeOracle/Plain   // locals + {}
         * (c) InvokeOracle/InvokeOracle/ForStep
         * (d) InvokeOracle/InvokeOracle/Plain   // locals.pop()
         * (e) InvokeOracle/Plain                //
         *
         * (a) (define-fun ... -> intermediateState_?) // will be consumed by (b)
         * (d) (define-fun ... -> intermediateState_?) // please_pop
         */

        Ok((new_game, partials))
    }
}

impl Statement {
    fn needs_split(
        &self,
        sig_mapping: &HashMap<(String, OracleSig), Vec<(SplitPath, OracleSig)>>,
    ) -> bool {
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
    let oracle_offs = pkg
        .pkg
        .oracles
        .iter()
        .position(|OracleDef { sig, .. }| sig == osig)
        .expect("there should be an oracle with this signature");
    let odef = &pkg.pkg.oracles[oracle_offs];
    let oracle_name = &odef.sig.name;

    let mut result = vec![];

    let mut transformed = transform_codeblock(
        &pkg.name,
        oracle_name,
        &odef.code,
        SplitPath::empty(game.name.clone()),
        vec![],
        sig_mapping,
    );

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
        entry.push((splitpath, sig))
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
    entry.push((last_splitpath, sig));

    pkg.pkg.oracles.remove(oracle_offs);
    pkg.pkg.oracles.extend(result);

    Ok(())
}

fn transform_codeblock(
    pkg_inst_name: &str,
    oracle_name: &str,
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
                if locals
                    .iter()
                    .find(|(localname, _)| localname == id_name)
                    .is_some()
                {
                    continue;
                }
                locals.push((
                    id_name.to_string(),
                    Type::Table(
                        Box::new(idx.get_type().unwrap().clone()),
                        Box::new(expr.get_type().unwrap().clone()),
                    ),
                ));
            }
            Statement::Assign(Identifier::Local(id_name), None, expr) => {
                if locals
                    .iter()
                    .find(|(localname, _)| localname == id_name)
                    .is_some()
                {
                    continue;
                }
                locals.push((id_name.to_string(), expr.get_type().unwrap().clone()));
            }
            Statement::InvokeOracle {
                id: Identifier::Local(id_name),
                tipe: Some(tipe),
                opt_idx: Some(idx),
                ..
            }
            | Statement::Sample(Identifier::Local(id_name), Some(idx), _, tipe) => {
                if locals
                    .iter()
                    .find(|(localname, _)| localname == id_name)
                    .is_some()
                {
                    continue;
                }
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
                if locals
                    .iter()
                    .find(|(localname, _)| localname == id_name)
                    .is_some()
                {
                    continue;
                }
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
                prefix.extended(SplitPathComponent::new(
                    pkg_inst_name,
                    oracle_name,
                    SplitType::Plain,
                    range.clone(),
                )),
                CodeBlock(code.0[range].to_vec()),
                split_locals.clone(),
            ))
        }

        match &code.0[split_idx] {
            Statement::IfThenElse(cond, ifcode, elsecode) => {
                result.push((
                    prefix.extended(SplitPathComponent::new(
                        pkg_inst_name,
                        oracle_name,
                        SplitType::IfCondition(cond.clone()),
                        split_idx..(split_idx + 1),
                    )),
                    CodeBlock(vec![]),
                    split_locals.clone(),
                ));
                result.extend(transform_codeblock(
                    pkg_inst_name,
                    oracle_name,
                    ifcode,
                    prefix.extended(SplitPathComponent::new(
                        pkg_inst_name,
                        oracle_name,
                        SplitType::IfBranch,
                        split_idx..(split_idx + 1),
                    )),
                    split_locals.clone(),
                    sig_mapping,
                ));
                result.extend(transform_codeblock(
                    pkg_inst_name,
                    oracle_name,
                    elsecode,
                    prefix.extended(SplitPathComponent::new(
                        pkg_inst_name,
                        oracle_name,
                        SplitType::ElseBranch,
                        split_idx..(split_idx + 1),
                    )),
                    split_locals.clone(),
                    sig_mapping,
                ));
            }
            Statement::For(_id_iter, from, to, code) => {
                result.extend(transform_codeblock(
                    pkg_inst_name,
                    oracle_name,
                    code,
                    prefix.extended(SplitPathComponent::new(
                        pkg_inst_name,
                        oracle_name,
                        SplitType::ForStep(from.clone(), to.clone()),
                        split_idx..(split_idx + 1),
                    )),
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
                        let mut newpath = prefix.extended(SplitPathComponent::new(
                            pkg_inst_name,
                            oracle_name,
                            SplitType::Invoc,
                            split_idx..(split_idx + 1),
                        ));
                        newpath.path.extend(splitpath.path.clone());
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
                    prefix.extended(SplitPathComponent::new(
                        pkg_inst_name,
                        oracle_name,
                        SplitType::Invoc,
                        split_idx..(split_idx + 1),
                    )),
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
                prefix.extended(SplitPathComponent::new(
                    pkg_inst_name,
                    oracle_name,
                    SplitType::Plain,
                    (cur_idx + 1)..code.0.len(),
                )),
                CodeBlock(rest.to_vec()),
                locals,
            ));
        }
    } else {
        result.push((
            prefix.extended(SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                SplitType::Plain,
                0..code.0.len(),
            )),
            CodeBlock(code.0.clone()),
            locals,
        ));
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

    use super::*;

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

        let out = transform_codeblock(
            "the-pkg",
            "TheOracle",
            &code,
            SplitPath::empty(),
            vec![],
            &mut sig_mapping,
        );

        println!("{out:#?}");
    }
}
