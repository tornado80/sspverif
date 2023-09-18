use std::collections::HashMap;

use crate::identifier::Identifier;
use crate::package::{Composition, Edge, Export, OracleDef, OracleSig, SplitExport};
use crate::statement::{CodeBlock, Statement};
use crate::types::Type;

pub struct SplitPartial;

#[derive(Debug)]
pub enum Error {}

type Result<T> = std::result::Result<T, Error>;

/*

adv -> A:O1 -> B:O2 -> C:O3

A:O1:Invoc(locals)
A:O1:Invoc(locals)/B:O2:Invoc(locals)

 */

/*
 * ForStep/ForStep/IfBranch/{locals1}Invoc , {inner_locals}
 * |---------locals1-------|
 */

use crate::split::{
    InvocTargetData, SplitOracleDef, SplitOracleSig, SplitPath, SplitPathComponent, SplitType,
};

#[derive(Clone, Debug)]
pub struct SplitInfoEntry {
    pkg_inst_name: String,
    oracle_name: String,
    path: SplitPath,
    locals: Vec<(String, Type)>,
    next: Option<SplitPath>,
    elsenext: Option<SplitPath>,
    original_sig: OracleSig,
}

impl SplitInfoEntry {
    pub fn path(&self) -> &SplitPath {
        &self.path
    }
    pub fn locals(&self) -> &Vec<(String, Type)> {
        &self.locals
    }

    pub fn pkg_inst_name(&self) -> &str {
        self.pkg_inst_name.as_ref()
    }

    pub fn oracle_name(&self) -> &str {
        self.oracle_name.as_ref()
    }

    pub fn next(&self) -> Option<&SplitPath> {
        self.next.as_ref()
    }

    pub fn elsenext(&self) -> Option<&SplitPath> {
        self.elsenext.as_ref()
    }

    pub fn split_type(&self) -> Option<&SplitType> {
        Some(&self.path.last()?.split_type())
    }

    pub fn original_sig(&self) -> &OracleSig {
        &self.original_sig
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
        let mut sig_mapping: HashMap<
            (String, OracleSig),
            Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
        > = Default::default();

        // dependencies is the game graph in a form where we can start processing the call graph
        // from the leaves, and then remove that leave from this map.
        // We add all called oracles, first the edges and then the exports.
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

        // as long as we haven't processed all called oracles, we keep going.
        while !dependencies.is_empty() {
            let keys: Vec<_> = dependencies.keys().cloned().collect();

            for key in &keys {
                let (pkg_inst_offs, sig) = key;
                let pkg_inst = &game.pkgs[*pkg_inst_offs];
                if dependencies[key].is_empty() {
                    // found an oracle that doesn't have unprocessed callees.
                    // transform it!
                    transform_oracle(&mut new_game, *pkg_inst_offs, sig, &mut sig_mapping)?;

                    // of the oracle needed transformation, update the game
                    let mapping_key = (pkg_inst.name.clone(), sig.clone());
                    if let Some(mapping) = sig_mapping.get(&mapping_key) {
                        // remove the old oracle from the exports
                        if let Some(export_position) = new_game
                            .exports
                            .iter()
                            .position(|Export(_, exported_sig)| exported_sig == sig)
                        {
                            new_game.exports.remove(export_position);
                        }

                        // export all new split oracles
                        // note that this is always needed, even if the oracle was not exported
                        // before
                        for split_spec in mapping {
                            let (_, _, split_sig) = split_spec;
                            new_game
                                .split_exports
                                .push(SplitExport(*pkg_inst_offs, split_sig.clone()))
                        }
                    }

                    // remove current oracle from all other oracles dependency lists
                    for dep_list in dependencies.values_mut() {
                        if let Some(pos) = dep_list.iter().position(|x| x == pkg_inst_offs) {
                            dep_list.remove(pos);
                        }
                    }

                    // remove oracle from map to mark it as processed
                    dependencies.remove(key);
                }
            }
        }

        println!("sig mapping after splitting: {sig_mapping:?}");
        for (place, info) in sig_mapping.iter() {
            for (_, split_path, _) in info {
                println!("{place:?} :: {split_path:?} --> {}", split_path.smt_name());
            }
        }

        /* build Aux data structure
         *
         * TODO
         */

        let mut partials = vec![];
        for Export(pkg_offs, sig) in &game.exports {
            let pkg_inst_name = &game.pkgs[*pkg_offs].name;
            if let Some(mapping) = sig_mapping.get(&(pkg_inst_name.clone(), sig.clone())) {
                let oracle_name = &sig.name;
                let mut oracle_partials: Vec<_> = mapping
                    .iter()
                    .map(|(_loopvars, path, partial_sig)| {
                        println!("QQQQQ {sig:?}");
                        SplitInfoEntry {
                            pkg_inst_name: pkg_inst_name.clone(),
                            oracle_name: partial_sig.name.clone(),
                            path: path.clone(),
                            locals: partial_sig.partial_vars.clone(),
                            next: None,
                            elsenext: None,
                            original_sig: sig.clone(),
                        }
                    })
                    .collect();

                for i in 0..(oracle_partials.len() - 1) {
                    let cur = &oracle_partials[i];
                    let next = &oracle_partials[i + 1];

                    if let Some((next, maybe_elsenext)) = determine_next(cur, next) {
                        let cur = &mut oracle_partials[i];
                        cur.next = Some(next);
                        cur.elsenext = maybe_elsenext;
                    }
                }

                partials.extend(oracle_partials.into_iter());
            }
        }

        Ok((new_game, partials))
    }
}

impl Statement {
    fn needs_split(
        &self,
        sig_mapping: &HashMap<
            (String, OracleSig),
            Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
        >,
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

fn is_actually_not_split(
    transformed: &Vec<(Vec<Identifier>, SplitPath, CodeBlock, Vec<(String, Type)>)>,
) -> bool {
    if transformed.len() == 1 {
        let (_, path, _, _) = &transformed[0];
        *path[0].split_type() == SplitType::Plain
    } else {
        false
    }
}

fn transform_oracle(
    game: &mut Composition,
    pkg_offs: usize,
    osig: &OracleSig,
    sig_mapping: &mut HashMap<
        (String, OracleSig),
        Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
    >,
) -> Result<()> {
    let pkg_inst = &mut game.pkgs[pkg_offs];
    let pkg_inst_name = &pkg_inst.name;
    let oracle_offs = pkg_inst
        .pkg
        .oracles
        .iter()
        .position(|OracleDef { sig, .. }| sig == osig)
        .expect("there should be an oracle with this signature");
    let odef = &pkg_inst.pkg.oracles[oracle_offs];
    let oracle_name = &odef.sig.name;

    let mut new_oracles = vec![];
    let mut transformed = transform_codeblock(
        pkg_inst_name,
        oracle_name,
        &odef.code,
        SplitPath::empty(),
        vec![],
        vec![],
        sig_mapping,
    );

    // this means we are splitting into a single shard, i.e. not acutally splitting
    if is_actually_not_split(&transformed) {
        return Ok(());
    }

    let mapping_entry = sig_mapping
        .entry((pkg_inst_name.to_string(), osig.clone()))
        .or_default();

    // we treat the last item differently:
    // intermediate items get an empty return type,
    // the last item gets the original return type.
    let (last_loopvars, last_splitpath, last_code, last_locals) = transformed.pop().unwrap();

    for (loopvars, splitpath, oracle_code, oracle_locals) in transformed.clone().into_iter() {
        let new_args = loopvars
            .iter()
            .map(|var| (var.ident(), Type::Integer).clone())
            .chain(osig.args.clone().into_iter())
            .collect();

        let new_sig = SplitOracleSig {
            name: oracle_name.clone(),
            args: new_args,
            tipe: Type::Empty, // <-- note the difference
            partial_vars: oracle_locals.clone(),
            path: splitpath.clone(),
        };

        new_oracles.push(SplitOracleDef {
            sig: new_sig.clone(),
            code: oracle_code,
        });
        mapping_entry.push((loopvars.clone(), splitpath, new_sig))
    }

    let last_newargs = last_loopvars
        .iter()
        .map(|var| (var.ident(), Type::Integer).clone())
        .chain(osig.args.clone().into_iter())
        .collect();

    let sig = SplitOracleSig {
        name: oracle_name.clone(),
        args: last_newargs,
        tipe: osig.tipe.clone(), // <-- note the difference
        partial_vars: last_locals.clone(),
        path: last_splitpath.clone(),
    };

    new_oracles.push(SplitOracleDef {
        sig: sig.clone(),
        code: last_code,
    });
    mapping_entry.push((last_loopvars.clone(), last_splitpath, sig));

    pkg_inst.pkg.oracles.remove(oracle_offs);
    pkg_inst.pkg.split_oracles.extend(new_oracles);

    Ok(())
}

fn transform_codeblock(
    pkg_inst_name: &str,
    oracle_name: &str,
    code: &CodeBlock,
    prefix: SplitPath,
    mut locals: Vec<(String, Type)>,
    loopvars: Vec<Identifier>,
    sig_mapping: &mut HashMap<
        (String, OracleSig),
        Vec<(Vec<Identifier>, SplitPath, SplitOracleSig)>,
    >,
) -> Vec<(Vec<Identifier>, SplitPath, CodeBlock, Vec<(String, Type)>)> {
    let mut result = vec![];

    let mut split_indices = vec![];
    for i in 0..code.0.len() {
        println!("sig_mapping for {pkg_inst_name} - {oracle_name}: {sig_mapping:?}");
        if code.0[i].needs_split(sig_mapping) {
            split_indices.push((i, locals.clone()));
        }
        if let Some((decl_name, decl_type)) = get_declarations(&code.0[i]) {
            match locals
                .iter()
                .position(|(found_name, _)| found_name == &decl_name)
            {
                None => locals.push((decl_name, decl_type)),
                // we already typechecked, so this must hold:
                Some(idx) => assert_eq!(locals[idx].1, decl_type),
            };
        }
    }

    if split_indices.is_empty() {
        result.push((
            loopvars,
            prefix.extended(SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                SplitType::Plain,
                0..code.0.len(),
            )),
            code.clone(),
            locals,
        ));

        return result;
    }

    let mut cur_idx = 0;

    for (split_idx, split_locals) in split_indices {
        let mk_single_split_path_component = |split_type| {
            SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                split_type,
                split_idx..(split_idx + 1),
            )
        };

        // insert the plain oracles that contain the code between the statemnts that require a
        // split -- but only if there would be statements in that plain oracle
        if split_idx != cur_idx {
            let range = cur_idx..split_idx;
            let split_path_component = SplitPathComponent::new(
                pkg_inst_name,
                oracle_name,
                SplitType::Plain,
                range.clone(),
            );
            result.push((
                loopvars.clone(),
                prefix.extended(split_path_component),
                CodeBlock(code.0[range].to_vec()),
                split_locals.clone(),
            ))
        }

        let stmt = &code.0[split_idx];
        match stmt {
            Statement::IfThenElse(cond, ifcode, elsecode) => {
                result.push((
                    loopvars.clone(),
                    prefix.extended(mk_single_split_path_component(SplitType::IfCondition(
                        cond.clone(),
                    ))),
                    CodeBlock(vec![]),
                    split_locals.clone(),
                ));
                result.extend(transform_codeblock(
                    pkg_inst_name,
                    oracle_name,
                    ifcode,
                    prefix.extended(mk_single_split_path_component(SplitType::IfBranch)),
                    split_locals.clone(),
                    loopvars.clone(),
                    sig_mapping,
                ));
                result.extend(transform_codeblock(
                    pkg_inst_name,
                    oracle_name,
                    elsecode,
                    prefix.extended(mk_single_split_path_component(SplitType::ElseBranch)),
                    split_locals.clone(),
                    loopvars.clone(),
                    sig_mapping,
                ));
            }
            Statement::For(id_iter, from, to, code) => {
                let mut newloopvars = loopvars.clone();
                newloopvars.push(id_iter.clone());

                result.extend(transform_codeblock(
                    pkg_inst_name,
                    oracle_name,
                    code,
                    prefix.extended(mk_single_split_path_component(SplitType::ForStep(
                        id_iter.clone(),
                        from.clone(),
                        to.clone(),
                    ))),
                    split_locals,
                    newloopvars,
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
                let oracle_name = name;
                let (_, splits) = sig_mapping
                    .iter()
                    .find(|((inst_name, sig), _)| {
                        inst_name == target_inst_name && &sig.name == name
                    })
                    .unwrap();

                let (_, last_splitpath, last_sig) = splits.last().unwrap();

                result.extend(splits.into_iter().take(splits.len() - 1).map(
                    |(loopvars, splitpath, split_sig)| {
                        let name = &split_sig.name;
                        let invoc_target_data = InvocTargetData {
                            pkg_inst_name: target_inst_name.to_string(),
                            oracle_name: oracle_name.to_string(),
                        };
                        let mut newpath = prefix.extended(mk_single_split_path_component(
                            SplitType::Invoc(invoc_target_data),
                        ));
                        newpath.join(splitpath);
                        (
                            loopvars.clone(),
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

                let invoc_target_data = InvocTargetData {
                    pkg_inst_name: target_inst_name.to_string(),
                    oracle_name: oracle_name.to_string(),
                };

                let mut newpath = prefix.extended(mk_single_split_path_component(
                    SplitType::Invoc(invoc_target_data),
                ));
                newpath.join(&last_splitpath);
                result.push((
                    loopvars.clone(),
                    newpath,
                    CodeBlock(vec![Statement::InvokeOracle {
                        id: id.clone(),
                        opt_idx: opt_idx.clone(),
                        name: last_sig.name.clone(),
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

    let rest = &code.0[cur_idx + 1..];
    if !rest.is_empty() {
        result.push((
            loopvars.clone(),
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

    result
}

#[cfg(test)]
mod test {
    // use std::default::Default;
    //
    // use crate::{
    //     expressions::Expression,
    //     identifier::Identifier,
    //     statement::{CodeBlock, Statement},
    // };
    //
    // use super::*;
    //
    // #[test]
    // fn oracle_transform_splits_around_for() {
    //     let id_i = Identifier::new_scalar("i");
    //     let id_foo = Identifier::new_scalar("foo");
    //     let expr_i = Expression::Identifier(id_i.clone());
    //     let expr_foo = Expression::Identifier(id_foo.clone());
    //
    //     let code = CodeBlock(vec![
    //         Statement::Assign(
    //             id_foo.clone(),
    //             None,
    //             Expression::IntegerLiteral("2".to_string()),
    //         ),
    //         Statement::For(
    //             id_i.clone(),
    //             Expression::IntegerLiteral("0".to_string()),
    //             Expression::IntegerLiteral("10".to_string()),
    //             CodeBlock(vec![Statement::Assign(
    //                 Identifier::new_scalar("foo"),
    //                 None,
    //                 Expression::Add(Box::new(expr_i.clone()), Box::new(expr_foo.clone())),
    //             )]),
    //         ),
    //         Statement::Return(Some(expr_foo.clone())),
    //     ]);
    //
    //     let mut sig_mapping = Default::default();
    //
    //     let out = transform_codeblock(
    //         "the-pkg",
    //         "TheOracle",
    //         &code,
    //         SplitPath::empty(),
    //         vec![],
    //         &mut sig_mapping,
    //     );
    //
    //     println!("{out:#?}");
    // }
}

fn get_declarations(stmt: &Statement) -> Option<(String, Type)> {
    match stmt {
        Statement::Parse(_ids, _expr) => {
            todo!()
        }
        Statement::Assign(Identifier::Local(id_name), Some(idx), expr) => Some((
            id_name.to_string(),
            Type::Table(
                Box::new(idx.get_type().unwrap().clone()),
                Box::new(expr.get_type().unwrap().clone()),
            ),
        )),
        Statement::Assign(Identifier::Local(id_name), None, expr) => {
            Some((id_name.to_string(), expr.get_type().unwrap().clone()))
        }
        Statement::InvokeOracle {
            id: Identifier::Local(id_name),
            tipe: Some(tipe),
            opt_idx: Some(idx),
            ..
        }
        | Statement::Sample(Identifier::Local(id_name), Some(idx), _, tipe) => Some((
            id_name.to_string(),
            Type::Table(
                Box::new(idx.get_type().unwrap().clone()),
                Box::new(tipe.clone()),
            ),
        )),
        Statement::InvokeOracle {
            id: Identifier::Local(id_name),
            tipe: Some(tipe),
            opt_idx: None,
            ..
        }
        | Statement::Sample(Identifier::Local(id_name), None, _, tipe) => {
            Some((id_name.to_string(), tipe.clone()))
        }
        _ => None,
    }
}

/*
 * fn strip_plain(path) -> Option<path>;
 *
 * fn determine_what_to_do(partials[i], partials[i+1]) -> (next, elsenext);
 *
 * for i in 0..(len-1)  {
 *   (next, elsenext) = determine_what_to_do(oracle_partials[i], oracle_partials[i+1])
 *   oracle_partials[i].next = next;
 *   oracle_partials[i].elsenext = elsenext;
 *
 * }
 *
 * */

/*
 * /Plain
 *   ->
 * /Plain/ForStep/Plain
 *
 *
 * /Plain/ForStep/Plain
 *   ->
 * /Plain/IfCondition
 *
 *
 * /Plain/ForStep/Plain
 *   ->
 * /Plain/Invoc
 *
 *
 * /Plain/Invoc/callee_path
 *
 *
 * PRF.Eval:
 *   k<-Get()
 *   return f(k)
 *   ->
 *   Invoc/Invoc/Invoc/Forstep/Plain
 *   Invoc/Invoc/Plain
 *   Invoc/Plain
 *   Plain
 *
 *
 * KeyFilter.Get():
 *   k<-Get()
 *   if k == 0:
 *     k' <-$ rand();
 *     return k'
 *   ->
 *   Invoc/Invoc/Forstep/Plain
 *   Invoc/Plain
 *   Plain
 *
 *  Key.Get():
 *    Log()
 *    return k
 *    ->
 *    Invoc/ForStep/Plain
 *    Invoc/Plain
 *    Plain
 *
 *
 * Log.Log():
 *   for {...}
 *   return
 *   ->
 *   ForStep/Plain
 *   Plain
 * */
fn determine_next(
    cur: &SplitInfoEntry,
    next: &SplitInfoEntry,
) -> Option<(SplitPath, Option<SplitPath>)> {
    let mut cur_path = cur.path().clone();
    let next_path = next.path();
    let common_path = cur_path.longest_shared_prefix(next_path);

    // move up the tree
    while cur_path != common_path {
        let (head, basename) = cur_path.basename();
        cur_path = basename;

        let head = head.unwrap();

        match head.split_type() {
            SplitType::Plain => {
                // just skip these
            }
            SplitType::IfCondition(_) => {
                return Some((
                    /* next: */
                    cur_path.extended(SplitPathComponent::new(
                        head.pkg_inst_name(),
                        head.oracle_name(),
                        SplitType::IfBranch,
                        head.split_range().clone(),
                    )),
                    /* elsenext: */
                    Some(cur_path.extended(SplitPathComponent::new(
                        head.pkg_inst_name(),
                        head.oracle_name(),
                        SplitType::ElseBranch,
                        head.split_range().clone(),
                    ))),
                ));
            }
            SplitType::Invoc(_) => {
                return Some((
                    /* next: */ next_path.clone(),
                    /* elsenext: */ None,
                ));
            }
            SplitType::ForStep(_, _, _) => {
                return Some((
                    /* next: */ cur.path().clone(),
                    /* elsenext: */ Some(next_path.clone()),
                ));
            }
            // Due to treeification, we know that nothing comes after these:
            SplitType::IfBranch | SplitType::ElseBranch => return None,
        }
    }

    // move down the tree
    while &cur_path != next_path {
        let path_component = &next_path.path()[cur_path.len()];

        match path_component.split_type() {
            SplitType::Plain => {
                // just skip these
            }
            SplitType::Invoc(_) | SplitType::ForStep(_, _, _) | SplitType::IfCondition(_) => {
                // enter these unconditionally
                return Some((
                    /* next: */ next_path.clone(),
                    /* elsenext: */ None,
                ));
            }
            SplitType::IfBranch | SplitType::ElseBranch => {
                unreachable!("requires us to have left an IfCondition, which should have been caught earlier")
            }
        }

        cur_path = cur_path.extended(path_component.clone())
    }

    None
}
