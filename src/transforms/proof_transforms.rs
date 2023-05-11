use std::collections::HashSet;

use crate::{
    expressions::Expression,
    identifier::Identifier,
    proof::GameInstance,
    statement::{CodeBlock, Statement},
    types::Type,
};

use super::{
    resolveoracles, resolvetypes, returnify, samplify, split_partial, tableinitialize, treeify,
    type_extract, typecheck, unwrapify, varspecify::var_specify_game_inst, GameTransform,
    Transformation,
};

pub struct EquivanceTransform;

impl super::ProofTransform for EquivanceTransform {
    type Err = typecheck::TypeCheckError;

    type Aux = Vec<(
        String,
        (typecheck::Scope, HashSet<Type>, samplify::SampleInfo),
    )>;

    fn transform_proof(
        &self,
        proof: &crate::proof::Proof,
    ) -> Result<(crate::proof::Proof, Self::Aux), Self::Err> {
        let new_game_instances: Vec<_> = proof
            .instances()
            .iter()
            .map(|game_inst| {
                let new_game = var_specify_game_inst(game_inst).unwrap();
                game_inst.with_other_game(new_game)
            })
            .collect();

        let results = new_game_instances.iter().map(transform_game_inst);
        let (instances, auxs) = itertools::process_results(results, |res| res.unzip())?;
        let proof = proof.with_new_instances(instances);

        Ok((proof, auxs))
    }
}

fn code_walker(code: &mut CodeBlock) -> Result<(), typecheck::TypeCheckError> {
    code.0.iter_mut().map(statement_walker).collect()
}

fn statement_walker(stmt: &mut Statement) -> Result<(), typecheck::TypeCheckError> {
    match stmt {
        Statement::Abort | Statement::Return(None) => Ok(()),
        Statement::Return(Some(expr)) => {
            expr.walk(&mut |expr| {
                if let Expression::Identifier(Identifier::Scalar(name)) = expr {};
                true
            });
            Ok(())
        }
        Statement::Assign(_, _, _) => todo!(),
        Statement::Parse(_, _) => todo!(),
        Statement::IfThenElse(_, _, _) => todo!(),
        Statement::Sample(_, _, _, _) => todo!(),
        Statement::For(_, _, _, _) => todo!(),
        Statement::InvokeOracle {
            id,
            opt_idx,
            name,
            args,
            target_inst_name,
            tipe,
        } => todo!(),
    }
}

fn transform_game_inst(
    game_inst: &GameInstance,
) -> Result<
    (
        GameInstance,
        (
            String,
            (typecheck::Scope, HashSet<Type>, samplify::SampleInfo),
        ),
    ),
    typecheck::TypeCheckError,
> {
    let comp = game_inst.as_game();

    let (comp, _) = resolvetypes::Transformation(comp)
        .transform()
        .expect("resolving user-defined types failed");
    let (comp, scope) = typecheck::Transformation::new_with_empty_scope(&comp).transform()?;
    let (comp, types) = type_extract::Transformation(&comp)
        .transform()
        .expect("type extraction transformation failed unexpectedly");
    let (comp, samplinginfo) = samplify::Transformation(&comp)
        .transform()
        .expect("samplify transformation failed unexpectedly");
    let (comp, _) = unwrapify::Transformation(&comp)
        .transform()
        .expect("unwrapify transformation failed unexpectedly");
    let (comp, _) = returnify::TransformNg
        .transform_game(&comp)
        .expect("returnify transformation failed unexpectedly");
    let (comp, _) = resolveoracles::Transformation(&comp)
        .transform()
        .expect("resolveoracles transformation failed unexpectedly");
    let (comp, _) = treeify::Transformation(&comp)
        .transform()
        .expect("treeify transformation failed unexpectedly");
    let (comp, _) = split_partial::SplitPartial
        .transform_game(&comp)
        .expect("split_partial transform failed unexpectedly");
    let (comp, _) = tableinitialize::Transformation(&comp)
        .transform()
        .expect("tableinitialize transformation failed unexpectedly");

    Ok((
        game_inst.with_other_game(comp),
        (
            game_inst.as_name().to_string(),
            (scope, types, samplinginfo),
        ),
    ))
}
