use super::Composition;

pub mod oraclelowlevelify;
pub mod returnify;
pub mod treeify;
pub mod typecheck;
pub mod varspecify;

pub trait Transformation {
    type Err;
    type Aux;

    fn transform(&self) -> Result<(Composition, Self::Aux), Self::Err>;
}

pub fn transform_all(
    comp: &Composition,
) -> Result<
    (Composition, <typecheck::Transform as Transformation>::Aux),
    <typecheck::Transform as Transformation>::Err,
> {
    let (comp, scope) = typecheck::Transform::new_with_empty_scope(comp.clone()).transform()?;
    let (comp, _) = treeify::Transformation(&comp)
        .transform()
        .expect("treeify transformation failed unexpectedly");
    let (comp, _) = returnify::Transformation(&comp)
        .transform()
        .expect("returnify transformation failed unexpectedly");
    let (comp, _) = varspecify::Transformation(&comp)
        .transform()
        .expect("varspecify transformation failed unexpectedly");
    let (comp, _) = oraclelowlevelify::Transformation(&comp)
        .transform()
        .expect("oraclelowlevelify transformation failed unexpectedly");

    Ok((comp, scope))
}
