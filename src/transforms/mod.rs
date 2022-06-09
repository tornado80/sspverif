use crate::package::Composition;

pub mod resolveoracles;
pub mod returnify;
pub mod treeify;
pub mod typecheck;
pub mod unwrapify;
pub mod varspecify;
pub mod samplify;

pub trait Transformation {
    type Err;
    type Aux;

    fn transform(&self) -> Result<(Composition, Self::Aux), Self::Err>;
}

pub fn transform_all(
    comp: &Composition,
) -> Result<
        (Composition,
         <typecheck::Transformation as Transformation>::Aux,
         <samplify::Transformation as Transformation>::Aux),
    <typecheck::Transformation as Transformation>::Err,
> {
    let (comp, scope) = typecheck::Transformation::new_with_empty_scope(comp.clone()).transform()?;
    let (comp, samplinginfo) = samplify::Transformation(&comp)
        .transform()
        .expect("samplify transformation failed unexpectedly");
    let (comp, _) = unwrapify::Transformation(&comp)
        .transform()
        .expect("unwrapify transformation failed unexpectedly");
    let (comp, _) = returnify::Transformation(&comp)
        .transform()
        .expect("returnify transformation failed unexpectedly");
    let (comp, _) = varspecify::Transformation(&comp)
        .transform()
        .expect("varspecify transformation failed unexpectedly");
    let (comp, _) = resolveoracles::Transformation(&comp)
        .transform()
        .expect("resolveoracles transformation failed unexpectedly");
    let (comp, _) = treeify::Transformation(&comp)
        .transform()
        .expect("treeify transformation failed unexpectedly");

    Ok((comp, scope, samplinginfo))
}
