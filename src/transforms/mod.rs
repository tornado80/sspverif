use super::Composition;

pub mod oraclelowlevelify;
pub mod treeify;
pub mod typecheck;
pub mod varspecify;

pub trait Transformation {
    type Err;
    type Aux;

    fn transform(&self) -> Result<(Composition, Self::Aux), Self::Err>;
}
