use super::Composition;

pub mod oraclelowlevelify;
pub mod typecheck;
pub mod varspecify;
pub mod treeify;
pub mod returnify;


pub trait Transformation {
    type Err;
    type Aux;

    fn transform(&self) -> Result<(Composition, Self::Aux), Self::Err>;
}
