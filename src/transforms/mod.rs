use super::Composition;
use std::error::Error;

pub mod typecheck;

trait Transformation {
    type E: Error;

    fn transform(&self) -> Result<Composition, Self::E>;
}
