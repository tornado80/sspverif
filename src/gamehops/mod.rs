use equivalence::Equivalence;
use reduction::Reduction;

pub mod equivalence;
pub mod reduction;
//
// TODO: add a HybridArgument variant
#[derive(Debug, Clone)]
pub enum GameHop {
    Reduction(Reduction),
    Equivalence(Equivalence),
}

impl GameHop {
    /// Returns `true` if the game hop is [`Reduction`].
    ///
    /// [`Reduction`]: GameHop::Reduction
    #[must_use]
    pub fn is_reduction(&self) -> bool {
        matches!(self, Self::Reduction(..))
    }

    /// Returns `true` if the game hop is [`Equivalence`].
    ///
    /// [`Equivalence`]: GameHop::Equivalence
    #[must_use]
    pub fn is_equivalence(&self) -> bool {
        matches!(self, Self::Equivalence(..))
    }

    pub fn as_reduction(&self) -> Option<&Reduction> {
        if let Self::Reduction(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_equivalence(&self) -> Option<&Equivalence> {
        if let Self::Equivalence(v) = self {
            Some(v)
        } else {
            None
        }
    }
}
