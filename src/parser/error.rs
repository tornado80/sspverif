use std::fmt::Debug;

use pest::Span;
use thiserror::Error;

use crate::{expressions::Expression, transforms::resolvetypes, types::Type};

#[derive(Clone)]
pub struct SpanError {
    err: Error,
    start: usize,
    end: usize,
    source: Option<String>,
}

impl SpanError {
    pub fn new(err: Error, start: usize, end: usize) -> SpanError {
        SpanError {
            err,
            start,
            end,
            source: None,
        }
    }

    pub fn new_with_span<'span>(err: Error, span: pest::Span<'span>) -> SpanError {
        SpanError {
            err,
            start: span.start(),
            end: span.end(),
            source: None,
        }
    }

    pub fn with_source(self, source: String) -> SpanError {
        SpanError {
            source: Some(source),
            ..self
        }
    }
}

impl std::fmt::Display for SpanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let SpanError {
            err,
            start,
            end,
            source,
        } = self;
        write!(f, "parse error {err} at {start}..{end}")
    }
}

impl Debug for SpanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref source) = self.source {
            let span = Span::new(source, self.start, self.end).unwrap();
            f.debug_struct("SpanError")
                .field("err", &self.err)
                .field("span", &span)
                .finish()
        } else {
            f.debug_struct("SpanError")
                .field("err", &self.err)
                .field("start", &self.start)
                .field("end", &self.end)
                .finish()
        }
    }
}

impl std::error::Error for SpanError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.err)
    }
}

#[derive(Clone, Debug, Error)]
pub enum Error {
    #[error("looks like composition {game_name} doesn't have a compose block")]
    MissingComposeBlock { game_name: String },
    #[error(
        "the types parameter assignments don't match the package definition for package {pkg_name}"
    )]
    TypeParameterMismatch { pkg_name: String },
    #[error(
        "the const parameter assignments don't match the package definition for package {pkg_name}"
    )]
    PackageConstParameterMismatch {
        pkg_name: String,
        inst_name: String,
        bound_params: Vec<(String, Type)>,
        pkg_params: Vec<(String, Type)>,
    },
    #[error(
        "the const parameter assignments don't match the game definition for game {game_name}"
    )]
    GameConstParameterMismatch {
        game_name: String,
        inst_name: String,
        bound_params: Vec<(String, Expression)>,
        game_params: Vec<(String, Type)>,
    },
    #[error("assiged const parameter {param_name} to game {game_name} in instance {inst_name}, but the game does not declare that parameter")]
    GameConstParameterUndeclared {
        game_name: String,
        inst_name: String,
        param_name: String,
    },
    #[error("mapping: the game names don't match there definition in the {place}")]
    ReductionMappingMismatch { place: String },
    #[error("error resolving type: {0:?}")]
    ResolveTypesError(#[from] resolvetypes::ResolutionError),
    #[error("game {0} is undefined")]
    UndefinedGame(String),
    #[error("use of undefined identifier {0}")]
    UndefinedIdentifer(String),
    #[error("cannot use expression {0:?} in const block")]
    IllegalExpression(Expression),
}

impl Error {
    pub fn with_span<'span>(self, span: Span<'span>) -> SpanError {
        SpanError::new_with_span(self, span)
    }
}

pub type Result<T> = std::result::Result<T, SpanError>;
