use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("{0}")]
    DuplicateGlobal(String),

    #[error("Empty variable context")]
    EmptyContext,

    #[error("{0}")]
    FromInt(#[from] std::num::TryFromIntError),

    #[error("{0}")]
    InfiniteType(String),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Parser error: {0}")]
    ParserError(#[from] crate::lang::parser::Error),

    #[error("Pattern match: {0}")]
    PatternMatch(String),

    #[error("{0}")]
    RuntimeError(String),

    #[error("{0}")]
    RustyLine(#[from] rustyline::error::ReadlineError),

    #[error("{0}")]
    TypeMismatch(String),

    #[error("{0}")]
    UnknownOperator(String),

    #[error("{0}")]
    VariableNotFound(String),
}

pub type Result<T> = std::result::Result<T, Error>;
