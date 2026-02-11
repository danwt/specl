//! Type checking error types.

use crate::types::Type;
use specl_syntax::Span;
use thiserror::Error;

/// A type checking error.
#[derive(Debug, Error)]
pub enum TypeError {
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: Type,
        found: Type,
        span: Span,
    },

    #[error("undefined variable: {name}")]
    UndefinedVariable { name: String, span: Span },

    #[error("undefined type: {name}")]
    UndefinedType { name: String, span: Span },

    #[error("undefined action: {name}")]
    UndefinedAction { name: String, span: Span },

    #[error("duplicate definition: {name}")]
    DuplicateDefinition { name: String, span: Span },

    #[error("invalid field access: type {ty} has no field {field}")]
    InvalidField { ty: Type, field: String, span: Span },

    #[error("cannot index into type {ty}")]
    NotIndexable { ty: Type, span: Span },

    #[error("cannot iterate over type {ty}")]
    NotIterable { ty: Type, span: Span },

    #[error("cannot call non-function type {ty}")]
    NotCallable { ty: Type, span: Span },

    #[error("wrong number of arguments: expected {expected}, found {found}")]
    ArityMismatch {
        expected: usize,
        found: usize,
        span: Span,
    },

    #[error("prime operator can only be applied to state variables")]
    InvalidPrime { span: Span },

    #[error("cannot unify types {a} and {b}")]
    UnificationFailure { a: Type, b: Type, span: Span },

    #[error("occurs check failed: type variable would create infinite type")]
    OccursCheck { span: Span },

    #[error("expression must be boolean, found {found}")]
    ExpectedBool { found: Type, span: Span },

    #[error("operands must be numeric, found {found}")]
    ExpectedNumeric { found: Type, span: Span },

    #[error("operands must be of the same type")]
    TypesNotEqual { left: Type, right: Type, span: Span },
}

impl TypeError {
    /// Get the source span of this error.
    pub fn span(&self) -> Span {
        match self {
            TypeError::TypeMismatch { span, .. }
            | TypeError::UndefinedVariable { span, .. }
            | TypeError::UndefinedType { span, .. }
            | TypeError::UndefinedAction { span, .. }
            | TypeError::DuplicateDefinition { span, .. }
            | TypeError::InvalidField { span, .. }
            | TypeError::NotIndexable { span, .. }
            | TypeError::NotIterable { span, .. }
            | TypeError::NotCallable { span, .. }
            | TypeError::ArityMismatch { span, .. }
            | TypeError::InvalidPrime { span }
            | TypeError::UnificationFailure { span, .. }
            | TypeError::OccursCheck { span }
            | TypeError::ExpectedBool { span, .. }
            | TypeError::ExpectedNumeric { span, .. }
            | TypeError::TypesNotEqual { span, .. } => *span,
        }
    }
}

/// Result type for type checking operations.
pub type TypeResult<T> = Result<T, TypeError>;
