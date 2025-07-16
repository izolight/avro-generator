use thiserror::Error;

/// Errors that can occur during code generation.
#[derive(Error, Debug)]
pub enum GeneratorError {
    #[error("Placeholder schema found during code generation: {0}")]
    PlaceholderFound(String),
    #[error("Mismatched type for default value. Expected {expected}, got {found}")]
    MismatchedDefaultType { expected: String, found: String },
    #[error("Decimal default value requires Decimal TypeIr")]
    DecimalDefaultValueMismatch,
    #[error("Failed to parse generated code: {0}")]
    SynError(#[from] syn::Error),
    #[error("Got multiple errors: {0:?}")]
    MultipleError(Vec<GeneratorError>),
    #[error("Chrono error: {0}")]
    ChronoError(#[from] chrono::ParseError),
    #[error("Uuid error: {0}")]
    UuidError(#[from] uuid::Error),
    #[error("Decimal parsing error: {0}")]
    DecimalParseError(#[from] rust_decimal::Error),
    #[error("BigDecimal parsing error: {0}")]
    BigDecimalParseError(#[from] bigdecimal::ParseBigDecimalError),
}

/// Errors that can occur during schema parsing.
#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Invalid default value for type '{expected}': {found}")]
    InvalidDefaultValue { expected: String, found: String },
    #[error("Unknown schema reference: {0}")]
    UnknownSchemaReference(String),
    #[error("Decimal default value has more fractional digits than specified scale")]
    DecimalScaleMismatch,
    #[error("Failed to parse BigInt from string: {0}")]
    BigIntParseError(String),
    #[error("Invalid duration string: {0}")]
    InvalidDurationString(String),
    #[error("Dependency not yet resolved: {0}")]
    DependencyNotResolved(String),
    #[error("Circular dependency detected or unresolvable schemas.")]
    CircularDependencyDetected,
    #[error("Failed to parse JSON: {0}")]
    JsonParseError(#[from] serde_json::Error),
}
