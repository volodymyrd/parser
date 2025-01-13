/// default error type, only contains the error's location and code
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Error<I> {
    /// position of the error in the input data
    pub input: I,
    /// nom error code
    pub code: ErrorKind,
}

impl<I> Error<I> {
    /// creates a new basic error
    pub fn new(input: I, code: ErrorKind) -> Error<I> {
        Error { input, code }
    }
}

impl<I> ParseError<I> for Error<I> {
    fn from_error_kind(input: I, kind: ErrorKind) -> Self {
        Error { input, code: kind }
    }

    fn append(_: I, _: ErrorKind, other: Self) -> Self {
        other
    }
}

/// Indicates which parser returned an error
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum ErrorKind {
    Tag,
    MapRes,
    TakeWhileMN,
}

/// This trait must be implemented by the error type of a nom parser.
pub trait ParseError<I>: Sized {
    /// Creates an error from the input position and an [ErrorKind]
    fn from_error_kind(input: I, kind: ErrorKind) -> Self;

    /// Combines an existing error with a new one created from the input
    /// position and an [ErrorKind]. This is useful when backtracking
    /// through a parse tree, accumulating error context on the way
    fn append(input: I, kind: ErrorKind, other: Self) -> Self;
}

/// This trait is required by the `map_res` combinator to integrate
/// error types from external functions, like [std::str::FromStr]
pub trait FromExternalError<I, E> {
    /// Creates a new error from an input position, an [ErrorKind] indicating the
    /// wrapping parser, and an external error
    fn from_external_error(input: I, kind: ErrorKind, e: E) -> Self;
}

impl<I, E> FromExternalError<I, E> for Error<I> {
    /// Create a new error from an input position and an external error
    fn from_external_error(input: I, kind: ErrorKind, _e: E) -> Self {
        Error { input, code: kind }
    }
}
