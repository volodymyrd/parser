use crate::error::{FromExternalError, ParseError};
use crate::internal::Parser;

/// Applies a function returning a `Result` over the result of a parser.
///
/// ```rust
/// # use nom::{Err,error::ErrorKind, IResult, Parser};
/// use nom::character::complete::digit1;
/// use nom::combinator::map_res;
/// # fn main() {
///
/// let mut parse = map_res(digit1, |s: &str| s.parse::<u8>());
///
/// // the parser will convert the result of digit1 to a number
/// assert_eq!(parse.parse("123"), Ok(("", 123)));
///
/// // this will fail if digit1 fails
/// assert_eq!(parse.parse("abc"), Err(Err::Error(("abc", ErrorKind::Digit))));
///
/// // this will fail if the mapped function fails (a `u8` is too small to hold `123456`)
/// assert_eq!(parse.parse("123456"), Err(Err::Error(("123456", ErrorKind::MapRes))));
/// # }
/// ```
#[allow(dead_code)]
pub fn map_res<I: Clone, O, E: ParseError<I> + FromExternalError<I, E2>, E2, F, G>(
    parser: F,
    f: G,
) -> impl Parser<I, Output=O, Error=E>
    where
        F: Parser<I, Error=E>,
        G: FnMut(<F as Parser<I>>::Output) -> Result<O, E2>,
{
    parser.map_res(f)
}
