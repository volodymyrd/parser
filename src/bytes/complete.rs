use crate::error::ParseError;
use crate::internal::{Complete, Emit, IResult, OutputM};
use crate::traits::{Compare, Input};
use crate::Parser;
use std::marker::PhantomData;

/// Recognizes a pattern
///
/// The input data will be compared to the tag combinator's argument and will return the part of
/// the input that matches the argument
///
/// It will return `Err(Err::Error((_, ErrorKind::Tag)))` if the input doesn't match the pattern
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::complete::tag;
///
/// fn parser(s: &str) -> IResult<&str, &str> {
///   tag("Hello")(s)
/// }
///
/// assert_eq!(parser("Hello, World!"), Ok((", World!", "Hello")));
/// assert_eq!(parser("Something"), Err(Err::Error(Error::new("Something", ErrorKind::Tag))));
/// assert_eq!(parser(""), Err(Err::Error(Error::new("", ErrorKind::Tag))));
/// ```
#[allow(dead_code)]
pub fn tag<T, I, Error: ParseError<I>>(tag: T) -> impl Fn(I) -> IResult<I, I, Error>
where
    I: Input + Compare<T>,
    T: Input + Clone,
{
    move |i: I| {
        let mut parser = super::Tag {
            tag: tag.clone(),
            e: PhantomData,
        };

        parser.process::<OutputM<Emit, Emit, Complete>>(i)
    }
}

// Returns the longest (m <= len <= n) input slice that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return an `Err::Error((_, ErrorKind::TakeWhileMN))` if the pattern wasn't met or is out
/// of range (m <= len <= n).
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::complete::take_while_m_n;
/// use nom::AsChar;
///
/// fn short_alpha(s: &[u8]) -> IResult<&[u8], &[u8]> {
///   take_while_m_n(3, 6, AsChar::is_alpha)(s)
/// }
///
/// assert_eq!(short_alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"lengthy"), Ok((&b"y"[..], &b"length"[..])));
/// assert_eq!(short_alpha(b"latin"), Ok((&b""[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"ed"), Err(Err::Error(Error::new(&b"ed"[..], ErrorKind::TakeWhileMN))));
/// assert_eq!(short_alpha(b"12345"), Err(Err::Error(Error::new(&b"12345"[..], ErrorKind::TakeWhileMN))));
/// ```
#[allow(dead_code)]
pub fn take_while_m_n<F, I, Error: ParseError<I>>(
    m: usize,
    n: usize,
    cond: F,
) -> impl FnMut(I) -> IResult<I, I, Error>
where
    I: Input,
    F: Fn(<I as Input>::Item) -> bool,
{
    let mut parser = super::take_while_m_n(m, n, cond);

    move |i: I| parser.process::<OutputM<Emit, Emit, Complete>>(i)
}
