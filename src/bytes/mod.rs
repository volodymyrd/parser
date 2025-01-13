use crate::error::{ErrorKind, ParseError};
use crate::{Compare, CompareResult, Input};
use crate::{Err, IsStreaming, Mode, Needed, OutputMode, PResult, Parser};
use std::marker::PhantomData;

pub mod complete;

/// Tag implementation
pub struct Tag<T, E> {
    tag: T,
    e: PhantomData<E>,
}

impl<I, Error: ParseError<I>, T> Parser<I> for Tag<T, Error>
where
    I: Input + Compare<T>,
    T: Input + Clone,
{
    type Output = I;

    type Error = Error;

    fn process<OM: OutputMode>(&mut self, i: I) -> PResult<OM, I, Self::Output, Self::Error> {
        let tag_len = self.tag.input_len();
        let t = self.tag.clone();

        match i.compare(t) {
            CompareResult::Ok => Ok((i.take_from(tag_len), OM::Output::bind(|| i.take(tag_len)))),
            CompareResult::Incomplete => {
                if OM::Incomplete::is_streaming() {
                    Err(Err::Incomplete(Needed::new(tag_len - i.input_len())))
                } else {
                    Err(Err::Error(OM::Error::bind(|| {
                        let e: ErrorKind = ErrorKind::Tag;
                        Error::from_error_kind(i, e)
                    })))
                }
            }
            CompareResult::Error => Err(Err::Error(OM::Error::bind(|| {
                let e: ErrorKind = ErrorKind::Tag;
                Error::from_error_kind(i, e)
            }))),
        }
    }
}

/// Returns the longest (m <= len <= n) input slice  that matches the predicate.
///
/// The parser will return the longest slice that matches the given predicate *(a function that
/// takes the input and returns a bool)*.
///
/// It will return an `Err::Error((_, ErrorKind::TakeWhileMN))` if the pattern wasn't met.
/// # Streaming Specific
/// *Streaming version* will return a `Err::Incomplete(Needed::new(1))`  if the pattern reaches the end of the input or is too short.
///
/// # Example
/// ```rust
/// # use nom::{Err, error::{Error, ErrorKind}, Needed, IResult};
/// use nom::bytes::streaming::take_while_m_n;
/// use nom::character::is_alphabetic;
///
/// fn short_alpha(s: &[u8]) -> IResult<&[u8], &[u8]> {
///   take_while_m_n(3, 6, is_alphabetic)(s)
/// }
///
/// assert_eq!(short_alpha(b"latin123"), Ok((&b"123"[..], &b"latin"[..])));
/// assert_eq!(short_alpha(b"lengthy"), Ok((&b"y"[..], &b"length"[..])));
/// assert_eq!(short_alpha(b"latin"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(short_alpha(b"ed"), Err(Err::Incomplete(Needed::new(1))));
/// assert_eq!(short_alpha(b"12345"), Err(Err::Error(Error::new(&b"12345"[..], ErrorKind::TakeWhileMN))));
/// ```
#[allow(dead_code)]
pub fn take_while_m_n<F, I, Error: ParseError<I>>(
    m: usize,
    n: usize,
    predicate: F,
) -> impl Parser<I, Output = I, Error = Error>
where
    I: Input,
    F: Fn(<I as Input>::Item) -> bool,
{
    TakeWhileMN {
        m,
        n,
        predicate,
        e: PhantomData,
    }
}

/// Parser implementation for [take_while_m_n]
pub struct TakeWhileMN<F, E> {
    m: usize,
    n: usize,
    predicate: F,
    e: PhantomData<E>,
}

impl<I, Error: ParseError<I>, F> Parser<I> for TakeWhileMN<F, Error>
where
    I: Input,
    F: Fn(<I as Input>::Item) -> bool,
{
    type Output = I;
    type Error = Error;

    fn process<OM: OutputMode>(
        &mut self,
        input: I,
    ) -> crate::PResult<OM, I, Self::Output, Self::Error> {
        let mut count = 0;
        for (i, (index, item)) in input.iter_indices().enumerate() {
            if i == self.n {
                return Ok((
                    input.take_from(index),
                    OM::Output::bind(|| input.take(index)),
                ));
            }

            if !(self.predicate)(item) {
                if i >= self.m {
                    return Ok((
                        input.take_from(index),
                        OM::Output::bind(|| input.take(index)),
                    ));
                } else {
                    return Err(Err::Error(OM::Error::bind(|| {
                        Error::from_error_kind(input, ErrorKind::TakeWhileMN)
                    })));
                }
            }
            count += 1;
        }

        let input_len = input.input_len();
        if OM::Incomplete::is_streaming() {
            let needed = if self.m > input_len {
                self.m - input_len
            } else {
                1
            };
            Err(Err::Incomplete(Needed::new(needed)))
        } else if count >= self.m {
            Ok((
                input.take_from(input_len),
                OM::Output::bind(|| input.take(input_len)),
            ))
        } else {
            Err(Err::Error(OM::Error::bind(|| {
                Error::from_error_kind(input, ErrorKind::TakeWhileMN)
            })))
        }
    }
}
