use self::Needed::*;
use crate::error;
use crate::error::{ErrorKind, FromExternalError, ParseError};
use std::marker::PhantomData;
use std::num::NonZeroUsize;

/// Contains information on needed data if a parser returned `Incomplete`
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Needed {
    /// Needs more data, but we do not know how much
    Unknown,
    /// Contains the required data size in bytes
    Size(NonZeroUsize),
}

impl Needed {
    /// Creates `Needed` instance, returns `Needed::Unknown` if the argument is zero
    pub fn new(s: usize) -> Self {
        match NonZeroUsize::new(s) {
            Some(sz) => Size(sz),
            None => Unknown,
        }
    }

    /// Indicates if we know how many bytes we need
    pub fn is_known(&self) -> bool {
        *self != Unknown
    }

    /// Maps a `Needed` to `Needed` by applying a function to a contained `Size` value.
    #[inline]
    pub fn map<F: Fn(NonZeroUsize) -> usize>(self, f: F) -> Needed {
        match self {
            Unknown => Unknown,
            Size(n) => Needed::new(f(n)),
        }
    }
}

/// The `Err` enum indicates the parser was not successful
///
/// It has three cases:
///
/// * `Incomplete` indicates that more data is needed to decide. The `Needed` enum
///   can contain how many additional bytes are necessary. If you are sure your parser
///   is working on full data, you can wrap your parser with the `complete` combinator
///   to transform that case in `Error`
/// * `Error` means some parser did not succeed, but another one might (as an example,
///   when testing different branches of an `alt` combinator)
/// * `Failure` indicates an unrecoverable error. For example, when a prefix has been
///   recognised and the next parser has been confirmed, if that parser fails, then the
///   entire process fails; there are no more parsers to try.
///
/// Distinguishing `Failure` this from `Error` is only relevant inside the parser's code. For
/// external consumers, both mean that parsing failed.
///
/// See also: [`Finish`].
///
#[derive(Debug, Clone, PartialEq)]
pub enum Err<Failure, Error = Failure> {
    /// There was not enough data
    Incomplete(Needed),
    /// The parser had an error (recoverable)
    Error(Error),
    /// The parser had an unrecoverable error: we got to the right
    /// branch and we know other branches won't work, so backtrack
    /// as fast as possible
    Failure(Failure),
}

/// Holds the result of parsing functions
///
/// It depends on the input type `I`, the output type `O`, and the error type `E`
/// (by default `(I, nom::ErrorKind)`)
///
/// The `Ok` side is a pair containing the remainder of the input (the part of the data that
/// was not parsed) and the produced value. The `Err` side contains an instance of `nom::Err`.
///
/// Outside of the parsing code, you can use the [Finish::finish] method to convert
/// it to a more common result type
pub type IResult<I, O, E = error::Error<I>> = Result<(I, O), Err<E>>;

/// Parser result type
///
/// * `Ok` branch: a tuple of the remaining input data, and the output value.
///   The output value is of the `O` type if the output mode was [Emit], and `()`
///   if the mode was [Check]
/// * `Err` branch: an error of the `E` type if the erroor mode was [Emit], and `()`
///   if the mode was [Check]
pub type PResult<OM, I, O, E> = Result<
    (I, <<OM as OutputMode>::Output as Mode>::Output<O>),
    Err<E, <<OM as OutputMode>::Error as Mode>::Output<E>>,
>;

/// Produces a value. This is the default behaviour for parsers
pub struct Emit;

impl Mode for Emit {
    type Output<T> = T;

    #[inline(always)]
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T> {
        f()
    }

    #[inline(always)]
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U> {
        f(x)
    }

    #[inline(always)]
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(
        x: Self::Output<T>,
        y: Self::Output<U>,
        f: F,
    ) -> Self::Output<V> {
        f(x, y)
    }
}

/// Indicates that the input data is streaming: more data may be available later
pub struct Streaming;

impl IsStreaming for Streaming {
    fn incomplete<E, F: FnOnce() -> E>(needed: Needed, _err_f: F) -> Err<E> {
        Err::Incomplete(needed)
    }

    #[inline]
    fn is_streaming() -> bool {
        true
    }
}

/// Parser mode: influences how combinators build values
///
/// the [Parser] trait is generic over types implementing [Mode]. Its method are
/// called to produce and manipulate output values or errors.
///
/// The main implementations of this trait are:
/// * [Emit]: produce a value
/// * [Check]: apply the parser but do not generate a value
pub trait Mode {
    /// The output type that may be generated
    type Output<T>;

    /// Produces a value
    fn bind<T, F: FnOnce() -> T>(f: F) -> Self::Output<T>;

    /// Applies a function over the produced value
    fn map<T, U, F: FnOnce(T) -> U>(x: Self::Output<T>, f: F) -> Self::Output<U>;

    /// Combines two values generated by previous parsers
    fn combine<T, U, V, F: FnOnce(T, U) -> V>(
        x: Self::Output<T>,
        y: Self::Output<U>,
        f: F,
    ) -> Self::Output<V>;
}

/// Specifies the behaviour when a parser encounters an error that could be due to partial ata
/// Specifies the behaviour when a parser encounters an error that could be due to partial ata
pub trait IsStreaming {
    /// called by parsers on partial data errors
    /// * `needed` can hold the amount of additional data the parser would need to decide
    /// * `err_f`: produces the error when in "complete" mode
    fn incomplete<E, F: FnOnce() -> E>(needed: Needed, err_f: F) -> Err<E>;
    /// Indicates whether the data is in streaming mode or not
    fn is_streaming() -> bool;
}

/// Holds the parser execution modifiers: output [Mode], error [Mode] and
/// streaming behaviour for input data
pub struct OutputM<M: Mode, EM: Mode, S: IsStreaming> {
    m: PhantomData<M>,
    em: PhantomData<EM>,
    s: PhantomData<S>,
}

impl<M: Mode, EM: Mode, S: IsStreaming> OutputMode for OutputM<M, EM, S> {
    type Output = M;
    type Error = EM;
    type Incomplete = S;
}

/// Trait Defining the parser's execution
///
/// The same parser implementation can vary in behaviour according to the chosen
/// output mode
pub trait OutputMode {
    /// Defines the [Mode] for the output type. [Emit] will generate the value, [Check] will
    /// apply the parser but will only generate `()` if successful. This can be used when
    /// verifying that the input data conforms to the format without having to generate any
    /// output data
    type Output: Mode;
    /// Defines the [Mode] for the output type. [Emit] will generate the value, [Check] will
    /// apply the parser but will only generate `()` if an error happened. [Emit] should be
    /// used when we want to handle the error and extract useful information from it. [Check]
    /// is used when we just want to know if parsing failed and reject the data quickly.
    type Error: Mode;
    /// Indicates whether the input data is "complete", ie we already have the entire data in the
    /// buffer, or if it is "streaming", where more data can be added later in the buffer. In
    /// streaming mode, the parser will understand that a failure may mean that we are missing
    /// data, and will return a specific error branch, [Err::Incomplete] to signal it. In complete
    /// mode, the parser will generate a normal error
    type Incomplete: IsStreaming;
}

/// Indicates that the input data is complete: no more data may be added later
pub struct Complete;

impl IsStreaming for Complete {
    fn incomplete<E, F: FnOnce() -> E>(_needed: Needed, err_f: F) -> Err<E> {
        Err::Error(err_f())
    }

    #[inline]
    fn is_streaming() -> bool {
        false
    }
}

/// Implementation of `Parser::map_res`
pub struct MapRes<F, G> {
    f: F,
    g: G,
}

impl<I, O2, E2, F, G> Parser<I> for MapRes<F, G>
where
    I: Clone,
    <F as Parser<I>>::Error: FromExternalError<I, E2>,
    F: Parser<I>,
    G: FnMut(<F as Parser<I>>::Output) -> Result<O2, E2>,
{
    type Output = O2;
    type Error = <F as Parser<I>>::Error;

    fn process<OM: OutputMode>(&mut self, i: I) -> PResult<OM, I, Self::Output, Self::Error> {
        let (input, o1) = self
            .f
            .process::<OutputM<Emit, OM::Error, OM::Incomplete>>(i.clone())?;

        match (self.g)(o1) {
            Ok(o2) => Ok((input, OM::Output::bind(|| o2))),
            Err(e) => Err(Err::Error(OM::Error::bind(|| {
                <F as Parser<I>>::Error::from_external_error(i, ErrorKind::MapRes, e)
            }))),
        }
    }
}

/// All nom parsers implement this trait
pub trait Parser<Input> {
    /// Type of the produced value
    type Output;
    /// Error type of this parser
    type Error: ParseError<Input>;

    /// A parser takes in input type, and returns a `Result` containing
    /// either the remaining input and the output value, or an error
    #[inline]
    fn parse(&mut self, input: Input) -> IResult<Input, Self::Output, Self::Error> {
        self.process::<OutputM<Emit, Emit, Streaming>>(input)
    }

    /// A parser takes in input type, and returns a `Result` containing
    /// either the remaining input and the output value, or an error
    #[inline]
    fn parse_complete(&mut self, input: Input) -> IResult<Input, Self::Output, Self::Error> {
        self.process::<OutputM<Emit, Emit, Complete>>(input)
    }

    /// A parser takes in input type, and returns a `Result` containing
    /// either the remaining input and the output value, or an error
    fn process<OM: OutputMode>(
        &mut self,
        input: Input,
    ) -> PResult<OM, Input, Self::Output, Self::Error>;

    /// Applies a function returning a `Result` over the result of a parser.
    fn map_res<G, O2, E2>(self, g: G) -> MapRes<Self, G>
    where
        G: FnMut(Self::Output) -> Result<O2, E2>,
        Self::Error: FromExternalError<Input, E2>,
        Self: core::marker::Sized,
    {
        MapRes { f: self, g }
    }
}

macro_rules! impl_parser_for_tuple {
  ($($parser:ident $output:ident),+) => (
    #[allow(non_snake_case)]
    impl<I, $($output),+, E: ParseError<I>, $($parser),+> Parser<I> for ($($parser),+,)
    where
      $($parser: Parser<I, Output = $output, Error = E>),+
    {
      type Output = ($($output),+,);
      type Error = E;

      #[inline(always)]
      fn process<OM: OutputMode>(&mut self, i: I) -> PResult<OM, I, Self::Output, Self::Error> {
        let ($(ref mut $parser),+,) = *self;

        // FIXME: is there a way to avoid producing the output values?
        $(let(i, $output) = $parser.process::<OutputM<Emit, OM::Error, OM::Incomplete>>(i)?;)+

        // ???
        Ok((i, OM::Output::bind(|| ($($output),+,))))
      }
    }
  )
}

impl<I, O, E: ParseError<I>, F> Parser<I> for F
where
    F: FnMut(I) -> IResult<I, O, E>,
{
    type Output = O;
    type Error = E;

    fn process<OM: OutputMode>(&mut self, i: I) -> PResult<OM, I, Self::Output, Self::Error> {
        let (i, o) = self(i).map_err(|e| match e {
            Err::Incomplete(i) => Err::Incomplete(i),
            Err::Error(e) => Err::Error(OM::Error::bind(|| e)),
            Err::Failure(e) => Err::Failure(e),
        })?;
        Ok((i, OM::Output::bind(|| o)))
    }
}

macro_rules! impl_parser_for_tuples {
    ($parser1:ident $output1:ident, $($parser:ident $output:ident),+) => {
        impl_parser_for_tuples!(__impl $parser1 $output1; $($parser $output),+);
    };
    (__impl $($parser:ident $output:ident),+; $parser1:ident $output1:ident $(,$parser2:ident $output2:ident)*) => {
        impl_parser_for_tuple!($($parser $output),+);
        impl_parser_for_tuples!(__impl $($parser $output),+, $parser1 $output1; $($parser2 $output2),*);
    };
    (__impl $($parser:ident $output:ident),+;) => {
        impl_parser_for_tuple!($($parser $output),+);
    }
}

impl_parser_for_tuples!(P1 O1, P2 O2, P3 O3);
