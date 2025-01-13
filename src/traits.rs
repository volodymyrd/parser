use std::str::{CharIndices, Chars};

/// Parser input types must implement this trait
pub trait Input: Clone + Sized {
    /// The current input type is a sequence of that `Item` type.
    ///
    /// Example: `u8` for `&[u8]` or `char` for `&str`
    type Item;

    /// An iterator over the input type, producing the item
    type Iter: Iterator<Item = Self::Item>;

    /// An iterator over the input type, producing the item and its byte position
    /// If we're iterating over `&str`, the position
    /// corresponds to the byte index of the character
    type IterIndices: Iterator<Item = (usize, Self::Item)>;

    /// Calculates the input length, as indicated by its name,
    /// and the name of the trait itself
    fn input_len(&self) -> usize;

    /// Returns a slice of `index` bytes. panics if index > length
    fn take(&self, index: usize) -> Self;
    /// Returns a slice starting at `index` bytes. panics if index > length
    fn take_from(&self, index: usize) -> Self;

    /// Returns an iterator over the elements and their byte offsets
    fn iter_indices(&self) -> Self::IterIndices;
}

impl<'a> Input for &'a str {
    type Item = char;
    type Iter = Chars<'a>;
    type IterIndices = CharIndices<'a>;

    fn input_len(&self) -> usize {
        self.len()
    }

    #[inline]
    fn take(&self, index: usize) -> Self {
        &self[..index]
    }

    #[inline]
    fn take_from(&self, index: usize) -> Self {
        &self[index..]
    }

    #[inline]
    fn iter_indices(&self) -> Self::IterIndices {
        self.char_indices()
    }
}

/// Indicates whether a comparison was successful, an error, or
/// if more data was needed
#[derive(Debug, Eq, PartialEq)]
pub enum CompareResult {
    /// Comparison was successful
    Ok,
    /// We need more data to be sure
    Incomplete,
    /// Comparison failed
    Error,
}

/// Abstracts comparison operations
pub trait Compare<T> {
    /// Compares self to another value for equality
    fn compare(&self, t: T) -> CompareResult;
    /// Compares self to another value for equality
    /// independently of the case.
    ///
    /// Warning: for `&str`, the comparison is done
    /// by lowercasing both strings and comparing
    /// the result. This is a temporary solution until
    /// a better one appears
    fn compare_no_case(&self, t: T) -> CompareResult;
}

fn lowercase_byte(c: u8) -> u8 {
    match c {
        b'A'..=b'Z' => c - b'A' + b'a',
        _ => c,
    }
}

impl<'b> Compare<&'b [u8]> for &[u8] {
    #[inline(always)]
    fn compare(&self, t: &'b [u8]) -> CompareResult {
        let pos = self.iter().zip(t.iter()).position(|(a, b)| a != b);

        match pos {
            Some(_) => CompareResult::Error,
            None => {
                if self.len() >= t.len() {
                    CompareResult::Ok
                } else {
                    CompareResult::Incomplete
                }
            }
        }
    }

    #[inline(always)]
    fn compare_no_case(&self, t: &'b [u8]) -> CompareResult {
        if self
            .iter()
            .zip(t)
            .any(|(a, b)| lowercase_byte(*a) != lowercase_byte(*b))
        {
            CompareResult::Error
        } else if self.len() < t.len() {
            CompareResult::Incomplete
        } else {
            CompareResult::Ok
        }
    }
}

impl<'b> Compare<&'b str> for &str {
    #[inline(always)]
    fn compare(&self, t: &'b str) -> CompareResult {
        self.as_bytes().compare(t.as_bytes())
    }

    //FIXME: this version is too simple and does not use the current locale
    #[inline(always)]
    fn compare_no_case(&self, t: &'b str) -> CompareResult {
        let pos = self
            .chars()
            .zip(t.chars())
            .position(|(a, b)| a.to_lowercase().ne(b.to_lowercase()));

        match pos {
            Some(_) => CompareResult::Error,
            None => {
                if self.len() >= t.len() {
                    CompareResult::Ok
                } else {
                    CompareResult::Incomplete
                }
            }
        }
    }
}
