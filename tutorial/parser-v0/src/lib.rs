mod parser;

use crate::parser::Parser;

/// Tag implementation
pub struct Tag<'t> {
    tag: &'t str,
}

impl<'i> Parser<'i> for Tag<'_> {
    type Output = (&'i str, &'i str);
    type Error = String;

    fn process(&mut self, input: &'i str) -> Result<Self::Output, Self::Error> {
        // compare tag with input
        let pos = input
            .as_bytes()
            .iter()
            .zip(self.tag.as_bytes().iter())
            .position(|(a, b)| a != b);
        if pos.is_some() {
            return Err(format!("The tag {} not found", self.tag));
        }

        let tag_len = self.tag.len();
        if input.len() < tag_len {
            Err(format!(
                "The input {} should be longer then tag {}",
                input, self.tag
            ))
        } else {
            let at = &input[..tag_len];
            let from = &input[tag_len..];
            Ok((from, at))
        }
    }
}

pub fn tag<'a>(tag: &'a str) -> impl Fn(&'a str) -> Result<(&'a str, &'a str), String> {
    |i: &'a str| {
        let mut parser = Tag { tag };
        parser.parse(i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_input(input: &str) -> Result<(&str, &str), String> {
        tag("abc")(input)
    }

    #[test]
    fn test_parse_success() {
        let (leftover_input, output) = parse_input("abcWorld").expect("Parsing Error");
        assert_eq!(leftover_input, "World");
        assert_eq!(output, "abc");
    }

    #[test]
    fn test_parse_fail() {
        assert!(parse_input("defWorld").is_err());
    }
}
