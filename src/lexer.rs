// https://spec.graphql.org/draft/

use std::iter;
use std::u8;

#[derive(Debug, Clone, PartialEq)]
pub struct Loc {
    start: usize,
    end: usize,
}

impl Loc {
    fn new(start: usize, end: usize) -> Self {
        return Self { start, end };
    }

    fn merge(&self, other: &Self) -> Self {
        return Self::new(
            std::cmp::min(self.start, other.start),
            std::cmp::min(self.end, other.end),
        );
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Annotated<T> {
    value: T,
    loc: Loc,
}

impl<T> Annotated<T> {
    fn new(value: T, loc: Loc) -> Self {
        return Self { value, loc };
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokenKind {
    // Lexical Tokens
    Punctuator,
    Name,
    IntValue,
    FloatValue,
    StringValue,

    // Ignored Tokens
    UnicodeBOM, // TODO
    WhiteSpace,
    LineTerminator,
    Comment,
    Comma,

    // tokens not defined in the spec
    NumericValue, // to indicate either IntValue or FloatValue
    Invalid,
}

impl TokenKind {
    pub fn is_ignored(&self) -> bool {
        return match self {
            TokenKind::UnicodeBOM
            | TokenKind::WhiteSpace
            | TokenKind::LineTerminator
            | TokenKind::Comment
            | TokenKind::Comma => true,
            _ => false,
        };
    }
}

pub type Token = Annotated<TokenKind>;

impl Token {
    pub fn get_str<'a>(&self, source: &'a str) -> &'a str {
        return &source[self.loc.start..self.loc.end];
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LexErrorKind {
    UnexpectedChar { expected: u8, got: u8 },
    UnexpectedEof,
    UnexpectedToken { expected: TokenKind, got: u8 },
    InvalidChar(u8),
}

pub type LexError = Annotated<LexErrorKind>;

pub struct Lexer<Iter: iter::Iterator<Item = u8>>
{
    src: iter::Peekable<Iter>,

    pos: usize,
    line: usize,
}

const SP: u8 = b'\x20'; // Space
const HT: u8 = b'\x09'; // Horizontal Tab
const CR: u8 = b'\x0d'; // Carriage Return
const NR: u8 = b'\x0a'; // New Line

fn is_digit(c: u8) -> bool {
    return match c {
        b'0'..=b'9' => true,
        _ => false,
    };
}

fn is_letter(c: u8) -> bool {
    return match c {
        b'a'..=b'z' | b'A'..=b'Z' => true,
        _ => false,
    };
}

fn is_name_start(c: u8) -> bool {
    return is_letter(c) || c == b'_';
}

fn is_name_continue(c: u8) -> bool {
    return is_letter(c) || is_digit(c) || c == b'_';
}

impl<'a> Lexer<std::str::Bytes<'a>> {
    pub fn from_str(str: &'a str) -> Self {
        return Lexer::from_iter(str.bytes());
    }
}

impl<Iter: iter::Iterator<Item = u8>> Lexer<Iter> {
    pub fn from_iter(iter: Iter) -> Self {
        return Self {
            src: iter.peekable(),
            pos: 0,
            line: 0,
        };
    }

    pub fn lex_to_tokens(&mut self) -> Vec<Token> {
        let mut tokens = Vec::<Token>::new();
        self.lex(&mut |token| {
            tokens.push(token);
            return None;
        });
        return tokens;
    }

    pub fn lex<F: FnMut(Token) -> Option<LexError>>(
        &mut self,
        cb: &mut F,
    ) -> Option<LexError> {
        loop {
            if let Some(token) = self.lex_whitespaces() {
                let err = cb(token);
                if err.is_some() {
                    return err;
                }
            } else if let Some(token) = self.lex_line_terminators() {
                let err = cb(token);
                if err.is_some() {
                    return err;
                }
            } else if let Some(token) = self.lex_int_or_float_value() {
                let err = cb(token);
                if err.is_some() {
                    return err;
                }
            } else if let Some(token) = self.lex_name() {
                let err = cb(token);
                if err.is_some() {
                    return err;
                }
            } else if let Some(token) = self.lex_punctuator() {
                let err = cb(token);
                if err.is_some() {
                    return err;
                }
            } else if self.peek().is_some() {
                let start = self.pos;
                self.consume();

                // TODO: to consume a unicode code-point in UTF-8 bytes
                let err = cb(Token::new(
                    TokenKind::Invalid,
                    self.loc(start, self.pos),
                ));
                if err.is_some() {
                    return err;
                }
            } else {
                // EOF
                break;
            }
        }
        return None;
    }

    fn consume(&mut self) {
        self.src.next().unwrap();
        self.pos += 1;
    }

    fn loc(&self, start: usize, end: usize) -> Loc {
        return Loc::new(start, end);
    }

    fn peek(&mut self) -> Option<u8> {
        return self.src.peek().copied();
    }

    fn expect_opt(&mut self, expected: u8) -> bool {
        if let Some(got) = self.peek() {
            if got == expected {
                self.consume();
                return true;
            }
        }
        return false;
    }

    #[must_use]
    fn expect(&mut self, expected: u8) -> Option<LexError> {
        if self.expect_opt(expected) {
            return None;
        }

        if let Some(got) = self.peek() {
            return Some(LexError::new(
                LexErrorKind::UnexpectedChar { expected, got },
                self.loc(self.pos, self.pos + 1),
            ));
        } else {
            return Some(LexError::new(
                LexErrorKind::UnexpectedEof,
                self.loc(self.pos, self.pos),
            ));
        }
    }

    fn lex_whitespaces(&mut self) -> Option<Token> {
        let start = self.pos;

        while let Some(c) = self.peek() {
            match c {
                SP | HT => {
                    self.consume();
                }
                _ => {
                    break;
                }
            };
        }

        if start != self.pos {
            return Some(Token::new(TokenKind::WhiteSpace, self.loc(start, self.pos)));
        } else {
            return None;
        }
    }

    fn lex_line_terminators(&mut self) -> Option<Token> {
        let start = self.pos;

        while let Some(c) = self.peek() {
            match c {
                NR => {
                    self.consume();
                    self.line += 1;
                }
                CR => {
                    self.consume();
                    self.line += 1;

                    if self.expect_opt(CR) {
                        self.consume();
                    }
                }
                _ => {
                    break;
                }
            };
        }

        if start != self.pos {
            return Some(Token::new(
                TokenKind::LineTerminator,
                self.loc(start, self.pos),
            ));
        } else {
            return None;
        }
    }

    // IntValue or FloatValue
    fn lex_int_or_float_value(&mut self) -> Option<Token> {
        let start = self.pos;

        // NegativeSign
        self.expect_opt(b'-');

        // IntegerPart
        while let Some(c) = self.peek() {
            if is_digit(c) {
                self.consume();

                if c == b'0' && self.pos == (start+1) {
                    let start_invalid = self.pos;
                    // "0" is ok, and make sure the next u8 is not digit.
                    // for example "0123" is an invalid token.
                    while let Some(ahead) = self.peek() {
                        if is_digit(ahead) {
                            self.consume();
                        } else {
                            break;
                        }
                    }

                    if self.pos != start_invalid {
                        return Some(Token::new(TokenKind::Invalid, self.loc(start, self.pos)));
                    }
                }
            } else {
                break;
            }
        }

        if self.pos == start {
            return None;
        }

        // fractional part or exponent part
        let mut has_fractional_part = false;
        if self.expect_opt(b'.') {
            // fractional part

            // digit+
            while let Some(c) = self.peek() {
                if is_digit(c) {
                    self.consume();
                    has_fractional_part = true;
                } else {
                    break;
                }
            }

            if !has_fractional_part {
                return Some(Token::new(TokenKind::Invalid, self.loc(start, self.pos)));
            }
        }

        let mut has_exponent_part = false;
        if self.expect_opt(b'e') || self.expect_opt(b'E') {
            // exponent part

            // sign
            let _ = self.expect_opt(b'-') || self.expect_opt(b'+');

            // digit+
            while let Some(c) = self.peek() {
                if is_digit(c) {
                    self.consume();
                    has_exponent_part = true;
                } else {
                    break;
                }
            }

            if !has_exponent_part {
                return Some(Token::new(TokenKind::Invalid, self.loc(start, self.pos)));
            }
        }

        if has_fractional_part || has_exponent_part {
            return Some(Token::new(TokenKind::FloatValue, self.loc(start, self.pos)));
        } else {
            return Some(Token::new(TokenKind::IntValue, self.loc(start, self.pos)));
        }
    }

    // Name
    fn lex_name(&mut self) -> Option<Token> {
        let start = self.pos;
        // NameStart
        if let Some(c) = self.peek() {
            if is_name_start(c) {
                self.consume();
            } else {
                return None;
            }
        } else {
            return None;
        }

        // NameContinue
        while let Some(c) = self.peek() {
            if is_name_continue(c) {
                self.consume();
            } else {
                break;
            }
        }

        return Some(Token::new(TokenKind::Name, self.loc(start, self.pos)));
    }

    // Punctuator
    fn lex_punctuator(&mut self) -> Option<Token> {
        let start = self.pos;

        if let Some(c) = self.peek() {
            match c {
                b'!' | b'$' | b'&' | b'(' | b')' | b':' | b'=' | b'@' | b'[' | b']' | b'{'
                | b'|' | b'}' => {
                    self.consume();
                    return Some(Token::new(TokenKind::Punctuator, self.loc(start, self.pos)));
                }
                b'.' => {
                    // ...
                    self.consume();
                    if self.expect(b'.').is_some() {
                        return Some(Token::new(TokenKind::Invalid, self.loc(start, self.pos)));
                    }
                    if self.expect(b'.').is_some() {
                        return Some(Token::new(TokenKind::Invalid, self.loc(start, self.pos)));
                    }
                    return Some(Token::new(TokenKind::Punctuator, self.loc(start, self.pos)));
                }
                _ => return None,
            }
        }

        return None;
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn lex_line_count() {
        let s = "foo\nbar\rbaz\r\nbax";
        let mut lexer = Lexer::from_str(s);
        let tokens = lexer.lex_to_tokens();
        assert_eq!(lexer.line, 4);
    }

    #[test]
    fn lex_invalid() {
        let invalid_values = ["01", "..", "/"];
        for s in invalid_values.iter() {
            let mut lexer = Lexer::from_str(s);
            let tokens = lexer.lex_to_tokens();

            assert_eq!(
                tokens,
                vec![Token::new(TokenKind::Invalid, Loc::new(0, s.len())),],
                "src={:?}",
                s
            );
        }
    }

    #[test]
    fn lex_int_value() {
        let int_values = ["0", "42", "-1234567890"];
        for s in int_values.iter() {
            let mut lexer = Lexer::from_str(s);
            let tokens = lexer.lex_to_tokens();

            assert_eq!(tokens.len(), 1);
            let token = tokens.get(0).unwrap();
            assert_eq!(token.get_str(s), *s);
            assert_eq!(token.loc, Loc::new(0, s.len()));
            assert_eq!(token.value, TokenKind::IntValue);
        }
    }

    #[test]
    fn lex_float_value() {
        let float_values = ["0.0", "42.195", "0.1e1", "0e0", "0E0", "0e+0", "0e-0"];
        for s in float_values.iter() {
            let mut lexer = Lexer::from_str(s);
            let tokens = lexer.lex_to_tokens();

            assert_eq!(tokens.len(), 1);

            let token = tokens.get(0).unwrap();
            assert_eq!(token.loc.start, 0);
            assert_eq!(token.loc.end, s.len());
            assert_eq!(token.value, TokenKind::FloatValue, "src={:?}", s);

            assert_eq!(token.get_str(s), *s);
        }
    }

    #[test]
    fn lex_schema() {
        let s = r#"
            schema {
                query: Query
                mutation: Mutation
                subscription: Subscription
            }
        "#;
        let src = String::from(s);
        let mut lexer = Lexer::from_iter(src.bytes());
        let tokens = lexer.lex_to_tokens();

        let token_kinds: Vec<TokenKind> = tokens
            .iter()
            .map(|token| {
                return token.value;
            })
            .filter(|token| {
                return !token.is_ignored();
            })
            .collect();

        assert_eq!(
            token_kinds,
            vec![
                TokenKind::Name,       // schema
                TokenKind::Punctuator, // {
                TokenKind::Name,       // query
                TokenKind::Punctuator, // :
                TokenKind::Name,       // Query,
                TokenKind::Name,       // mutation
                TokenKind::Punctuator, // :
                TokenKind::Name,       // Mutation,
                TokenKind::Name,       // subscription
                TokenKind::Punctuator, // :
                TokenKind::Name,       // Subscription,
                TokenKind::Punctuator, // }
            ]
        );
    }
}
