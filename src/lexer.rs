// https://spec.graphql.org/draft/

use std::char;
use std::iter;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    // TODO: recognize them in lex()
    UnicodeBOM,
    WhiteSpace,
    LineTerminator,
    Comment,
    Comma,

    // abstract token used in errors
    NumericValue, // either IntValue or FloatValue
}

pub type Token = Annotated<TokenKind>;

impl Token {
    pub fn get_str<'a>(&self, source: &'a String) -> &'a str {
        return &source[self.loc.start..self.loc.end];
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LexErrorKind {
    UnexpectedChar { expected: char, got: char },
    UnexpectedEof,
    UnexpectedToken { expected: TokenKind, got: char },
    InvalidChar(char),
}

pub type LexError = Annotated<LexErrorKind>;

pub struct Lexer<Iter>
where
    Iter: iter::Iterator<Item = char>,
{
    src: iter::Peekable<Iter>,

    pos: usize,
    line: usize,
}

const CR: char = '\x0d'; // Carriage Return
const NR: char = '\x0a'; // New Line

impl<'a> Lexer<std::str::Chars<'a>> {
    pub fn from_str<StrLike: Into<String>>(src: StrLike) -> Self {
        let s = src.into();
        return Self::from_iter(s.chars());
    }
}

impl<Iter: iter::Iterator<Item = char>> Lexer<Iter> {
    pub fn from_iter(iter: Iter) -> Self {
        return Self {
            src: iter.peekable(),
            pos: 0,
            line: 0,
        };
    }

    pub fn lex_to_tokens(&mut self) -> Result<Vec<Token>, LexError> {
        let mut tokens: Vec<Token> = Vec::new();
        if let Some(err) = self.lex(&mut |result| {
            return match result {
                Ok(token) => {
                    tokens.push(token);
                    None
                }
                Err(err) => Some(err),
            };
        }) {
            return Err(err);
        } else {
            return Ok(tokens);
        }
    }

    pub fn lex<F: FnMut(Result<Token, LexError>) -> Option<LexError>>(
        &mut self,
        cb: &mut F,
    ) -> Option<LexError> {
        loop {
            self.skip_whitespaces();

            if let Ok(token) = self.lex_numeric() {
                let err = cb(Ok(token));
                if err.is_some() {
                    return err;
                }
            } else if let Ok(token) = self.lex_name() {
                let err = cb(Ok(token));
                if err.is_some() {
                    return err;
                }
            } else if let Ok(token) = self.lex_punctuator() {
                let err = cb(Ok(token));
                if err.is_some() {
                    return err;
                }
            } else if let Some(c) = self.peek() {
                let err = cb(Err(LexError::new(
                    LexErrorKind::InvalidChar(c),
                    self.loc(self.pos, self.pos),
                )));
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

    fn next(&mut self) {
        self.src.next().unwrap();
        self.pos += 1;
    }

    fn loc(&self, start: usize, end: usize) -> Loc {
        return Loc::new(start, end);
    }

    fn skip_whitespaces(&mut self) {
        while let Some(c) = self.peek() {
            match c {
                ' ' | '\t' => {
                    self.next();
                }
                NR => {
                    self.next();
                    self.line += 1;
                }
                CR => {
                    self.next();
                    self.line += 1;

                    if self.expect_opt(CR) {
                        self.next();
                    }
                }
                _ => {
                    return;
                }
            }
        }
    }

    fn peek(&mut self) -> Option<char> {
        return self.src.peek().copied();
    }

    fn expect_opt(&mut self, expected: char) -> bool {
        if let Some(got) = self.peek() {
            if got == expected {
                self.next();
                return true;
            }
        }
        return false;
    }

    fn expect(&mut self, expected: char) -> Option<LexError> {
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

    fn unexpected_token_error(&mut self, expected: TokenKind) -> LexError {
        if let Some(got) = self.peek() {
            return LexError::new(
                LexErrorKind::UnexpectedToken { expected, got },
                self.loc(self.pos, self.pos + 1),
            );
        } else {
            return LexError::new(LexErrorKind::UnexpectedEof, self.loc(self.pos, self.pos));
        }
    }

    // IntValue or FloatValue
    fn lex_numeric(&mut self) -> Result<Token, LexError> {
        let start = self.pos;

        // NegativeSign
        self.expect_opt('-');

        // IntegerPart
        let mut has_int_part = false;
        while let Some(c) = self.peek() {
            if c.is_numeric() {
                self.next();
                has_int_part = true;

                if c == '0' && !has_int_part {
                    // ok, and make sure the next char is not digit nor NameStart
                    if let Some(ahead) = self.peek() {
                        if ahead.is_alphanumeric() {
                            return Err(self.unexpected_token_error(TokenKind::NumericValue));
                        }
                    }
                }
            } else {
                // TODO: make sure the next char is not NameStart
                break;
            }
        }

        if !has_int_part {
            return Err(self.unexpected_token_error(TokenKind::NumericValue));
        }

        // fractional part or exponent part
        let mut has_fractional_part = false;
        if self.expect_opt('.') {
            // fractional part
            has_fractional_part = true;

            // digits
            while let Some(c) = self.peek() {
                if c.is_numeric() {
                    self.next();
                    has_fractional_part = true;
                } else {
                    break;
                }
            }
        }

        let mut has_exponent_part = false;
        if self.expect_opt('e') || self.expect_opt('E') {
            // exponent part
            has_exponent_part = true;

            // sign
            let _ = self.expect_opt('-') || self.expect_opt('+');

            // digits
            while let Some(c) = self.peek() {
                if c.is_numeric() {
                    self.next();
                } else {
                    break;
                }
            }
        }

        if has_fractional_part || has_exponent_part {
            return Ok(Token::new(TokenKind::FloatValue, self.loc(start, self.pos)));
        } else {
            return Ok(Token::new(TokenKind::IntValue, self.loc(start, self.pos)));
        }
    }

    // Name
    fn lex_name(&mut self) -> Result<Token, LexError> {
        let start = self.pos;
        // NameStart
        if let Some(c) = self.peek() {
            if c.is_ascii_alphabetic() {
                self.next();
            } else {
                return Err(self.unexpected_token_error(TokenKind::Name));
            }
        } else {
            return Err(LexError::new(LexErrorKind::UnexpectedEof, self.loc(self.pos, self.pos)));
        }

        // NameContinue
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() {
                self.next();
            } else {
                break;
            }
        }

        return Ok(Token::new(TokenKind::Name, self.loc(start, self.pos)));
    }

    // Punctuator
    fn lex_punctuator(&mut self) -> Result<Token, LexError> {
        let start = self.pos;

        if let Some(c) = self.peek() {
            match c {
                '!' | '$' | '&' | '(' | ')'	| ':'	| '='	| '@' |	'['	| ']'	| '{'	| '|' |	'}' => {
                    self.next();
                    return Ok(Token::new(TokenKind::Punctuator, self.loc(start, self.pos)));
                },
                '.' => { // ...
                    self.next();
                    self.expect('.');
                    self.expect('.');
                    return Ok(Token::new(TokenKind::Punctuator, self.loc(start, self.pos)));
                },
                _ => {
                    return Err(self.unexpected_token_error(TokenKind::Punctuator))
                }
            }
        }

        return Err(LexError::new(LexErrorKind::UnexpectedEof, self.loc(start, self.pos)));
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn lex_str() {
        let s = "";
        let mut lexer = Lexer::from_str(s);
        let tokens = lexer.lex_to_tokens().unwrap();
        assert_eq!(tokens.len(), 0);
    }

    #[test]
    fn lex_line_count() {
        let s = "foo\nbar\rbaz\r\nbax";
        let mut lexer = Lexer::from_iter(s.chars());
        let _ = lexer.lex_to_tokens().unwrap();
        assert_eq!(lexer.line, 4);
    }

    #[test]
    fn lex_int_value() {
        let int_values = ["0", "42", "-1234567890"];
        for s in int_values.iter() {
            let src = String::from(*s);
            let mut lexer = Lexer::from_iter(src.chars());
            let r = lexer.lex_to_tokens();
            if r.is_err() {
                panic!("{:?} -> {:?}", src, r.unwrap_err());
            }
            let tokens = r.unwrap();

            assert_eq!(tokens.len(), 1);

            let token = tokens.get(0).unwrap();
            assert_eq!(token.loc.start, 0);
            assert_eq!(token.loc.end, s.len());
            assert_eq!(token.value, TokenKind::IntValue);

            assert_eq!(token.get_str(&src), *s);
        }
    }

    #[test]
    fn lex_float_value() {
        let float_values = ["0.0", "42.195", "0.1e1", "0e0", "0E0", "0e+0", "0e-0"];
        for s in float_values.iter() {
            let src = String::from(*s);
            let mut lexer = Lexer::from_iter(src.chars());
            let r = lexer.lex_to_tokens();
            if r.is_err() {
                panic!("{:?} -> {:?}", src, r.unwrap_err());
            }
            let tokens = r.unwrap();

            assert_eq!(tokens.len(), 1);

            let token = tokens.get(0).unwrap();
            assert_eq!(token.loc.start, 0);
            assert_eq!(token.loc.end, s.len());
            assert_eq!(token.value, TokenKind::FloatValue);

            assert_eq!(token.get_str(&src), *s);
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
        let mut lexer = Lexer::from_iter(src.chars());
        let r = lexer.lex_to_tokens();
        if r.is_err() {
            panic!("{:?} -> {:?}", src, r.unwrap_err());
        }
        let tokens = r.unwrap();

        let token_kinds: Vec<TokenKind> = tokens.iter().map(|token| {
            return token.value;
        }).collect();

        assert_eq!(token_kinds, vec![
            TokenKind::Name, // schema
            TokenKind::Punctuator, // {

            TokenKind::Name, // query
            TokenKind::Punctuator, // :
            TokenKind::Name, // Query,
            TokenKind::Name, // mutation
            TokenKind::Punctuator, // :
            TokenKind::Name, // Mutation,
            TokenKind::Name, // subscription
            TokenKind::Punctuator, // :
            TokenKind::Name, // Subscription,

            TokenKind::Punctuator, // }
        ]);
    }
}
