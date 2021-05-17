use std::iter;

use crate::{Annotated, Lexer, Token};

// another root object that includes only executables
#[derive(Debug, Clone)]
pub struct ExecutableDocument {
    definitions: Vec<ExecutableDefinition>,
}

#[derive(Debug, Clone)]
pub struct TypeSystemExtensionDocument {
    definitions: Vec<TypeSystemDefinitionOrExtension>,
}

#[derive(Debug, Clone)]
pub enum ExecutableDefinition {
    Operation,
    Fragment,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperationType {
    Query,
    Mutation,
    Subscription,
}

#[derive(Debug, Clone)]
pub struct TypeSystemDefinitionOrExtension {}

pub enum ParseErrorKind {

}

pub type ParseError = Annotated<ParseErrorKind>;

#[derive(Debug)]
pub struct Parser<'a, Iter: iter::Iterator<Item = &'a Token>> {
    src: Vec<u8>,
    tokens: Vec<Token>,
    iter: iter::Peekable<Iter>,
}

pub fn parse_executable_document(src: Vec<u8>) -> Result<ExecutableDocument, ParseError> {
    let mut lexer = Lexer::from_iter(src.into_iter());
    let tokens = lexer.lex_to_tokens();

    panic!("TODO");
    // let parser = Parser {
    //     src,
    //     tokens,
    //     iter: tokens.iter().peekable(),
    // };

    // let mut definitions = Vec::<ExecutableDefinition>::new();

    // return Ok(ExecutableDocument { definitions });
}

impl<'a, Iter: iter::Iterator<Item = &'a Token>> Parser<'a, Iter> {

    fn parse_executable_definition(&mut self) -> Result<ExecutableDefinition, ParseError> {
        panic!("TODO");
    }

    fn parse_operation_definition(&mut self) -> Result<ExecutableDefinition, ParseError> {
        panic!("TODO");
    }
}
