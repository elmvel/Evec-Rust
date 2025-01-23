use std::iter;
use std::fmt;
use core::iter::from_fn;

use crate::errors::SyntaxError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Core
    Ident(Location, String),
    Int(Location, i64),
    Op(Location, char),
    Dots(Location),

    // Keywords
    Module(Location),
    Fn(Location),
    Dbg(Location),
    Let(Location),
    
    Eof,
}

impl Token {
    pub fn loc(&self) -> Location {
        match self {
            Token::Ident(loc, _) => loc.clone(),
            Token::Int(loc, _) => loc.clone(),
            Token::Op(loc, _) => loc.clone(),
            Token::Dots(loc) => loc.clone(),
            Token::Module(loc) => loc.clone(),
            Token::Fn(loc) => loc.clone(),
            Token::Dbg(loc) => loc.clone(),
            Token::Let(loc) => loc.clone(),
            Token::Eof => panic!("Didn't handle Eof in previous match case"),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Location {
    file_path: String,
    line: usize,
    column: usize,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{}:", self.file_path, self.line, self.column)
    }
}

// This is so expect_token function can work properly
impl PartialEq for Location {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}

impl Eq for Location {}

// Annoying but necessary
macro_rules! ldef {
    () => {
        Location::default()
    }
}

impl Location {
    pub fn new(file_path: String, line: usize, column: usize) -> Self {
        Self { file_path, line, column }
    }
}

pub struct Lexer {
    tokens: Vec<Token>,
}

impl Lexer {
    pub fn new(input: &str) -> Result<Self, SyntaxError> {
        let mut tokens: Vec<Token> = Vec::new();
        let mut iter = input.chars().peekable();
        let mut line = 1;
        let mut col = 1;
        
        // TODO: Rewrite this loop to do multi-token checks
        // do "iter.peek" or maybe just while true and check for
        // multi tokens first.
        while let Some(ch) = iter.next() {
            match ch {
                '\n' => {
                    line += 1;
                    col = 1;
                    continue;
                },
                ch if ch.is_whitespace() => {
                    col += 1;
                },
                '+' | '-' | '*' | '/' | '.' | '!' | '(' | ')'
                    | '[' | ']' | ';' | '{' | '}' | '=' => {
                        tokens.push(Token::Op(Location::new("temp".into(), line, col), ch));
                        col += 1;
                },
                ':' => {
                    // Todo: Ugly way to get a multi-token
                    let next = iter.peek();
                    if next.is_none() {
                        let loc = Location::new("temp".into(), line, col);
                        return Err(error!(loc, "Unknown character `{ch}`"));
                    }

                    let ch2 = next.unwrap();
                    if *ch2 != ':' {
                        let loc = Location::new("temp".into(), line, col);
                        return Err(error!(loc, "Unknown character `{ch}`"));
                    }

                    iter.next();
                    tokens.push(Token::Op(Location::new("temp".into(), line, col), 'D'));
                    col += 2;
                },
                'a'..='z' | 'A'..='Z' | '_' => {
                    let n: String = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_alphanumeric())))
                        .collect::<String>();

                    let loc = Location::new("temp".into(), line, col);
                    col += n.len();
                    Self::add_ident(n, &mut tokens, loc);
                },
                '1'..='9' => {
                    let s: String = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_digit())))
                        .collect::<String>();
                    let n: i64 = s.parse().unwrap();

                    tokens.push(Token::Int(Location::new("temp".into(), line, col), n));  
                    col += s.len();
                },
                _ => return Err(error!(Location::new("temp".into(), line, col), "Unknown character `{ch}`")),
            }
        }
        
        tokens.reverse();
        
        Ok(Self {
            tokens
        })
    }

    fn add_ident(id: String, tokens: &mut Vec<Token>, loc: Location) {
        let token = match &id[..] {
            "module" => Token::Module(loc),
            "fn" => Token::Fn(loc),
            "dbg" => Token::Dbg(loc),
            "let" => Token::Let(loc),
            _ => Token::Ident(loc, id),
        };
        tokens.push(token);  
    }

    // Note: not the most performant helpers, but easier to reason with

    pub fn next(&mut self) -> Token {
        self.tokens.pop().unwrap_or(Token::Eof)
    }

    pub fn peek(&mut self) -> Token {
        self.tokens.last().cloned().unwrap_or(Token::Eof)
    }

    pub fn eat(&mut self, token: Token) -> bool {
        let peek = self.peek();
        if std::mem::discriminant(&peek) == std::mem::discriminant(&token) {
            self.next();
            return true;
        }
        false
    }
}
