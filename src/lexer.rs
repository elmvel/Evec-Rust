use std::iter;
use std::fmt;
use core::iter::from_fn;

use crate::errors::SyntaxError;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    // Core
    Ident(Location, String),
    Int(Location, i64),
    Op(Location, char),
    WideOp(Location, (char, char)),
    Dots(Location),

    // Keywords
    Module(Location),
    Import(Location),
    Fn(Location),
    Dbg(Location),
    Let(Location),
    If(Location),
    Then(Location),
    Else(Location),
    While(Location),
    Break(Location),
    Continue(Location),
    Return(Location),
    Null(Location),
    Defer(Location),
    Type(Location),

    // Types
    U64(Location),
    U32(Location),
    U16(Location),
    U8(Location),
    S64(Location),
    S32(Location),
    S16(Location),
    S8(Location),
    Bool(Location),

    // Special Values
    True(Location),
    False(Location),
    
    Eof,
}

impl Token {
    pub fn loc(&self) -> Location {
        match self {
            Token::Ident(loc, _) => loc.clone(),
            Token::Int(loc, _) => loc.clone(),
            Token::Op(loc, _) => loc.clone(),
            Token::WideOp(loc, _) => loc.clone(),
            Token::Dots(loc) => loc.clone(),
            Token::Module(loc) => loc.clone(),
            Token::Import(loc) => loc.clone(),
            Token::Fn(loc) => loc.clone(),
            Token::Dbg(loc) => loc.clone(),
            Token::Let(loc) => loc.clone(),
            Token::If(loc) => loc.clone(),
            Token::Then(loc) => loc.clone(),
            Token::Else(loc) => loc.clone(),
            Token::While(loc) => loc.clone(),
            Token::Break(loc) => loc.clone(),
            Token::Continue(loc) => loc.clone(),
            Token::Return(loc) => loc.clone(),
            Token::Null(loc) => loc.clone(),
            Token::Defer(loc) => loc.clone(),
            Token::Type(loc) => loc.clone(),
            Token::U64(loc) => loc.clone(),
            Token::U32(loc) => loc.clone(),
            Token::U16(loc) => loc.clone(),
            Token::U8(loc) => loc.clone(),
            Token::S64(loc) => loc.clone(),
            Token::S32(loc) => loc.clone(),
            Token::S16(loc) => loc.clone(),
            Token::S8(loc) => loc.clone(),
            Token::Bool(loc) => loc.clone(),
            Token::True(loc) => loc.clone(),
            Token::False(loc) => loc.clone(),
            Token::Eof => panic!("Didn't handle Eof in previous match case"),
        }
    }

    pub fn is_sink_ident(&self) -> bool {
        match self {
            Token::Ident(_, text) => {
                text == "_"
            },
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Default, Hash)]
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

const WIDE_CHARS: &[(char, char)] = &[
    (':', ':'),
    ('&', '&'),
    ('|', '|'),
    ('>', '='),
    ('<', '='),
    ('=', '='),
    ('!', '='),
    ('-', '>'),
    ('.', '.'),
];

impl Lexer {
    pub fn new(input_path: &str) -> Result<Self, SyntaxError> {
        let Ok(input) = std::fs::read_to_string(input_path) else {
            eprintln!("error: Could not find file '{input_path}'");
            std::process::exit(1);
        };
        
        let mut tokens: Vec<Token> = Vec::new();
        let mut iter = input.chars().peekable();
        let mut line = 1;
        let mut col = 1;
        
        // TODO: Rewrite this loop to do multi-token checks
        // do "iter.peek" or maybe just while true and check for
        // multi tokens first.
        'outer: while true {
            let Some(ch) = iter.next() else { break };
            if ch == '/' && iter.peek().filter(|c| **c == '/').is_some() {
                iter.next();
                col += 2;
                let _: String = iter::once(ch)
                    .chain(from_fn(|| iter.by_ref().next_if(|s| *s != '\n')))
                    .collect::<String>();
                continue;
            }
            for wchar in WIDE_CHARS {
                if ch == wchar.0 && iter.peek().filter(|c| **c == wchar.1).is_some() {
                    iter.next();
                    tokens.push(Token::WideOp(Location::new(input_path.into(), line, col), *wchar));
                    col += 2;
                    continue 'outer;
                }
            }
            
            match ch {
                '\n' => {
                    line += 1;
                    col = 1;
                    continue;
                },
                ch if ch.is_whitespace() => {
                    col += 1;
                },
                '+' | '-' | '*' | '/' | '.' | '!' | '(' | ')' |
                '[' | ']' | ';' | '{' | '}' | '=' | ':' | '>' |
                '<' | ',' | '&' => {
                        tokens.push(Token::Op(Location::new(input_path.into(), line, col), ch));
                        col += 1;
                },
                'a'..='z' | 'A'..='Z' | '_' => {
                    let n: String = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_alphanumeric())))
                        .collect::<String>();

                    let loc = Location::new(input_path.into(), line, col);
                    col += n.len();
                    Self::add_ident(n, &mut tokens, loc);
                },
                '1'..='9' => {
                    let s: String = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_digit())))
                        .collect::<String>();
                    let loc = Location::new(input_path.into(), line, col);
                    let n: i64 = s.parse().map_err(|_| error!(loc, "Could not parse signed 64 bit integer"))?;

                    tokens.push(Token::Int(Location::new(input_path.into(), line, col), n));  
                    col += s.len();
                },
                '0' => {
                    let s: String = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| *s == '0')))
                        .collect::<String>();
                    let loc = Location::new(input_path.into(), line, col);
                    let n: i64 = s.parse().map_err(|_| error!(loc, "Could not parse signed 64 bit integer"))?;
                    tokens.push(Token::Int(Location::new(input_path.into(), line, col), n));  
                    col += s.len();
                }
                _ => return Err(error!(Location::new(input_path.into(), line, col), "Unknown character `{ch}`")),
            }
        }

        // for token in &tokens {
        //     println!("{token:?}");
        // }
        
        tokens.reverse();
        
        Ok(Self {
            tokens
        })
    }

    fn add_ident(id: String, tokens: &mut Vec<Token>, loc: Location) {
        let token = match &id[..] {
            "module" => Token::Module(loc),
            "import" => Token::Import(loc),
            "fn" => Token::Fn(loc),
            "dbg" => Token::Dbg(loc),
            "let" => Token::Let(loc),
            "if" => Token::If(loc),
            "then" => Token::Then(loc),
            "else" => Token::Else(loc),
            "while" => Token::While(loc),
            "break" => Token::Break(loc),
            "continue" => Token::Continue(loc),
            "return" => Token::Return(loc),
            "null" => Token::Null(loc),
            "defer" => Token::Defer(loc),
            "type" => Token::Type(loc),

            "u64" => Token::U64(loc),
            "u32" => Token::U32(loc),
            "u16" => Token::U16(loc),
            "u8" => Token::U8(loc),
            "s64" => Token::S64(loc),
            "s32" => Token::S32(loc),
            "s16" => Token::S16(loc),
            "s8" => Token::S8(loc),
            "bool" => Token::Bool(loc),

            "true" => Token::True(loc),
            "false" => Token::False(loc),
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
        if peek == token {
            self.next();
            return true;
        }
        false
    }

    pub fn has_tokens(&mut self, rtokens: &[Token]) -> bool {
        self.tokens.ends_with(rtokens)
    }
}
