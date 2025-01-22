use std::iter;
use core::iter::from_fn;

use crate::errors::SyntaxError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Core
    Ident(String),
    Int(i64),
    Op(char),
    Dots,

    // Keywords
    Module,
    Fn,
    Dbg,
    Let,
    
    Eof,
}

pub struct Lexer {
    tokens: Vec<Token>,
}

impl Lexer {
    pub fn new(input: &str) -> Result<Self, SyntaxError> {
        let mut tokens: Vec<Token> = Vec::new();
        let mut iter = input.chars().peekable();
        
        while let Some(ch) = iter.next() {
            match ch {
                ch if ch.is_whitespace() => continue,
                '+' | '-' | '*' | '/' | '.' | '!' | '(' | ')'
                    | '[' | ']' | ';' | '{' | '}' | '=' => tokens.push(Token::Op(ch)),
                ':' => {
                    // Todo: Ugly way to get a multi-token
                    let next = iter.peek();
                    if next.is_none() {
                        return Err(format!("Unknown character `{ch}`").into());
                    }

                    let ch2 = next.unwrap();
                    if *ch2 != ':' {
                        return Err(format!("Unknown character `{ch}`").into());
                    }

                    iter.next();
                    tokens.push(Token::Op('D'));
                },
                'a'..='z' | 'A'..='Z' | '_' => {
                    let n: String = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_alphanumeric())))
                        .collect::<String>();

                    Self::add_ident(n, &mut tokens);
                },
                '1'..='9' => {
                    let n: i64 = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_digit())))
                        .collect::<String>()
                        .parse()
                        .unwrap();

                    tokens.push(Token::Int(n));  
                },
                _ => return Err(format!("Unknown character `{ch}`").into()),
            }
        }
        
        tokens.reverse();
        
        Ok(Self {
            tokens
        })
    }

    fn add_ident(id: String, tokens: &mut Vec<Token>) {
        let token = match &id[..] {
            "module" => Token::Module,
            "fn" => Token::Fn,
            "dbg" => Token::Dbg,
            "let" => Token::Let,
            _ => Token::Ident(id),
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
