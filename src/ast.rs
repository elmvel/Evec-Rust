use std::fmt;

use crate::lexer::{Token, Location};
use crate::parser::Result;
use crate::errors::SyntaxError;

#[derive(Debug)]
pub enum Global {
    DeclModule(Expr), // module main;
    Import(Expr), //import std::io;
    Decl(Token, Expr), // main :: <expr> \ main :: fn() { ... }
}

#[derive(Debug)]
pub enum Stmt {
    Dbg(Expr),
    Let(Token, Option<Type>, Expr),
    Scope(Vec<Stmt>),
    Ex(Expr), // C-style: a+b; foo();
}

#[derive(Debug)]
pub enum Expr {
    Ident(Token), // foo
    Path(Token, Box<Expr>), // std::io => (String std) (::) (*Expr(io))
    Number(Token),
    BinOp(char, Box<Expr>, Box<Expr>),
    UnOp(char, Box<Expr>),
    Func(Vec<Stmt>), // Eventually Func(Token, Vec<Param>, RetType, Vec<Stmt>)
}

impl Expr {
    pub fn loc(&self) -> Location {
        match self {
            Expr::Ident(t) => t.loc(),
            Expr::Path(t, _) => t.loc(),
            Expr::Number(t) => t.loc(),
            Expr::BinOp(_, lhs, _) => lhs.loc(),
            Expr::UnOp(_, expr) => expr.loc(),
            Expr::Func(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Type {
    U64,
    U32,
    U16,
    U8,
    S64,
    S32,
    S16,
    S8,
}

impl Type {
    pub fn qbe_type(&self) -> &str {
        match self {
            Type::U64 => "l",
            Type::U32 | Type::U16 | Type::U8 => "w",
            Type::S64 => "l",
            Type::S32 | Type::S16 | Type::S8 => "w",
        }
    }

    pub fn assert_number(&self, loc: Location) -> Result<()> {
        match self {
            Type::U64 | Type::U32 | Type::U16 | Type::U8 |
            Type::S64 | Type::S32 | Type::S16 | Type::S8 => Ok(()),
            _ => Err(error!(loc, "Expected type to be a number")),
        }
    }

    pub fn unsigned(&self) -> bool {
        match self {
            Type::U64 | Type::U32 | Type::U16 | Type::U8 => true,
            _ => false,
        }
    }
}
