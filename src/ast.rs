use std::fmt;

use crate::lexer::Token;

#[derive(Debug)]
pub enum Global {
    DeclModule(Expr), // module main;
    Import(Expr), //import std::io;
    Decl(Token, Expr), // main :: <expr> \ main :: fn() { ... }
}

#[derive(Debug)]
pub enum Stmt {
    Dbg(Expr),
    Let(Token, Expr),
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
