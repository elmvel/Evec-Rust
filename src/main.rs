#![allow(warnings)] // for now

use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::gen::Compiletime;

mod lexer;
mod ast;
mod precedence;
mod parser;
mod errors;
mod gen;

// https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

// TODO: very dumb box allocations, but maybe its fine?

fn main() {
    let mut lexer = Lexer::new(
        r#"
module hello;

main :: fn() {
    let x = 420;
    dbg x;
}
        "#).unwrap();
    let mut parser = Parser::from(lexer);

    let parse_module = parser.parse().map_err(|e| {
        eprintln!("Error: {e:?}");
    }).unwrap();
    println!("{:?}", parse_module.globals);
    let mut comptime = Compiletime::new(vec![parse_module]);
    comptime.emit().unwrap();
}
