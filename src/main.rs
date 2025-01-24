#![allow(warnings)] // for now

use std::process::ExitCode;

use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::gen::Compiletime;

#[macro_use] 
mod error_macro;
#[macro_use] mod lexer;
mod ast;
mod precedence;
mod parser;
mod errors;
mod gen;

// https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

// TODO: very dumb box allocations, but maybe its fine?

fn entry(input_path: String) -> crate::parser::Result<()> {
    let mut lexer = Lexer::new(&input_path).unwrap();
    let mut parser = Parser::from(lexer);

    let parse_module = parser.parse().map_err(|e| {
        eprintln!("{e}");
        e
    })?;
    println!("{:?}", parse_module.globals);
    let mut comptime = Compiletime::new(vec![parse_module]);
    let _ = comptime.emit().map_err(|e| {
        eprintln!("{e}");
        e
    })?;
    Ok(())
}

fn main() -> ExitCode {
    let mut args = std::env::args();
    let program = args.next().expect("program");

    let input_path = if let Some(input_path) = args.next() {
        input_path
    } else {
        eprintln!("Usage: {program} <file.eve>");
        eprintln!("error: no input is provided");
        return ExitCode::FAILURE;
    };

    match entry(input_path) {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
