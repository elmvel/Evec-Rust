#![allow(warnings)] // for now

use std::process::ExitCode;
use std::path::Path;

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

#[derive(Default)]
struct BuildOptions {
    emit_qbe: bool,
    emit_assembly: bool,
}

// TODO: handle multiple source files even though we technically take in a vector
fn entry(input_paths: Vec<String>, options: BuildOptions) -> crate::parser::Result<()> {
    let mut parse_modules = Vec::new();
    
    for input_path in input_paths {
        let mut lexer = Lexer::new(&input_path).map_err(|e| {
            eprintln!("{e}");
            e
        })?;
        let mut parser = Parser::from(lexer);

        let path = Path::new(&input_path).file_stem().unwrap();
        let parse_module = parser.parse(path.to_str().unwrap().to_string()).map_err(|e| {
            eprintln!("{e}");
            e
        })?;
        //println!("{:?}", parse_module.globals);
        parse_modules.push(parse_module);
    }

    let mut comptime = Compiletime::new(parse_modules);
    let _ = comptime.emit(&options).map_err(|e| {
        eprintln!("{e}");
        e
    })?;
    Ok(())
}

fn main() -> ExitCode {
    let mut args = std::env::args();
    let program = args.next().expect("program");
    let mut options = BuildOptions::default();

    let mut input_paths = Vec::new();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-ssa" | "--emit-qbe" => options.emit_qbe = true,
            "-S" | "--emit-asm" => options.emit_assembly = true,
            arg => input_paths.push(arg.to_string()),
        }
    }

    if input_paths.is_empty() {
        eprintln!("Usage: {program} <file.eve>");
        eprintln!("error: no input is provided");
        return ExitCode::FAILURE;
    }

    match entry(input_paths, options) {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
