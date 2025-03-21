#![allow(warnings)] // for now

use std::process::ExitCode;
use std::path::{Path, PathBuf};
use std::sync::RwLock;

use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::decorator::Decorator;
use crate::gen::Compiletime;
use crate::constants::STD_LIB_PATH;
use crate::target::*;

#[macro_use] 
mod error_macro;
#[macro_use] mod lexer;
mod ast;
mod const_eval;
mod precedence;
mod parser;
mod decorator;
mod errors;
mod gen;
mod constants;
mod target;
mod ir;
mod backend_qbe;
mod backend_c;

// https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

macro_rules! expect_argument {
    ($args:expr, $arg:expr, $dst:expr) => {
        if let Some(name) = $args.next() {
            $dst = Some(name);
        } else {
            let a = $arg;
            eprintln!("error: Expected argument with {a} flag");
            std::process::exit(1);
        }
    }
}

// TODO: very dumb box allocations, but maybe its fine?

#[derive(Default)]
struct BuildOptions {
    emit_qbe: bool,
    emit_assembly: bool,
    compile_only: bool,
    verbose_shell: bool,
    verbose: bool,
    debug_info: bool,
    output_name: Option<String>,
    assembler_path: Option<String>,
    linker_path: Option<String>,
    linker_arguments: Vec<String>,
    qbe_path: Option<String>,
    target: Target,
}

// TODO: handle multiple source files even though we technically take in a vector
fn entry(input_paths: Vec<String>, options: BuildOptions) -> crate::parser::Result<()> {
    let mut decorated_modules = Vec::new();
    
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
        let mut decorator = Decorator::new(parse_module);
        decorator.decorate();
        decorated_modules.push(decorator.decorated_mod);
    }

    let mut comptime = Compiletime::new();
    let _ = comptime.emit(decorated_modules, &options).map_err(|e| {
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
            "-h" | "--help" => print_help(&program),
            "-o" => {
                expect_argument!(args, arg, options.output_name);
            },
            "-c" => options.compile_only = true,
            "-vs" | "--verbose-shell" => options.verbose_shell = true,
            "-v" | "--verbose" => options.verbose = true,
            "-g" => {
                if !options.target.can_debug_info() {
                    eprintln!("error: Backend {} does not support debug information.", options.target.backend());
                    std::process::exit(1);
                }
                options.debug_info = true;
            },
            "--assembler" => {
                expect_argument!(args, arg, options.assembler_path);
            },
            "-Z" | "--linker-path" => {
                expect_argument!(args, arg, options.linker_path);
            },
            "-z" | "--linker-arg" => {
                let link_arg;
                expect_argument!(args, arg, link_arg);
                if let Some(la) = link_arg {
                    options.linker_arguments.push(la);
                }
            },
            "-Q" | "--qbe-path" => {
                expect_argument!(args, arg, options.qbe_path);
            },
            "--backend" => {
                let backend;
                expect_argument!(args, arg, backend);
                if let Some(b) = backend {
                    match b.as_str() {
                        "qbe" | "QBE" => options.target.set_backend(Backend::Qbe),
                        "llvm" | "LLVM" => options.target.set_backend(Backend::Llvm),
                        "c" | "C" => options.target.set_backend(Backend::C),
                        _ => {
                            eprintln!("error: Unknown backend '{b}'.");
                            eprintln!("Known backends are: qbe, llvm, c.");
                            std::process::exit(1);
                        },
                    }
                }
            },
            arg => input_paths.push(arg.to_string()),
        }
    }

    if input_paths.is_empty() {
        usage(&program);
        return ExitCode::FAILURE;
    }

    fetch_stdlib(&mut input_paths);

    // if options.target.backend() != Backend::Qbe {
    //     todo!("Handling other backends are not supported yet! I need to add infrastructure in ir.rs");
    // }
    if options.verbose {
        println!(
            "Targetting {}-{}, using the {} backend.",
            options.target.os(),
            options.target.arch(),
            options.target.backend(),
        );
    }
    match entry(input_paths, options) {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}

fn fetch_stdlib(input_paths: &mut Vec<String>) {
    let mut paths = std::fs::read_dir(*STD_LIB_PATH.read().unwrap()).map_err(|e| {
        eprintln!("ERROR: Could not find the standard library at path: {}", *STD_LIB_PATH.read().unwrap());
        std::process::exit(1);
    }).unwrap()
        .map(|de| de.unwrap().path())
        .collect::<Vec<PathBuf>>();
    while !paths.is_empty() {
        let path = paths.pop().unwrap();
        if path.is_dir() {
            paths.extend(std::fs::read_dir(path).unwrap().map(|de| de.unwrap().path()));
        } else {
            input_paths.push(format!("{}", path.display()));
        }
    }
}

fn usage(program: &str) {
    eprintln!("Usage: {program} [<option> ...] <file.eve> [<file2.eve> ...]");
    eprintln!("error: no input is provided");
}

fn print_help(program: &str) {
    usage(program);
        
    println!("\nOptions:\n");

    println!("  -ssa, --emit-qbe          Output QBE .ssa IR file.");
    println!("  -S, --emit-asm            Output assembly generated by QBE.");
    println!("  -h, --help                Print this help page.");
    println!("  -o                        Sets the executable name.");
    println!("  -c                        Only compile, do not link.");
    println!("  -vs, --verbose-shell      Show shell commands run by the compiler.");
    println!("  --assembler               Sets the assembler (default: cc).");
    println!("  -Z, --linker-path         Sets the linker (default: cc).");
    println!("  -z, --linker-arg          Forward an argument to the linker (default: cc).");
    println!("  -Q, --qbe-path            Sets the path to the QBE backend.");

    println!();
    std::process::exit(0);
}
