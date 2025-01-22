use std::collections::HashMap;
use std::fmt::{self, Write};
use std::io::Write as IoWrite;
use std::fs::File;
use std::process::Command;

use crate::lexer::Token;
use crate::parser::ParseModule;
use crate::parser::Result;
use crate::ast::*;

// Valid for Generator methods
macro_rules! genf {
    ($gen:expr, $($l:tt),+) => {
        $gen.writeln(&format!($($l),+));
    }
}

struct Module {
    tmp: i32,
}

/////////// Bookkeeping ////////////////

// Might need to be an enum at some point for other "values"
#[derive(Clone)]
struct StackValue {
    tag: usize,
}

impl fmt::Display for StackValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.tag)
    }
}

type SymbolTable = HashMap<String, StackValue>;

#[derive(Default)]
struct StackFrame {
    var_table: SymbolTable,
    stack_counter: usize,
}

impl StackFrame {
    pub fn alloc(&mut self) -> usize {
        let i = self.stack_counter;
        self.stack_counter += 1;
        i
    }

    pub fn symtab_store(&mut self, name: String, val: StackValue) {
        self.var_table.insert(name, val);
    }

    pub fn symtab_lookup(&mut self, name: &str) -> Result<StackValue> {
        self.var_table.get(name).cloned().ok_or(format!("No variable exists of name '{name}'").into())
    }
}

/////////// Runtime ////////////////

pub struct Compiletime {
    decorated_mods: Vec<ParseModule>,
    module_map: HashMap<String, Module>,
}

#[derive(Default)]
struct GeneratedModule {
    name: String,
    output: String,
}

struct Generator {
    decorated_mod: ParseModule,
    pub generated_mod: GeneratedModule,
    frames: Vec<StackFrame>,
}

impl Generator {
    pub fn new(decorated_mod: ParseModule) -> Self {
        Self {
            decorated_mod,
            generated_mod: GeneratedModule::default(),
            frames: Vec::new(),
        }
    }

    fn write(&mut self, text: &str) {
        let _ = write!(self.generated_mod.output, "{text}");
    }

    fn writeln(&mut self, text: &str) {
        let _ = writeln!(self.generated_mod.output, "{text}");
    }

    fn current_frame(&mut self) -> Result<&mut StackFrame> {
        let last = self.frames.len() - 1;
        let Some(frame) = self.frames.get_mut(last) else {
            unreachable!("No stack frames!");
        };
        Ok(frame)
    }

    fn push_frame(&mut self) {
        self.frames.push(StackFrame::default());
    }

    fn pop_frame(&mut self) {
        let _ = self.frames.pop();
    }

    pub fn emit(&mut self) -> Result<()> {
        // TODO: set the name field of the gen module
        self.writeln("# QBE Start");
        genf!(self, "data $fmt_d = {{ b \"%d\\n\", b 0 }}");
        // for global in self.decorated_mod.globals.drain(..) {
        //     self.emit_global(global)?;
        // }
        self.decorated_mod.globals.reverse();
        while !self.decorated_mod.globals.is_empty() {
            let global = self.decorated_mod.globals.pop().unwrap();
            self.emit_global(global);
        }
        Ok(())
    }

    pub fn emit_global(&mut self, global: Global) -> Result<()> {
        match global {
            Global::Decl(name, expr) => {
                let Expr::Func(stmts) = expr else {
                    return Err("Only global functions are supported for now!".into());
                };
                self.emit_function(name, stmts)
            },
            g => Err(format!("Unknown global {g:?}").into())
        }
    }

    pub fn emit_function(&mut self, name: Token, stmts: Vec<Stmt>) -> Result<()> {
        let Token::Ident(text) = name else {
            unreachable!("must have an ident here")
        };

        genf!(self, "export function w ${text}() {{\n@start");

        self.push_frame();
        self.emit_stmts(stmts)?;
        self.pop_frame();
        
        genf!(self, "ret 0");
        genf!(self, "}}");
        Ok(())
    }

    pub fn emit_stmts(&mut self, stmts: Vec<Stmt>) -> Result<()> {
        for stmt in stmts {
            self.emit_stmt(stmt);
        }
        Ok(())
    }

    pub fn emit_stmt(&mut self, stmt: Stmt) -> Result<()> {
        match stmt {
            Stmt::Dbg(expr) => {
                let val = self.emit_expr(expr)?;
                genf!(self, "%.void =w call $printf(l $fmt_d, ..., w %.s{})", val);
                Ok(())
            },
            Stmt::Let(name, expr) => {
                let Token::Ident(text) = name else { unreachable!() };
                
                let val = self.emit_expr(expr)?;
                let frame = self.current_frame()?;
                frame.symtab_store(text, val);
                Ok(())
            },
            _ => todo!("other statement types")
        }
    }

    pub fn emit_expr(&mut self, expr: Expr) -> Result<StackValue> {
        match expr {
            Expr::Ident(token) => {
                let Token::Ident(text) = token else { unreachable!() };
                let frame = self.current_frame()?;
                let val = frame.symtab_lookup(&text)?;
                Ok(val)
            },
            Expr::Path(token, box_expr) => {
                todo!()
            },
            Expr::Number(token) => {
                // TODO: assuming its an i32 for now
                let Token::Int(i) = token else { unreachable!() };
                let mut frame = self.current_frame()?;
                let tag = frame.alloc();

                genf!(self, "%.s{tag} =w copy {i}");
                Ok(StackValue{ tag })
            },
            Expr::BinOp(ch, box_lhs, box_rhs) => {
                todo!()
            },
            Expr::UnOp(ch, box_expr) => {
                todo!()
            },
            Expr::Func(stmts) => {
                unreachable!("TBD: Should I put emit_function in here?")
            },
        }
    }
}

impl Compiletime {
    // TODO: accept buildoptions in the future
    pub fn new(decorated_mods: Vec<ParseModule>) -> Self {
        Self {
            decorated_mods,
            module_map: HashMap::new(),
        }
    }

    pub fn emit(&mut self) -> Result<()> {
        let mut objs = Vec::new();
        for decorated_mod in self.decorated_mods.drain(..) {
            let mut generator = Generator::new(decorated_mod);
            generator.emit()?;

            println!("QBE:\n{}", generator.generated_mod.output);
            // TODO: I need some way to preserve file names for qbe output files

            let name = "out";
            let mut file = File::create(&format!("{name}.ssa")).or(Err("Could not create qbe output file".into()))?;
            write!(file, "{}", generator.generated_mod.output);

            // .ssa -> .s
            if !Command::new("qbe")
                .arg(&format!("{name}.ssa"))
                .arg("-o")
                .arg(&format!("{name}.s"))
                .status()
                .expect("ERROR: qbe not found")
                .success()
            {
                return Err("Failure with getting assembly from QBE".into());
            }

            // .s -> .o
            if !Command::new("cc")
                .arg("-c")
                .arg(&format!("{name}.s"))
                .status()
                .expect("ERROR: qbe not found")
                .success()
            {
                return Err("Failure with getting assembly from QBE".into());
            }

            objs.push(format!("{name}.o"));
        }

        if !Command::new("cc")
            .args(objs)
            .arg("-o")
            .arg("b.out")
            .status()
            .expect("ERROR: qbe not found")
            .success()
        {
            return Err("Failure with linking final executable".into());
        }

        println!("Created executable b.out!");
        Ok(())
    }

    pub fn cmd(&mut self, cmd: Vec<String>) -> Result<()> {
        todo!()
    }
}
