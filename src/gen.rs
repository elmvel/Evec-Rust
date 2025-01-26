use std::collections::HashMap;
use std::fmt::{self, Write};
use std::io::Write as IoWrite;
use std::fs::File;
use std::process::Command;

use crate::BuildOptions;
use crate::lexer::{Token, Location};
use crate::parser::ParseModule;
use crate::parser::Result;
use crate::ast::*;
use crate::errors::SyntaxError;

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
#[derive(Clone, Debug)]
struct StackValue {
    typ: Type,
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
}

impl StackFrame {
    pub fn symtab_store(&mut self, name: String, val: StackValue) {
        self.var_table.insert(name, val);
    }

    pub fn symtab_lookup(&mut self, name: &str, loc: Location) -> Result<StackValue> {
        self.var_table.get(name).cloned().ok_or(error!(loc, "No variable exists of name '{name}'"))
    }
}

#[derive(Default)]
pub struct FunctionContext {
    frames: Vec<StackFrame>,
    stack_counter: usize,
    logic_counter: usize,
    if_counter: usize,
    loop_counter: usize,
    loop_tracker: usize,
    stopper_counter: usize, // For when we need a label after a jmp because of qbe restrictions
}

impl FunctionContext {
    pub fn alloc(&mut self) -> usize {
        let i = self.stack_counter;
        self.stack_counter += 1;
        i
    }

    pub fn label_logic(&mut self) -> usize {
        let i = self.logic_counter;
        self.logic_counter += 1;
        i
    }

    pub fn label_cond(&mut self) -> usize {
        let i = self.if_counter;
        self.if_counter += 1;
        i
    }

    pub fn label_loop(&mut self) -> usize {
        let i = self.loop_counter;
        self.loop_counter += 1;
        i
    }

    pub fn stopper(&mut self) -> usize {
        let i = self.stopper_counter;
        self.stopper_counter += 1;
        i
    }

    pub fn current_loop(&self) -> usize {
        self.loop_counter - 1
    }

    pub fn loop_push(&mut self) {
        self.loop_tracker += 1;
    }

    pub fn loop_pop(&mut self) {
        self.loop_tracker -= 1;
    }

    pub fn loop_valid(&self) -> bool {
        self.loop_tracker > 0
    }

    pub fn lookup(&mut self, name: &str, loc: Location) -> Result<StackValue> {
        for frame in self.frames.iter_mut().rev() {
            let result = frame.symtab_lookup(name, loc.clone());
            if result.is_ok() {
                return result;
            }
        }
        Err(error!(loc, "No variable exits of name '{name}'"))
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
    ctx: FunctionContext,
    expected_type: Option<Type>,
}

impl Generator {
    pub fn new(decorated_mod: ParseModule) -> Self {
        Self {
            decorated_mod,
            generated_mod: GeneratedModule::default(),
            ctx: FunctionContext::default(),
            expected_type: None,
        }
    }

    fn write(&mut self, text: &str) {
        let _ = write!(self.generated_mod.output, "{text}");
    }

    fn writeln(&mut self, text: &str) {
        let _ = writeln!(self.generated_mod.output, "{text}");
    }

    fn current_frame(&mut self) -> Result<&mut StackFrame> {
        let last = self.ctx.frames.len() - 1;
        let Some(frame) = self.ctx.frames.get_mut(last) else {
            unreachable!("No stack frames!");
        };
        Ok(frame)
    }

    fn push_frame(&mut self) {
        self.ctx.frames.push(StackFrame::default());
    }

    fn pop_frame(&mut self) {
        let _ = self.ctx.frames.pop();
    }

    pub fn emit(&mut self) -> Result<()> {
        // TODO: set the name field of the gen module
        self.writeln("# QBE Start");
        genf!(self, "data $fmt_d = {{ b \"%d\\n\", b 0 }}");
        genf!(self, "data $fmt_ll = {{ b \"%lld\\n\", b 0 }}");
        genf!(self, "data $fmt_bool = {{ b \"bool: %d\\n\", b 0 }}");
        // for global in self.decorated_mod.globals.drain(..) {
        //     self.emit_global(global)?;
        // }
        self.decorated_mod.globals.reverse();
        while !self.decorated_mod.globals.is_empty() {
            let global = self.decorated_mod.globals.pop().unwrap();
            self.emit_global(global)?;
        }
        Ok(())
    }

    pub fn emit_global(&mut self, global: Global) -> Result<()> {
        match global {
            Global::Decl(name, expr) => {
                let Expr::Func(stmts) = expr else {
                    return Err(error!(name.loc(), "Only global functions are supported for now!"));
                };
                self.emit_function(name, stmts)
            },
            g => Err(error_orphan!("Unknown global {g:?}"))
        }
    }

    pub fn emit_function(&mut self, name: Token, stmts: Vec<Stmt>) -> Result<()> {
        let Token::Ident(_, text) = name else {
            unreachable!("must have an ident here")
        };

        genf!(self, "export function w ${text}() {{\n@start");

        self.ctx = FunctionContext::default();
        self.emit_stmts(stmts)?;
        
        genf!(self, "ret 0");
        genf!(self, "}}");
        Ok(())
    }

    pub fn emit_stmts(&mut self, stmts: Vec<Stmt>) -> Result<()> {
        // TODO: handle stack frames in here
        self.push_frame();
        for stmt in stmts {
            self.emit_stmt(stmt)?;
        }
        self.pop_frame();
        Ok(())
    }

    pub fn emit_stmt(&mut self, stmt: Stmt) -> Result<()> {
        match stmt {
            Stmt::Dbg(expr) => {
                let val = self.emit_expr(expr, None)?;

                match val.typ {
                    Type::U64 | Type::S64 => {
                        genf!(self, "%.void =w call $printf(l $fmt_ll, ..., l %.s{})", val);
                    },
                    Type::U32 | Type::U16 | Type::U8 |
                    Type::S32 | Type::S16 | Type::S8 => {
                        genf!(self, "%.void =w call $printf(l $fmt_d, ..., w %.s{})", val);
                    },
                    Type::Bool => {
                        genf!(self, "%.void =w call $printf(l $fmt_bool, ..., w %.s{})", val);
                    }
                }
                // TODO: match on stackvalue's type
                Ok(())
            },
            Stmt::Let(name, typ, expr) => {
                let Token::Ident(loc, text) = name else { unreachable!() };
                
                let val = self.emit_expr(expr, typ.clone())?;
                if let Some(expected_type) = typ {
                    if val.typ != expected_type {
                        return Err(error!(loc, "Expected type {expected_type:?}, but got {:?} instead", (val.typ)));
                    }
                }
                
                // NOTE: This allows shadowing
                let frame = self.current_frame()?;
                if frame.symtab_lookup(&text, loc.clone()).is_ok() {
                    return Err(error!(loc, "Redefinition of variable {text} is not allowed!"));
                }
                frame.symtab_store(text, val);
                Ok(())
            },
            Stmt::Scope(stmts) => {
                self.emit_stmts(stmts)?;
                Ok(())
            },
            Stmt::Ex(expr) => {
                let _ = self.emit_expr(expr, None)?;
                Ok(())
            },
            Stmt::If(expr, box_stmt, opt_else) => {
                let val = self.emit_expr(expr, None)?;
                let i = self.ctx.label_cond();
                genf!(self, "jnz %.s{}, @i{i}_body, @i{i}_else", (val.tag));
                genf!(self, "@i{i}_body");
                self.emit_stmt(*box_stmt)?;
                genf!(self, "jmp @i{i}_end");
                genf!(self, "@i{i}_else");

                if let Some(box_else_block) = opt_else {
                    self.emit_stmt(*box_else_block)?;
                }

                genf!(self, "@i{i}_end");
                
                Ok(())
            },
            Stmt::While(expr, box_stmt) => {
                self.ctx.loop_push(); // Allow break/continue
                
                let p = self.ctx.label_loop();
                genf!(self, "@p{p}_test");
                let val = self.emit_expr(expr, None)?;
                genf!(self, "jnz %.s{}, @p{p}_body, @p{p}_exit", (val.tag));

                genf!(self, "@p{p}_body");
                self.emit_stmt(*box_stmt)?;
                genf!(self, "jmp @p{p}_test");
                
                genf!(self, "@p{p}_exit");

                self.ctx.loop_pop(); // Disallow break/continue
                Ok(())
            },
            Stmt::Break(loc) => {
                // Get the current block we are in
                let p = self.ctx.current_loop();
                if !self.ctx.loop_valid() {
                    return Err(error!(loc, "No body to break out of!"));
                }
                genf!(self, "jmp @p{p}_exit");

                let s = self.ctx.stopper();
                genf!(self, "@p{p}_stopper{s}");
                Ok(())
            },
            Stmt::Continue(loc) => {
                // Get the current block we are in
                let p = self.ctx.current_loop();
                if !self.ctx.loop_valid() {
                    return Err(error!(loc, "No body to continue in!"));
                }
                genf!(self, "jmp @p{p}_test");

                let s = self.ctx.stopper();
                genf!(self, "@p{p}_stopper{s}");
                Ok(())
            },
            s => todo!("other statement types: {s:?}")
        }
    }

    pub fn emit_expr(&mut self, expr: Expr, expected_type: Option<Type>) -> Result<StackValue> {
        match expr {
            Expr::Ident(token) => {
                let Token::Ident(loc, text) = token else { unreachable!() };
                let val = self.ctx.lookup(&text, loc)?;
                Ok(val)
            },
            Expr::Path(token, box_expr) => {
                todo!()
            },
            Expr::Bool(token) => {
                let tag = self.ctx.alloc();

                let b = match token {
                    Token::True(_) => "1",
                    Token::False(_) => "0",
                    _ => unreachable!()
                };

                genf!(self, "%.s{tag} =w copy {b}");
                Ok(StackValue{ typ: Type::Bool, tag })
            },
            Expr::Number(token) => {
                // TODO: assuming its an i32 for now
                let Token::Int(_, i) = token else { unreachable!() };
                let tag = self.ctx.alloc();

                let typ = if let Some(typ) = expected_type {
                    if typ.assert_number(ldef!()).is_ok() {
                        typ
                    } else {
                        Type::S32
                    }
                } else {
                    Type::S32
                };
                let qtyp = typ.qbe_type();
                genf!(self, "%.s{tag} ={qtyp} copy {i}");
                Ok(StackValue{ typ, tag })
            },
            Expr::BinOp(op, box_lhs, box_rhs) => {
                match op {
                    Op::Add | Op::Sub | Op::Mul | Op::Div => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(*box_lhs, expected_type)?;
                        lval.typ.assert_number(lloc)?;
                        let rval = self.emit_expr(*box_rhs, Some(lval.typ.clone()))?;
                        rval.typ.assert_number(rloc)?;

                        let tag = self.ctx.alloc();

                        let qtyp = lval.typ.qbe_type();

                        let instr = match op {
                            Op::Add => "add",
                            Op::Sub => "sub",
                            Op::Mul => "mul",
                            Op::Div => {
                                if lval.typ.unsigned() {
                                    "udiv"
                                } else {
                                    "div"
                                }
                            },
                            _ => unreachable!(),
                        };
                        genf!(self, "%.s{tag} ={qtyp} {instr} %.s{}, %.s{}", (lval.tag), (rval.tag));
                        Ok(StackValue{ typ: lval.typ, tag })
                    },
                    Op::Eq => {
                        // Clone galore
                        let Expr::Ident(Token::Ident(loc, text)) = *box_lhs else { return Err(error!(box_lhs.loc(), "Expected variable")) };
                        let val = self.ctx.lookup(&text, loc.clone())?;

                        let new = self.emit_expr(*box_rhs, Some(val.typ.clone()))?;
                        if val.typ != new.typ {
                            return Err(error!(loc, "Assignment expected {:?}, got {:?} instead", (val.typ), (new.typ)))
                        }
                        // Redundant but necessary
                        let qtyp = new.typ.qbe_type();
                        genf!(self, "%.s{} ={qtyp} copy %.s{}", (val.tag), (new.tag));
                        Ok(new)
                    },
                    Op::AndAnd => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(*box_lhs, Some(Type::Bool))?;
                        let rval = self.emit_expr(*box_rhs, Some(Type::Bool))?;
                        lval.typ.assert_bool(lloc)?;
                        rval.typ.assert_bool(rloc)?;

                        let cond = self.ctx.alloc();
                        let tag = self.ctx.alloc();
                        let l = self.ctx.label_logic();
                        genf!(self, "jnz %.s{}, @l{l}_rhs, @l{l}_false", (lval.tag));
                        genf!(self, "@l{l}_rhs");
                        genf!(self, "jnz %.s{}, @l{l}_true, @l{l}_false", (rval.tag));

                        genf!(self, "@l{l}_true");
                        genf!(self, "%.s{tag} =w copy 1"); // Set false if we jump here
                        genf!(self, "jmp @l{l}_end");

                        genf!(self, "@l{l}_false");
                        genf!(self, "%.s{tag} =w copy 0"); // Set false if we jump here

                        genf!(self, "@l{l}_end");
                        Ok(StackValue{ tag, typ: Type::Bool })
                    },
                    Op::OrOr => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(*box_lhs, Some(Type::Bool))?;
                        let rval = self.emit_expr(*box_rhs, Some(Type::Bool))?;
                        lval.typ.assert_bool(lloc)?;
                        rval.typ.assert_bool(rloc)?;

                        let cond = self.ctx.alloc();
                        let tag = self.ctx.alloc();
                        let l = self.ctx.label_logic();
                        genf!(self, "jnz %.s{}, @l{l}_true, @l{l}_rhs", (lval.tag));
                        genf!(self, "@l{l}_rhs");
                        genf!(self, "jnz %.s{}, @l{l}_true, @l{l}_false", (rval.tag));

                        genf!(self, "@l{l}_true");
                        genf!(self, "%.s{tag} =w copy 1"); // Set false if we jump here
                        genf!(self, "jmp @l{l}_end");

                        genf!(self, "@l{l}_false");
                        genf!(self, "%.s{tag} =w copy 0"); // Set false if we jump here

                        genf!(self, "@l{l}_end");
                        Ok(StackValue{ tag, typ: Type::Bool })
                    },
                    Op::Gt | Op::Lt | Op::Ge | Op::Le | Op::EqEq | Op::NotEq => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(*box_lhs, expected_type)?;
                        lval.typ.assert_number(lloc)?;
                        let rval = self.emit_expr(*box_rhs, Some(lval.typ.clone()))?;
                        rval.typ.assert_number(rloc)?;

                        let tag = self.ctx.alloc();

                        let qtyp = lval.typ.qbe_type();
                        let instr = match op {
                            Op::Gt => "gt",
                            Op::Lt => "lt",
                            Op::Ge => "ge",
                            Op::Le => "le",
                            Op::EqEq => "eq",
                            Op::NotEq => "ne",
                            _ => todo!(),
                        };
                        if op.qbe_depends_sign() {
                            if lval.typ.unsigned() {
                                genf!(self, "%.s{tag} =w cu{instr}{qtyp} %.s{}, %.s{}", (lval.tag), (rval.tag));
                            } else {
                                genf!(self, "%.s{tag} =w cs{instr}{qtyp} %.s{}, %.s{}", (lval.tag), (rval.tag));
                            }
                        } else {
                            genf!(self, "%.s{tag} =w c{instr}{qtyp} %.s{}, %.s{}", (lval.tag), (rval.tag));
                        }
                        Ok(StackValue{ tag, typ: Type::Bool })
                    },
                    _ => todo!()
                }
            },
            Expr::UnOp(ch, box_expr) => {
                match ch {
                    Op::Sub => {
                        match *box_expr {
                            Expr::Number(token) => {
                                let Token::Int(_, i) = token else { unreachable!() };
                                let tag = self.ctx.alloc();

                                let typ = expected_type.unwrap_or(Type::S32);
                                let qtyp = typ.qbe_type();
                                genf!(self, "%.s{tag} ={qtyp} copy -{i}");
                                Ok(StackValue{ typ, tag })
                            },
                            Expr::Ident(token) => todo!(),
                            _ => unreachable!("Unsupported expr"),
                        }
                    },
                    c => todo!("op `{c:?}`"),
                }
            },
            Expr::Func(stmts) => {
                unreachable!("TBD: Should I put emit_function in here?")
            },
        }
    }

    // fn 
}

impl Compiletime {
    // TODO: accept buildoptions in the future
    pub fn new(decorated_mods: Vec<ParseModule>) -> Self {
        Self {
            decorated_mods,
            module_map: HashMap::new(),
        }
    }

    pub fn emit(&mut self, options: &BuildOptions) -> Result<()> {
        let mut objs = Vec::new();
        for decorated_mod in self.decorated_mods.drain(..) {
            let mut generator = Generator::new(decorated_mod);
            generator.emit()?;

            println!("QBE:\n{}", generator.generated_mod.output);
            // TODO: I need some way to preserve file names for qbe output files

            let name = "out";
            let mut file = File::create(&format!("{name}.ssa")).or(Err(error_orphan!("Could not create qbe output file")))?;
            let _ = write!(file, "{}", generator.generated_mod.output);

            // .ssa -> .s
            if !Command::new("qbe")
                .arg(&format!("{name}.ssa"))
                .arg("-o")
                .arg(&format!("{name}.s"))
                .status()
                .expect("ERROR: qbe not found")
                .success()
            {
                return Err(error_orphan!("Failure with getting assembly from QBE"));
            }

            // .s -> .o
            if !Command::new("cc")
                .arg("-c")
                .arg(&format!("{name}.s"))
                .status()
                .expect("ERROR: qbe not found")
                .success()
            {
                return Err(error_orphan!("Failure with getting object file from assembly"));
            }

            if !options.emit_qbe {
                let path = format!("{name}.ssa");
                if !Command::new("rm")
                    .arg(&path)
                    .status()
                    .expect("ERROR: rm failed")
                    .success()
                {
                    return Err(error_orphan!("Could not remove file {path}"));
                }
            }

            if !options.emit_assembly {
                let path = format!("{name}.s");
                if !Command::new("rm")
                    .arg(&path)
                    .status()
                    .expect("ERROR: rm failed")
                    .success()
                {
                    return Err(error_orphan!("Could not remove file {path}"));
                }
            }

            objs.push(format!("{name}.o"));
        }

        if !Command::new("cc")
            .args(objs.clone())
            .arg("-o")
            .arg("b.out")
            .status()
            .expect("ERROR: qbe not found")
            .success()
        {
            return Err(error_orphan!("Failure with linking final executable!"));
        }

        for path in objs {
            if !Command::new("rm")
                .arg(&path)
                .status()
                .expect("ERROR: rm failed")
                .success()
            {
                return Err(error_orphan!("Could not remove file {path}"));
            }
        }

        println!("Created executable b.out!");
        Ok(())
    }

    pub fn cmd(&mut self, cmd: Vec<String>) -> Result<()> {
        todo!()
    }
}
