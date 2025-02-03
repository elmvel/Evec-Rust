use std::collections::{HashMap, HashSet};
use std::fmt::{self, Write};
use std::io::Write as IoWrite;
use std::fs::File;
use std::process::Command;

use crate::BuildOptions;
use crate::lexer::{Token, Location};
use crate::parser::ParseModule;
use crate::parser::Result;
use crate::decorator::DecoratedModule;
use crate::ast::*;
use crate::errors::SyntaxError;

// Valid for Generator methods
macro_rules! genf {
    ($gen:expr, $($l:tt),+) => {
        $gen.writeln(&format!($($l),+));
    }
}

macro_rules! gen {
    ($gen:expr, $($l:tt),+) => {
        $gen.write(&format!($($l),+));
    }
}

type Module = HashMap<String, FunctionDecl>;

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

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct FunctionDecl {
    name: String, //TODO: remove when not needed
    params: Vec<Param>,
    ret_type: Option<Type>,
}

impl FunctionDecl {
    pub fn new(params: Vec<Param>, ret_type: Option<Type>, name: String) -> Self {
        Self { params, ret_type, name }
    }
}

/////////// Runtime ////////////////

pub struct Compiletime {
    module_map: HashMap<String, Module>,
    main_defined: bool,
}

impl Compiletime {
    pub fn add_module(&mut self, name: String, module: Module) {
        if self.module_map.get(&name).is_some() {
            self.module_map.get_mut(&name).unwrap().extend(module.into_iter());
        } else {
            self.module_map.insert(name, module);
        }
    }
    
    pub fn get_module(&self, path: Expr) -> Option<&Module> {
        let s = path_to_string(path);
        self.module_map.get(&s)
    }
}

#[derive(Default)]
struct GeneratedModule {
    name: String,
    output: String,
}

struct Generator {
    pub decorated_mod: DecoratedModule,
    pub generated_mod: GeneratedModule,
    ctx: FunctionContext,
    expected_type: Option<Type>,
    imports: HashSet<String>,
    expected_return: Type,
}

pub fn path_to_string(expr: Expr) -> String {
    match expr {
        Expr::Ident(Token::Ident(_, text)) => text,
        Expr::Path(Token::Ident(_, text), box_expr) => {
            let mut t = text.clone();
            t.push_str("__");
            t.push_str(&path_to_string(*box_expr));
            t
        },
        _ => unreachable!(),
    }
}

fn get_module_name(s: String) -> String {
    let Some(idx) = s.rfind("__") else { unreachable!() };
    s[..idx].to_string()
}

fn get_func_name(s: String) -> String {
    let Some(i) = s.rfind("__") else { unreachable!() };
    let idx = i + 2;
    s[idx..].to_string()
}

macro_rules! gen_funcall_from_funcdef {
    ($slf:expr, $comptime:expr, $modname:expr, $def:expr, $text:expr, $args:expr, $loc:expr) => {
        if $def.is_some() {
            let def = $def.unwrap().clone();
            let parlen = def.params.len();
            
            let tag = $slf.ctx.alloc();
            let txt = $text;
            let ret_type = def.ret_type.clone().unwrap_or(TypeKind::Void.into());
            let qt = ret_type.qbe_type();

            let arglen = $args.len();
            if arglen != parlen {
                return Err(error!($loc, "Expected {parlen} arguments, got {arglen} instead."));
            }

            // Generate expressions
            let mut stack_values = Vec::new();
            for expr in $args.drain(..) {
                stack_values.push($slf.emit_expr($comptime, expr, None)?);
            }

            // Type check arguments
            for i in 0..stack_values.len() {
                if stack_values[i].typ != def.params.get(i).unwrap().1 {
                    return Err(error!(def.params[i].0.loc(), "Parameter expected type {}, but got {} instead.", (def.params[i].1), (stack_values[i].typ)));
                }
            }

            gen!($slf, "%.s{tag} ={qt} call ${}.{txt}(", $modname);

            // Emit arguments
            gen!($slf, "{}", (stack_values
                              .iter()
                              .map(|StackValue{tag, typ}| {
                                  let qtype = typ.qbe_type();
                                  format!("{qtype} %.s{tag}")
                              })
                              .collect::<Vec<String>>()
                              .join(", ")
            ));
            genf!($slf, ")");

            Ok(StackValue{tag, typ: ret_type})
            //Ok(StackValue{tag, typ: Type::Void})
        } else {
            let txt = $text;
            return Err(error!($loc, "Could not find function '{txt}'"));
        }
    }
}

impl Generator {
    pub fn new(decorated_mod: DecoratedModule) -> Self {
        let name = path_to_string(decorated_mod.parse_module.name.clone());
        let mut gen = Self {
            decorated_mod,
            generated_mod: GeneratedModule::default(),
            ctx: FunctionContext::default(),
            expected_type: None,
            imports: HashSet::new(),
            expected_return: TypeKind::Void.into(),
        };
        gen.generated_mod.name = name;
        gen
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

    fn import_lookup<'a>(&mut self, comptime: &'a mut Compiletime, modname: &str) -> Option<&'a Module> {
        // No-op except for ? operator
        let imported_name = self.imports.get(modname)?;
        comptime.module_map.get(modname)
    }

    // TODO: make more performant
    fn import_lookup_fuzzy<'a>(&mut self, comptime: &'a Compiletime, modname: &str) -> Option<(&'a Module, String)> {
        let mut matches = self.imports.iter()
            .filter(|imp| imp.ends_with(modname))
            .map(|imp| imp.clone())
            .collect::<Vec<String>>();
        matches.sort_by_key(|imp| imp.len());

        if matches.is_empty() {
            return None;
        }

        if matches.len() > 1 {
            warn!("Ambiguous path `{modname}`, choosing the first one...");
        }

        let name = &matches[0];
        Some((comptime.module_map.get(name)?, matches.remove(0)))
    }

    fn import(&mut self, comptime: &Compiletime, modname: &str) {
        
    }

    pub fn emit(&mut self, comptime: &mut Compiletime) -> Result<()> {
        // TODO: set the name field of the gen module
        self.writeln("# QBE Start");
        genf!(self, "data $fmt_d = {{ b \"%d\\n\", b 0 }}");
        genf!(self, "data $fmt_ll = {{ b \"%lld\\n\", b 0 }}");
        genf!(self, "data $fmt_bool = {{ b \"bool: %d\\n\", b 0 }}");
        genf!(self, "data $fmt_ptr = {{ b \"%p\\n\", b 0 }}");
        // for global in self.decorated_mod.globals.drain(..) {
        //     self.emit_global(global)?;
        // }
        self.decorated_mod.parse_module.globals.reverse();
        while !self.decorated_mod.parse_module.globals.is_empty() {
            let global = self.decorated_mod.parse_module.globals.pop().unwrap();
            self.emit_global(comptime, global)?;
        }
        Ok(())
    }

    pub fn emit_global(&mut self, comptime: &mut Compiletime, global: Global) -> Result<()> {
        match global {
            Global::Decl(name, expr) => {
                let Expr::Func(params, ret_type, stmts) = expr else {
                    return Err(error!(name.loc(), "Only global functions are supported for now!"));
                };
                let Token::Ident(_, text) = name.clone() else { unreachable!() };
                // TODO IMPORTANT: was this necessary?
                //self.func_map().insert(text.clone(), FunctionDecl::new(text));
                self.emit_function(comptime, params, ret_type, name, stmts)
            },
            Global::Import(expr) => {
                let loc = expr.loc();
                let modname = path_to_string(expr);
                if comptime.module_map.get(&modname).is_none() {
                    // TODO: prettier module name
                    return Err(error!(loc, "Module `{modname}` does not exist!"));
                }
                self.imports.insert(modname);
                Ok(())
            },
            g => Err(error_orphan!("Unknown global {g:?}"))
        }
    }

    pub fn emit_function(&mut self, comptime: &mut Compiletime, params: Vec<Param>, ret_type: Option<Type>, name: Token, stmts: Vec<Stmt>) -> Result<()> {
        let Token::Ident(loc, text) = name else {
            unreachable!("must have an ident here")
        };

        self.expected_return = match ret_type {
            Some(ref typ) => typ.clone(),
            None => TypeKind::Void.into(),
        };
        let qbe_return_type = match ret_type {
            Some(ref typ) => typ.qbe_type(),
            None => "",
        };

        // TODO: clearly define main semantics
        let mut setting_main = false;
        if &text == "main" {
            if comptime.main_defined {
                return Err(error!(loc, "Redefinition of function main!"));
            }
            gen!(self, "export function w $main(");
            let mut hack = 0;
            gen!(self, "{}", (params
                  .iter()
                  .map(|Param(tag, typ)| {
                      let f = format!("{} %.s{hack}", typ.qbe_type());
                      hack += 1;
                      f
                  })
                  .collect::<Vec<String>>()
                  .join(", "))
            );
            genf!(self, ") {{\n@start");
            comptime.main_defined = true;
            setting_main = true;
        } else {
            gen!(self, "export function {qbe_return_type} ${}.{text}(", (self.generated_mod.name));
            let mut hack = 0;
            gen!(self, "{}", (params
                  .iter()
                  .map(|Param(tag, typ)| {
                      let f = format!("{} %.s{hack}", typ.qbe_type());
                      hack += 1;
                      f
                  })
                  .collect::<Vec<String>>()
                  .join(", "))
            );
            genf!(self, ") {{\n@start");
        }

        self.ctx = FunctionContext::default();

        // Add all parameters to symbol table
        let mut prelude = StackFrame::default();
        for Param(token, typ) in params {
            let Token::Ident(_, text) = token else { unreachable!() };
            let tag = self.ctx.alloc();
            prelude.symtab_store(text, StackValue{tag, typ});
        }
        
        self.emit_stmts(comptime, stmts, Some(prelude))?;
        
        if ret_type.is_some() || setting_main {
            genf!(self, "ret 0");
        } else {
            genf!(self, "ret");
        }
        genf!(self, "}}");
        self.expected_return = TypeKind::Void.into();
        Ok(())
    }

    pub fn emit_stmts(&mut self, comptime: &mut Compiletime, stmts: Vec<Stmt>, prelude: Option<StackFrame>) -> Result<()> {
        // TODO: handle stack frames in here
        match prelude {
            Some(frame) => self.ctx.frames.push(frame),
            None => self.push_frame(),
        }
        for stmt in stmts {
            self.emit_stmt(comptime, stmt)?;
        }
        self.pop_frame();
        Ok(())
    }

    pub fn emit_stmt(&mut self, comptime: &mut Compiletime, stmt: Stmt) -> Result<()> {
        match stmt {
            Stmt::Dbg(expr) => {
                let val = self.emit_expr(comptime, expr, None)?;

                if val.typ.is_ptr() {
                    genf!(self, "%.void =w call $printf(l $fmt_ptr, ..., l %.s{})", val);
                } else {
                    match val.typ.kind {
                        TypeKind::U64 | TypeKind::S64 => {
                            genf!(self, "%.void =w call $printf(l $fmt_ll, ..., l %.s{})", val);
                        },
                        TypeKind::U32 | TypeKind::U16 | TypeKind::U8 |
                        TypeKind::S32 | TypeKind::S16 | TypeKind::S8 => {
                            genf!(self, "%.void =w call $printf(l $fmt_d, ..., w %.s{})", val);
                        },
                        TypeKind::Bool => {
                            genf!(self, "%.void =w call $printf(l $fmt_bool, ..., w %.s{})", val);
                        },
                        TypeKind::Void => unreachable!(),
                    }
                }
                Ok(())
            },
            Stmt::Let(name, typ, expr) => {
                let Token::Ident(loc, text) = name else { unreachable!() };

                // Do we need to allocate this on the stack?
                let mut allocate = false;
                if self.decorated_mod.addressed_vars.contains(&text) {
                    allocate = true;
                }
                
                let expr = self.emit_expr(comptime, expr, typ.clone())?;

                let val = if allocate {
                    let tag = self.ctx.alloc();
                    // TODO: alignment
                    genf!(self, "%.s{tag} =l alloc4 {}", (expr.typ.sizeof()));
                    genf!(self, "store{} %.s{}, %.s{tag}", (expr.typ.qbe_type()), (expr.tag));
                    StackValue{tag, typ: expr.typ}
                } else {
                    expr
                };
                
                if let Some(expected_type) = typ {
                    if val.typ != expected_type {
                        return Err(error!(loc, "Expected type {expected_type}, but got {} instead", (val.typ)));
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
                self.emit_stmts(comptime, stmts, None)?;
                Ok(())
            },
            Stmt::Ex(expr) => {
                let _ = self.emit_expr(comptime, expr, None)?;
                Ok(())
            },
            Stmt::If(expr, box_stmt, opt_else) => {
                let val = self.emit_expr(comptime, expr, None)?;
                let i = self.ctx.label_cond();
                genf!(self, "jnz %.s{}, @i{i}_body, @i{i}_else", (val.tag));
                genf!(self, "@i{i}_body");
                self.emit_stmt(comptime, *box_stmt)?;
                genf!(self, "jmp @i{i}_end");
                genf!(self, "@i{i}_else");

                if let Some(box_else_block) = opt_else {
                    self.emit_stmt(comptime, *box_else_block)?;
                }

                genf!(self, "@i{i}_end");
                
                Ok(())
            },
            Stmt::While(expr, box_stmt) => {
                self.ctx.loop_push(); // Allow break/continue
                
                let p = self.ctx.label_loop();
                genf!(self, "@p{p}_test");
                let val = self.emit_expr(comptime, expr, None)?;
                genf!(self, "jnz %.s{}, @p{p}_body, @p{p}_exit", (val.tag));

                genf!(self, "@p{p}_body");
                self.emit_stmt(comptime, *box_stmt)?;
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
            Stmt::Return(loc, opt) => {
                if let Some(expr) = opt {
                    let val = self.emit_expr(comptime, expr, None)?;
                    if self.expected_return != val.typ {
                        return Err(error!(loc, "Expected to return {}, but got {} instead", (self.expected_return), (val.typ)));
                    }
                    genf!(self, "ret %.s{}", (val.tag));
                } else {
                    if self.expected_return != TypeKind::Void.into() {
                        let void: Type = TypeKind::Void.into();
                        return Err(error!(loc, "Expected to return {}, but got {} instead", (self.expected_return), (void)));
                    }
                    genf!(self, "ret");
                }
                let s = self.ctx.stopper();
                genf!(self, "@return_stopper{s}");
                Ok(())
            },
        }
    }

    pub fn emit_expr(&mut self, comptime: &mut Compiletime, expr: Expr, expected_type: Option<Type>) -> Result<StackValue> {
        match expr {
            Expr::Ident(token) => {
                let Token::Ident(loc, text) = token else { unreachable!() };

                let mut allocated = false;
                if self.decorated_mod.addressed_vars.contains(&text) {
                    allocated = true;
                }

                let val = self.ctx.lookup(&text, loc)?;
                if allocated {
                    let tag = self.ctx.alloc();
                    let deref = val.typ.deref();
                    let qtype = deref.qbe_type();
                    // TODO: won't be compatible with large data
                    if val.typ.unsigned() {
                        genf!(self, "%.s{tag} ={qtype} loadu{qtype} %.s{}", (val.tag));
                    } else {
                        genf!(self, "%.s{tag} ={qtype} loads{qtype} %.s{}", (val.tag));
                    }
                    Ok(StackValue{tag, typ: val.typ})
                } else {
                    Ok(val)
                }
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
                Ok(StackValue{ typ: TypeKind::Bool.into(), tag })
            },
            Expr::Number(token) => {
                // TODO: assuming its an i32 for now
                let Token::Int(_, i) = token else { unreachable!() };
                let tag = self.ctx.alloc();

                let typ = if let Some(typ) = expected_type {
                    if typ.assert_number(ldef!()).is_ok() {
                        typ
                    } else {
                        TypeKind::S32.into()
                    }
                } else {
                    TypeKind::S32.into()
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
                        
                        let lval = self.emit_expr(comptime, *box_lhs, expected_type)?;
                        lval.typ.assert_number(lloc)?;
                        let rval = self.emit_expr(comptime, *box_rhs, Some(lval.typ.clone()))?;
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
                        match *box_lhs {
                            Expr::Ident(Token::Ident(loc, text)) => {
                                let val = self.ctx.lookup(&text, loc.clone())?;

                                let new = self.emit_expr(comptime, *box_rhs, Some(val.typ.clone()))?;
                                if val.typ != new.typ {
                                    // TODO: print types properly
                                    return Err(error!(loc, "Assignment expected {}, got {} instead", (val.typ), (new.typ)))
                                }
                                // Redundant but necessary
                                let qtyp = new.typ.qbe_type();
                                genf!(self, "%.s{} ={qtyp} copy %.s{}", (val.tag), (new.tag));
                                Ok(new)
                            },
                            Expr::UnOp(Op::Mul, box_expr) => {
                                let loc = box_expr.loc();
                                let ptr = self.emit_expr(comptime, *box_expr, None)?;
                                
                                if !ptr.typ.is_ptr() {
                                    return Err(error!(loc, "Cannot dereference a non-pointer type {}", (ptr.typ)));
                                }

                                let new = self.emit_expr(comptime, *box_rhs, Some(ptr.typ.deref()))?;
                                
                                let deref = ptr.typ.deref();
                                let qtype = deref.qbe_type();
                                // TODO: won't be compatible with large data

                                genf!(self, "store{qtype} %.s{}, %.s{}", (new.tag), (ptr.tag));
                                Ok(new)
                            },
                            e => return Err(error!(e.loc(), "Expected variable or deref assignment")),
                        }
                    },
                    Op::AndAnd => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(comptime, *box_lhs, Some(TypeKind::Bool.into()))?;
                        let rval = self.emit_expr(comptime, *box_rhs, Some(TypeKind::Bool.into()))?;
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
                        Ok(StackValue{ tag, typ: TypeKind::Bool.into() })
                    },
                    Op::OrOr => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(comptime, *box_lhs, Some(TypeKind::Bool.into()))?;
                        let rval = self.emit_expr(comptime, *box_rhs, Some(TypeKind::Bool.into()))?;
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
                        Ok(StackValue{ tag, typ: TypeKind::Bool.into() })
                    },
                    Op::Gt | Op::Lt | Op::Ge | Op::Le | Op::EqEq | Op::NotEq => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(comptime, *box_lhs, expected_type)?;
                        lval.typ.assert_number(lloc)?;
                        let rval = self.emit_expr(comptime, *box_rhs, Some(lval.typ.clone()))?;
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
                        Ok(StackValue{ tag, typ: TypeKind::Bool.into() })
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

                                let typ = expected_type.unwrap_or(TypeKind::S32.into());
                                let qtyp = typ.qbe_type();
                                genf!(self, "%.s{tag} ={qtyp} copy -{i}");
                                Ok(StackValue{ typ, tag })
                            },
                            Expr::Ident(token) => todo!(),
                            _ => unreachable!("Unsupported expr"),
                        }
                    },
                    Op::And => {
                        match *box_expr {
                            Expr::Ident(token) => {
                                // We should already allocate the variable as a pointer
                                let Token::Ident(loc, text) = token else { unreachable!() };
                                let val = self.ctx.lookup(&text, loc)?;
                                Ok(StackValue{tag: val.tag, typ: val.typ.ptr()})
                            },
                            _ => unreachable!("Unsupported expr"),
                        }
                    },
                    Op::Mul => {
                        let loc = box_expr.loc();
                        let ptr = self.emit_expr(comptime, *box_expr, None)?;

                        if !ptr.typ.is_ptr() {
                            return Err(error!(loc, "Cannot dereference a non-pointer type {}", (ptr.typ)));
                        }
                        
                        let tag = self.ctx.alloc();
                        
                        let deref = ptr.typ.deref();
                        let qtype = deref.qbe_type();
                        // TODO: won't be compatible with large data
                        if deref.unsigned() {
                            genf!(self, "%.s{tag} ={qtype} loadu{qtype} %.s{}", (ptr.tag));
                        } else {
                            genf!(self, "%.s{tag} ={qtype} loads{qtype} %.s{}", (ptr.tag));
                        }
                        Ok(StackValue{tag: tag, typ: deref})
                    },
                    c => todo!("op `{c:?}`"),
                }
            },
            Expr::Func(params, ret_type, stmts) => {
                unreachable!("TBD: Should I put emit_function in here?")
            },
            Expr::Call(box_expr, mut args) => {
                // todo!("Parse for expressions in function calls. Then, using $def in the gen_funcall_from_funcdef macro, check the validity of arguments passed and call with the correct arguments");
                match *box_expr {
                    Expr::Ident(token) => {
                        //todo!("work on module resolution and maybe return types");
                        let Token::Ident(loc, text) = token else { unreachable!() };
                        let local_func = self.decorated_mod.parse_module.function_map.get(&text);
                        gen_funcall_from_funcdef!(self, comptime, (self.generated_mod.name),local_func, &text, args, loc)
                    },
                    Expr::Path(token, box_expr) => {
                        // todo!("module resolution: make sure function maps get moved into Compiletime for module resolution lookup. This should be the library for which the 'import' statement can be moved into the Generator function map (I might need to make another structure which contains a global map and also a map of imported modules (key is the full path))")
                        let loc = token.loc();
                        let path = path_to_string(Expr::Path(token, box_expr));
                        let modname = get_module_name(path.clone());
                        if let Some(module) = self.import_lookup(comptime, &modname) {
                            let func_name = get_func_name(path);
                            let imported_func = module.get(&func_name);
                            gen_funcall_from_funcdef!(self, comptime, modname, imported_func, &func_name, args, loc)
                        } else {
                            if let Some((module, absolute_name)) = self.import_lookup_fuzzy(comptime, &modname) {
                                let func_name = get_func_name(path);
                                let imported_func = module.get(&func_name);
                                gen_funcall_from_funcdef!(self, comptime, absolute_name, imported_func, &func_name, args, loc)
                            } else {
                                // TODO: Nicer name printing here
                                return Err(error!(loc, "Unknown path `{modname}`"));
                            }
                        }
                    },
                    _ => return Err(error_orphan!("Got a function call without an identifier")),
                }
            },
            Expr::Null(token) => {
                if let Some(typ) = expected_type {
                    let tag = self.ctx.alloc();
                    
                    genf!(self, "%.s{tag} =l copy 0");
                    Ok(StackValue{tag, typ})
                } else {
                    Err(error!(token.loc(), "Cannot infer type of null pointer"))
                }
            },
        }
    }

}


impl Compiletime {
    // TODO: accept buildoptions in the future
    pub fn new() -> Self {
        Self {
            module_map: HashMap::new(),
            main_defined: false,
        }
    }

    pub fn emit(&mut self, mut decorated_mods: Vec<DecoratedModule>, options: &BuildOptions) -> Result<()> {
        let mut objs = Vec::new();
        for decorated_mod in &decorated_mods {
            let name = path_to_string(decorated_mod.parse_module.name.clone());
            self.add_module(name, decorated_mod.parse_module.function_map.clone());
        }
        for decorated_mod in decorated_mods.drain(..) {
            let name = decorated_mod.parse_module.file_stem.clone();

            let mut generator = Generator::new(decorated_mod);
            generator.emit(self)?;

            let mut file = File::create(&format!("{name}.ssa")).or(Err(error_orphan!("Could not create qbe output file")))?;
            let _ = write!(file, "{}", generator.generated_mod.output);

            // .ssa -> .s
            let qbe_path = options.qbe_path.clone().unwrap_or("qbe".to_string());
            if options.verbose_shell { println!("[CMD] {qbe_path} {name}.ssa -o {name}.s") }
            if !Command::new(&qbe_path)
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
            let assembler_path = options.assembler_path.clone().unwrap_or("cc".to_string());
            if options.verbose_shell { println!("[CMD] {assembler_path} -c {name}.s") }
            if !Command::new(&assembler_path)
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
                if options.verbose_shell { println!("[CMD] rm {path}") }
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
                if options.verbose_shell { println!("[CMD] rm {path}") }
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
            self.add_module(generator.generated_mod.name, generator.decorated_mod.parse_module.function_map);
        }

        let output_name = options.output_name.clone().unwrap_or("b.out".to_string());
        if !options.compile_only {
            let linker_path = options.linker_path.clone().unwrap_or("cc".to_string());
            let linker_args = options.linker_arguments.clone();
            if options.verbose_shell { println!("[CMD] {linker_path} {linker_args:?} {objs:?} -o {output_name}") }
            if !Command::new(linker_path)
                .args(linker_args)
                .args(objs.clone())
                .arg("-o")
                .arg(&output_name)
                .status()
                .expect("ERROR: qbe not found")
                .success()
            {
                return Err(error_orphan!("Failure with linking final executable!"));
            }

            for path in objs {
                if options.verbose_shell { println!("[CMD] rm {path}") }
                if !Command::new("rm")
                    .arg(&path)
                    .status()
                    .expect("ERROR: rm failed")
                    .success()
                {
                    return Err(error_orphan!("Could not remove file {path}"));
                }
            }
            println!("Created executable {output_name}!");
        } else {
            println!("Created object files!");
        }

        Ok(())
    }

    pub fn cmd(&mut self, cmd: Vec<String>) -> Result<()> {
        todo!()
    }
}
