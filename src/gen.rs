use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::fs::File;
use std::process::Command;
use std::io::Write as IoWrite;

use crate::BuildOptions;
use crate::lexer::{Token, Location};
use crate::parser::Result;
use crate::ast::*;
use crate::decorator::DecoratedModule;
use crate::errors::SyntaxError;
use crate::ir::*;
use crate::constants::MODULE_SEPARATOR;

type Module = HashMap<String, FunctionDecl>;
type SymbolTable = HashMap<String, TempValue>;

////////////////////// GENERATOR MACROS //////////////////////

macro_rules! genf {
    ($gen:expr, $($l:tt),+) => {
        let _ = writeln!($gen.generated_mod.output, "{}", &format!($($l),+));
    }
}

macro_rules! gen {
    ($gen:expr, $($l:tt),+) => {
        let _ = write!($gen.generated_mod.output, "{}", &format!($($l),+));
    }
}

macro_rules! temp [
    ($tag:expr, $typ:expr) => {
        TempValue{tag: $tag, typ: $typ}
    }
];

macro_rules! label [
    ($($l:tt),+) => {
        Value::Label(format!($($l),+))
    }
];

// A lot of clones, but it's tedious to care about each and every clone
// Owns dst_typ
macro_rules! load (
    ($gen:expr, $dst_typ:expr, $tv:expr) => {
        {
            let tag = $gen.ctx.alloc();
            let typ: Type = $dst_typ;
            $gen.block_add_assign(temp![tag, $dst_typ], Instruction::Load(Value::Temp($tv.clone()), typ.clone()))
        }
    }
);

// Doesn't own any
macro_rules! array_offset (
    ($gen:expr, $tv:expr, $typ:expr, $i:expr) => {
        {
            let btag = $gen.ctx.alloc();
            let ptr = $gen.ctx.alloc();
            let bytes = $i * $typ.sizeof();

            let btv = $gen.block_add_assign(temp![btag, TypeKind::U64.into()], Instruction::Copy(Value::Constant(format!("{bytes}"))));
            let ptv = $gen.block_add_assign(temp![ptr, $typ.ptr()], Instruction::Add(Value::Temp($tv.clone()), Value::Temp(btv)));
            ptv
        }
    }
);

////////////////////// GENERATOR //////////////////////

#[derive(Default)]
struct StackFrame {
    var_table: SymbolTable,
}

impl StackFrame {
    pub fn symtab_store(&mut self, name: String, val: TempValue) {
        self.var_table.insert(name, val);
    }

    pub fn symtab_lookup(&mut self, name: &str, loc: Location) -> Result<TempValue> {
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

    pub fn lookup(&mut self, name: &str, loc: Location) -> Result<TempValue> {
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
    pub params: Vec<Param>,
    ret_type: Option<Type>,
    pub extern_name: Option<String>,
}

impl FunctionDecl {
    pub fn new(params: Vec<Param>, ret_type: Option<Type>, name: String, extern_name: Option<String>) -> Self {
        Self { params, ret_type, name, extern_name }
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
    strings: Vec<String>,
    cstrings: Vec<String>,
    
    // IR
    toplevels: Vec<TopLevel>,
    working_blocks: Vec<Block>,
}

pub fn path_to_string(expr: Expr) -> String {
    match expr {
        Expr::Ident(Token::Ident(_, text)) => text,
        Expr::Path(Token::Ident(_, text), box_expr) => {
            let mut t = text.clone();
            t.push_str(MODULE_SEPARATOR);
            t.push_str(&path_to_string(*box_expr));
            t
        },
        _ => unreachable!(),
    }
}

fn get_module_name(s: String) -> String {
    let Some(idx) = s.rfind(MODULE_SEPARATOR) else { unreachable!() };
    s[..idx].to_string()
}

fn get_func_name(s: String) -> String {
    let Some(i) = s.rfind(MODULE_SEPARATOR) else { unreachable!() };
    let idx = i + 2;
    s[idx..].to_string()
}

// I don't know how to escape this macro, the logic is complex but must be repeated
macro_rules! gen_funcall_from_funcdef {
    ($slf:expr, $comptime:expr, $modname:expr, $def:expr, $text:expr, $args:expr, $loc:expr) => {
        if $def.is_some() {
            let def = $def.unwrap().clone();
            let parlen = def.params.len();
            
            let tag = $slf.ctx.alloc();
            let txt = $text;
            let ret_type = def.ret_type.clone().unwrap_or(TypeKind::Void.into());
            //let qt = ret_type.qbe_abi_type();

            let arglen = $args.len();
            if arglen != parlen {
                return Err(error!($loc, "Expected {parlen} arguments, got {arglen} instead."));
            }

            // Generate expressions
            let mut stack_values = Vec::new();
            for (i, expr) in $args.drain(..).enumerate() {
                stack_values.push($slf.emit_expr($comptime, expr, Some(def.params.get(i).unwrap().1.clone()))?);
            }

            // Type check arguments
            for i in 0..stack_values.len() {
                if def.params.get(i).unwrap().1.infer_elements {
                    return Err(error!(def.params[i].0.loc(), "Inferring array sizes is not supported in function parameters!"));
                }
                if !stack_values[i].typ.soft_equals(&def.params.get(i).unwrap().1) {
                    return Err(error!(def.params[i].0.loc(), "Parameter expected type {}, but got {} instead.", (def.params[i].1), (stack_values[i].typ)));
                }
            }

            if def.extern_name.is_some() {
                let extrn_name = def.extern_name.clone().unwrap();
                let tv = $slf.block_add_assign(
                    temp![tag, ret_type],
                    Instruction::Call(Value::Global(extrn_name), stack_values)
                );
                Ok(tv)
            } else {
                let tv = $slf.block_add_assign(
                    temp![tag, ret_type],
                    Instruction::Call(Value::Global(format!("{}.{txt}", $modname)), stack_values)
                );
                Ok(tv)
            }
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
            strings: Vec::new(),
            cstrings: Vec::new(),
            toplevels: Vec::new(),
            working_blocks: Vec::new(),
        };
        gen.generated_mod.name = name;
        gen
    }

    // Dump after all AST converted to IR
    fn dump(&mut self) {
        for toplevel in &self.toplevels {
            genf!(self, "{toplevel}");
        }
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
    
    fn start_block(&mut self, text: &str) {
        let name = Value::Label(text.to_string());
        self.working_blocks.push(Block{name, stmts: Vec::new(), dead: false});
    }

    fn current_block(&mut self) -> &mut Block {
        self.working_blocks.last_mut().unwrap()
    }
    
    fn drain_blocks(&mut self) -> Vec<Block> {
        self.working_blocks.drain(..).collect()
    }
    
    // Construct the temp value in tv, and then we give it back to you
    fn block_add_assign(&mut self, tv: TempValue, instr: Instruction) -> TempValue {
        self.current_block().stmts.push(Statement::Assignment(tv.clone(), instr));
        tv
    }

    fn block_add_discard(&mut self, instr: Instruction) {
        self.current_block().stmts.push(Statement::Discard(instr));
    }
    
    fn block_add_raw(&mut self, text: String) {
        self.current_block().stmts.push(Statement::Raw(text));
    }

    fn get_indexable_ptr(&mut self, val: &TempValue) -> usize {
        if val.typ.is_ptr() {
            return val.tag;
        }
        if !val.typ.is_struct() {
            unreachable!("Must be a structure if not a pointer");
        }
        match val.typ.struct_kind {
            StructKind::Array => val.tag,
            StructKind::Slice => {
                let tag = self.ctx.alloc();
                let tv = self.block_add_assign(temp![tag, TypeKind::U64.into()], Instruction::Load(Value::Temp(val.clone()), TypeKind::U64.into()));
                tv.tag
            },
            _ => unreachable!("unreachable unless if we support operator overloading"),
        }
    }

    pub fn emit_types(&mut self, comptime: &mut Compiletime) {
        // TODO: use toplevels instead
        genf!(self, "type :slice = {{ l, l }}");
    }

    fn emit_builtin_methods(&mut self, comptime: &mut Compiletime) -> Result<()> {
        // TODO: use toplevels instead
        genf!(
            self,
r#"
function l $.slice.ptr(l %slc) {{
@start
    %p =l loadl %slc
    ret %p
}}

function l $.slice.len(l %slc) {{
@start
    %off =l add %slc, 8
    %sz =l loadl %off
    ret %sz
}}
"#
        );

        let mut map = HashMap::new();
        let ptr_typ: Type = Into::<Type>::into(TypeKind::Void).ptr();
        map.insert("ptr".into(), FunctionDecl::new(vec![], Some(ptr_typ), "ptr".into(), None));
        map.insert("len".into(), FunctionDecl::new(vec![], Some(TypeKind::U64.into()), "len".into(), None));
        comptime.method_map.insert(Type::wrap(TypeKind::Void.into(), StructKind::Slice, None, false), map);
        Ok(())
    }

    fn type_to_builtin_check(typ: &Type) -> Type {
        if typ.is_struct() {
            match typ.struct_kind {
                StructKind::Slice => Type::wrap(TypeKind::Void.into(), StructKind::Slice, None, false),
                _ => typ.clone()
            }
        } else {
            return typ.clone();
        }
    }

    fn escape_string(mut text: &str) -> (String, usize) {
        let mut buf = String::new();
        let mut len = 0;
        while !text.is_empty() {
            if text.starts_with("\\n") {
                buf.push_str("\\x0A");
                text = &text[2..];
            } else if text.starts_with("\\r") {
                buf.push_str("\\x0D");
                text = &text[2..];
            } else if text.starts_with("\\t") {
                buf.push_str("\\x09");
                text = &text[2..];
            } else if text.starts_with("\\v") {
                buf.push_str("\\x0B");
                text = &text[2..];
            } else if text.starts_with("\\0") {
                buf.push_str("\\x00");
                text = &text[2..];
            } else if text.starts_with("\\x") && text.len() >= 4 {
                let mut it = text.chars().take(4);
                let (Some('\\'), Some('x'), Some(a), Some(b)) = (it.next(), it.next(), it.next(), it.next()) else {
                    unreachable!();
                };
                buf.push_str("\\x");
                buf.push(a);
                buf.push(b);
                text = &text[4..];
            } else {
                buf.push(text.chars().nth(0).expect("We have characters if its not empty"));
                text = &text[1..];
            }
            len += 1;
        }
        (buf, len)
    }

    fn emit_strings(&mut self) {
        let mut c = 0;
        self.strings.reverse();
        while !self.strings.is_empty() {
            let (string, len) = Generator::escape_string(&self.strings.pop().unwrap()); 
            genf!(self, "data $.str.data{c} = {{ b \"{string}\" }}");
            genf!(self, "data $.str{c} = {{ l $.str.data{c}, l {} }}", len);
            c += 1;
        }
    }

    fn emit_c_strings(&mut self) {
        let mut c = 0;
        self.cstrings.reverse();
        while !self.cstrings.is_empty() {
            let (cstring, _) = Generator::escape_string(&self.cstrings.pop().unwrap()); 
            genf!(self, "data $.cstr{c} = {{ b \"{cstring}\", b 0 }}");
            c += 1;
        }
    }
    
    pub fn emit(&mut self, comptime: &mut Compiletime) -> Result<()> {
        genf!(self, "# QBE Start");
        genf!(self, "data $fmt_d = {{ b \"%d\\n\", b 0 }}");
        genf!(self, "data $fmt_ll = {{ b \"%lld\\n\", b 0 }}");
        genf!(self, "data $fmt_bool = {{ b \"bool: %d\\n\", b 0 }}");
        genf!(self, "data $fmt_ptr = {{ b \"%p\\n\", b 0 }}");
        genf!(self, "data $fmt_arr_start = {{ b \"{{\\n\", b 0 }}");
        genf!(self, "data $fmt_arr_end = {{ b \"}}\\n\", b 0 }}");

        self.emit_types(comptime);
        self.emit_builtin_methods(comptime);

        self.decorated_mod.parse_module.globals.reverse();
        while !self.decorated_mod.parse_module.globals.is_empty() {
            let global = self.decorated_mod.parse_module.globals.pop().unwrap();
            // Collect the AST as IR
            let result = self.emit_global(comptime, global)?;
            if let Some(toplevel) = result {
                self.toplevels.push(toplevel);
            }
        }

        self.emit_strings();
        self.emit_c_strings();
        genf!(self, "");
        
        self.dump(); // Emit IR into the backend 
        Ok(())
    }

    pub fn emit_global(&mut self, comptime: &mut Compiletime, global: Global) -> Result<Option<TopLevel>> {
        match global {
            Global::Decl(name, expr) => {
                match expr {
                    Expr::Func(fn_, params, ret_type, stmts, returns, attrs) => {
                        if !returns && ret_type.is_some() {
                            return Err(error!(fn_.loc(), "This function does not always return, but should return {}", (ret_type.unwrap())));
                        }
                        let Token::Ident(_, text) = name.clone() else { unreachable!() };
                        Ok(Some(self.emit_function(comptime, params, ret_type, name, stmts, attrs)?))
                    },
                    Expr::FuncDecl(fn_, params, ret_type, _) => {
                        Ok(None)
                    },
                    _ => return Err(error!(name.loc(), "Only global functions are supported for now!")),
                }
            },
            Global::Import(expr) => {
                let loc = expr.loc();
                let modname = path_to_string(expr);
                if comptime.module_map.get(&modname).is_none() {
                    // TODO: prettier module name
                    return Err(error!(loc, "Module `{modname}` does not exist!"));
                }
                self.imports.insert(modname);
                Ok(None)
            },
            g => Err(error_orphan!("Unknown global {g:?}"))
        }
    }

    pub fn emit_function(&mut self, comptime: &mut Compiletime, params: Vec<Param>, ret_type: Option<Type>, name: Token, mut stmts: Vec<Stmt>, attrs: Vec<Attribute>) -> Result<TopLevel> {
        let Token::Ident(loc, text2) = name else { unreachable!() };
        
        // Resolve function attributes
        let mut extern_name = None;
        for attr in attrs {
            match attr {
                Attribute::Extern(expr) => {
                    let Expr::String(Token::String(_, text)) = expr else { unreachable!() };
                    extern_name = Some(text);
                },
                _ => return Err(error_orphan!("Unsupported function attribute `{attr:?}`")),
            }
        }

        // Function name
        let text = extern_name.unwrap_or(text2);

        self.expected_return = match ret_type {
            Some(ref typ) => typ.clone(),
            None => TypeKind::Void.into(),
        };
        
        let setting_main = &text == "main";
        if setting_main {
            if comptime.main_defined {
                return Err(error!(loc, "Redefinition of function main!"));
            }

            // Hack 2: let the ast know which returns are in main
            for stmt in &mut stmts {
                match stmt {
                    Stmt::Return(_, _, ref mut is_main, _) => *is_main = true,
                    _ => ()
                }
            }
        }
        
        // Reset function context
        self.ctx = FunctionContext::default();

        // Add all parameters to symbol table
        let mut prelude = StackFrame::default();
        for Param(token, typ) in &params {
            let Token::Ident(_, text) = token else { unreachable!() };
            let tag = self.ctx.alloc();
            prelude.symtab_store(text.clone(), temp![tag, typ.clone()]);
        }
        
        // TODO: IMPORTANT: Need to redo the return evaluation
        
        // NOTE: this does not follow the return semantic, as we will always have a working "block"
        self.start_block("start");
        if ret_type.is_none() { // TODO: double check hack
            stmts.push(Stmt::Return(ldef!(), None, setting_main, false));
        }
        self.emit_stmts(comptime, stmts, Some(prelude))?;
        if ret_type.is_some() { // TODO: double check hack
            // genf!(self, "ret 0"); //TODO I guess we didn't need this? return needs to be analyzed badly
        }

        // Reset expected_return (TODO: see if this absolutely needs to be here)
        self.expected_return = TypeKind::Void.into();
        if setting_main {
            Ok(TopLevel::Function(text, params, ret_type, self.drain_blocks(), setting_main))
        } else {
            Ok(TopLevel::Function(format!("{}.{text}", self.generated_mod.name), params, ret_type, self.drain_blocks(), setting_main))
        }
    }

    pub fn emit_stmts(&mut self, comptime: &mut Compiletime, stmts: Vec<Stmt>, prelude: Option<StackFrame>) -> Result<()> {
        match prelude {
            Some(frame) => self.ctx.frames.push(frame),
            None => self.push_frame(),
        }
        let mut deferred = Vec::new();
        let mut none: Option<&mut Vec<Stmt>> = None;
        for stmt in stmts {
            if let Stmt::Return(_, _, _, _) = stmt {
                let mut copied = deferred.clone();
                for stmt in copied.drain(..).rev() {
                    if self.current_block().dead { // Reset if we have returned out of it
                        let s = self.ctx.stopper();
                        self.start_block(&format!("BLK{s}"));
                    }
                    self.emit_stmt(comptime, stmt, &mut none)?;
                }
            }
            let mut opt: Option<&mut Vec<Stmt>>  = Some(&mut deferred);
            if self.current_block().dead { // Reset if we have returned out of it
                let s = self.ctx.stopper();
                self.start_block(&format!("BLK{s}"));
            }
            self.emit_stmt(comptime, stmt, &mut opt)?;
        }
        self.pop_frame();
        Ok(())
    }

    fn dbg_print_val(&mut self, comptime: &mut Compiletime, val: TempValue) -> Result<()> {
        // todo!("Let the IR support raw qbe IR");
        if val.typ.is_ptr() {
            self.block_add_raw(format!("%.void =w call $printf(l $fmt_ptr, ..., l %.{})", val))
        } else {
            match val.typ.kind {
                TypeKind::U64 | TypeKind::S64 => {
                    self.block_add_raw(format!("%.void =w call $printf(l $fmt_ll, ..., l %.{})", val));
                },
                TypeKind::U32 | TypeKind::U16 | TypeKind::U8 |
                TypeKind::S32 | TypeKind::S16 | TypeKind::S8 => {
                    //let tag = self.extend_to_long(val.tag, &val.typ);
                    // TODO: incorrect output
                    let tag = self.ctx.alloc();
                    let tv = self.block_add_assign(
                        temp![tag, TypeKind::U64.into()],
                        Instruction::Cast(Value::Temp(val.clone()), TypeKind::U64.into(), val.typ.clone())
                    );
                    self.block_add_raw(format!("%.void =w call $printf(l $fmt_d, ..., w %.{})", tv));
                },
                TypeKind::Bool => {
                    self.block_add_raw(format!("%.void =w call $printf(l $fmt_bool, ..., w %.{})", val));
                },
                TypeKind::Void => unreachable!(),
                TypeKind::Unresolved => unreachable!(),
                TypeKind::Structure => {
                    match val.typ.struct_kind {
                        StructKind::Array => {
                            let Some(ref inner) = val.typ.inner else { unreachable!() };

                            self.block_add_raw(format!("%.void =w call $printf(l $fmt_arr_start, ...)"));
                            for i in 0..val.typ.elements {
                                let ptr = array_offset!(self, val, inner, i);
                                let tag = self.ctx.alloc();
                                let tv = self.block_add_assign(
                                    temp![tag, *val.typ.inner.clone().unwrap()],
                                    Instruction::Load(Value::Temp(ptr.clone()), ptr.typ.clone())
                                );
                                self.dbg_print_val(comptime, tv);
                            }
                            self.block_add_raw(format!("%.void =w call $printf(l $fmt_arr_end, ...)"));
                        },
                        StructKind::Slice => {
                            let sz_offset = self.ctx.alloc();
                            let sz_ptr = self.ctx.alloc();
                            let sz_offset_tv = self.block_add_assign(
                                temp![sz_offset, TypeKind::U64.into()],
                                Instruction::Copy(Value::Constant("8".into()))
                            );
                            let sz_ptr_tv = self.block_add_assign(
                                temp![sz_ptr, TypeKind::U64.into()],
                                Instruction::Add(Value::Temp(val.clone()), Value::Temp(sz_offset_tv))
                            );
                            
                            let sz_tv = load!(self, TypeKind::U64.into(), sz_ptr_tv);
                            let ptr_tv = load!(self, TypeKind::U64.into(), val);

                            self.block_add_raw(format!("%.void =w call $printf(l $fmt_arr_start, ...)"));
                            self.block_add_raw(format!("%.void =w call $printf(l $fmt_ptr, ..., l %.{})", ptr_tv));
                            self.block_add_raw(format!("%.void =w call $printf(l $fmt_ll, ..., l %.{})", sz_tv));
                            self.block_add_raw(format!("%.void =w call $printf(l $fmt_arr_end, ...)"));
                        },
                        _ => todo!("generic printing of structures")
                    }
                },
            }
        }
        Ok(())
    }

    pub fn emit_stmt(&mut self, comptime: &mut Compiletime, stmt: Stmt, deferred: &mut Option<&mut Vec<Stmt>>) -> Result<()> {
        match stmt {
            Stmt::Dbg(expr) => {
                let tv = self.emit_expr(comptime, expr, None)?;
                self.dbg_print_val(comptime, tv);
                Ok(())
            },
            Stmt::Let(name, typ, expr) => {
                let Token::Ident(loc, text) = name else { unreachable!() };

                // Do we need to allocate this on the stack?
                let mut allocate = false;
                if self.decorated_mod.addressed_vars.contains(&text) {
                    allocate = true;
                }
                
                let raw = self.emit_expr(comptime, expr, typ.clone())?;

                let mut tv = if allocate {
                    let tag = self.ctx.alloc();
                    let tv_ptr = self.block_add_assign(
                        temp![tag, raw.typ.ptr()],
                        Instruction::Alloc(raw.typ.clone())
                    );
                    self.block_add_discard(Instruction::Store(Value::Temp(tv_ptr.clone()), Value::Temp(raw.clone()), raw.typ.clone()));
                    temp![tv_ptr.tag, raw.typ.clone()]
                } else {
                    raw
                };

                if let Some(mut expected_type) = typ {
                    // TODO: refactor type checking
                    if !tv.typ.soft_equals_array(&mut expected_type) {
                        return Err(error!(loc, "Expected type {expected_type}, but got {} instead", (tv.typ)));
                    }
                }

                let frame = self.current_frame()?;
                if frame.symtab_lookup(&text, loc.clone()).is_ok() {
                    return Err(error!(loc, "Redefinition of variable {text} is not allowed!"));
                }
                frame.symtab_store(text, tv);
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
                self.block_add_discard(Instruction::Jnz(Value::Temp(val), label!["i{i}_body"], label!["i{i}_else"]));
                self.start_block(&format!("i{i}_body"));
                self.emit_stmt(comptime, *box_stmt, deferred)?;
                self.block_add_discard(Instruction::Jmp(label!["i{i}_end"]));
                self.start_block(&format!("i{i}_else"));

                if let Some(box_else_block) = opt_else {
                    self.emit_stmt(comptime, *box_else_block, deferred)?;
                }

                self.start_block(&format!("i{i}_end"));
                
                Ok(())
            },
            Stmt::While(expr, box_stmt) => {
                self.ctx.loop_push(); // Allow break/continue
                
                let p = self.ctx.label_loop();
                self.start_block(&format!("p{p}_test"));
                let val = self.emit_expr(comptime, expr, None)?;
                self.block_add_discard(Instruction::Jnz(Value::Temp(val), label!["p{p}_body"], label!["p{p}_exit"]));

                self.start_block(&format!("p{p}_body"));
                self.emit_stmt(comptime, *box_stmt, deferred)?;
                self.block_add_discard(Instruction::Jmp(label!["p{p}_test"]));
                
                self.start_block(&format!("p{p}_exit"));

                self.ctx.loop_pop(); // Disallow break/continue
                Ok(())
            },
            Stmt::Break(loc) => {
                // Get the current block we are in
                let p = self.ctx.current_loop();
                if !self.ctx.loop_valid() {
                    return Err(error!(loc, "No body to break out of!"));
                }
                self.block_add_discard(Instruction::Jmp(label!["p{p}_exit"]));

                let s = self.ctx.stopper();
                self.start_block(&format!("p{p}_stopper{s}"));
                Ok(())
            },
            Stmt::Continue(loc) => {
                // Get the current block we are in
                let p = self.ctx.current_loop();
                if !self.ctx.loop_valid() {
                    return Err(error!(loc, "No body to continue in!"));
                }
                self.block_add_discard(Instruction::Jmp(label!["p{p}_test"]));

                let s = self.ctx.stopper();
                self.start_block(&format!("p{p}_stopper{s}"));
                Ok(())
            },
            Stmt::Return(loc, opt, setting_main, use_stopper) => {
                if let Some(expr) = opt {
                    let tv = self.emit_expr(comptime, expr, None)?;
                    if self.expected_return != tv.typ {
                        return Err(error!(loc, "Expected to return {}, but got {} instead", (self.expected_return), (tv.typ)));
                    }
                    self.block_add_discard(Instruction::Ret(Some(Value::Temp(tv))));
                } else {
                    if self.expected_return != TypeKind::Void.into() {
                        let void: Type = TypeKind::Void.into();
                        return Err(error!(loc, "Expected to return {}, but got {} instead", (self.expected_return), (void)));
                    }
                    // TODO: check HACK: stupid dumb dirty annoying hack ty qbe
                    if setting_main {
                        self.block_add_discard(Instruction::Ret(Some(Value::Constant("0".into()))));
                    } else {
                        self.block_add_discard(Instruction::Ret(None));
                    }
                }
                // TODO: use_stopper is deprecated
                // Make all blocks store a "dead" variable
                // if returned, they are dead
                // emit_stmts should check this to see if a block should be inserted
                //     let s = self.ctx.stopper();
                //     self.start_block(format!("return_stopper{s}"))
                self.current_block().dead = true;
                Ok(())
            },
            Stmt::Defer(loc, box_stmt) => {
                if let Some(stmts) = deferred {
                    stmts.push(*box_stmt);
                    Ok(())
                } else {
                    Err(error!(loc, "Cannot defer here (did you try to nest them?)"))
                }
            },
            _ => todo!("stmt {stmt:?}"),
        }
    }

    pub fn emit_expr(&mut self, comptime: &mut Compiletime, expr: Expr, expected_type: Option<Type>) -> Result<TempValue> {
        match expr {
            Expr::Ident(token) => {
                let Token::Ident(loc, text) = token else { unreachable!() };

                let mut allocated = false;
                if self.decorated_mod.addressed_vars.contains(&text) {
                    allocated = true;
                }

                let tv = self.ctx.lookup(&text, loc)?;
                if allocated {
                    let deref = tv.typ.deref(); // TODO: does this make sense? why would the type be a ptr
                    let tag = self.ctx.alloc();
                    let tv_retrieved = self.block_add_assign(
                        temp![tag, tv.typ.clone()],
                        Instruction::Load(Value::Temp(tv), deref)
                    );
                    Ok(tv_retrieved)
                } else {
                    Ok(tv)
                }
            },
            Expr::Path(token, box_expr) => {
                todo!()
            },
            Expr::Bool(token) => {
                let b = match token {
                    Token::True(_) => "1",
                    Token::False(_) => "0",
                    _ => unreachable!()
                };

                let tag = self.ctx.alloc();
                let tv = self.block_add_assign(
                    temp![tag, TypeKind::Bool.into()],
                    Instruction::Copy(Value::Constant(format!("{b}")))
                );
                Ok(tv)
            },
            Expr::Number(token) => {
                let Token::Int(_, i) = token else { unreachable!() };

                let typ = if let Some(typ) = expected_type {
                    if typ.assert_number(ldef!()).is_ok() {
                        typ
                    } else {
                        TypeKind::S32.into()
                    }
                } else {
                    TypeKind::S32.into()
                };

                let tag = self.ctx.alloc();
                let tv = self.block_add_assign(
                    temp![tag, typ],
                    Instruction::Copy(Value::Constant(format!("{i}")))
                );
                Ok(tv)
            },
            Expr::String(token) => {
                let Token::String(_, text) = token else { unreachable!() };
                let gtag = self.strings.len();
                let tag = self.ctx.alloc(); // for local instance
                let tv = self.block_add_assign(
                    temp![tag, TypeKind::U64.into()],
                    Instruction::Copy(Value::Global(format!(".str{gtag}")))
                );
                self.strings.push(text);
                Ok(temp![tv.tag, self.decorated_mod.parse_module.type_alias_map.get("str").unwrap().clone()])
            },
            Expr::CString(token) => {
                let Token::CString(_, text) = token else { unreachable!() };
                let gtag = self.cstrings.len();
                let tag = self.ctx.alloc(); // for local instance
                let tv = self.block_add_assign(
                    temp![tag, TypeKind::U64.into()],
                    Instruction::Copy(Value::Global(format!(".cstr{gtag}")))
                );
                self.cstrings.push(text);
                Ok(temp![tv.tag, self.decorated_mod.parse_module.type_alias_map.get("cstr").unwrap().clone()])
            },
            Expr::BinOp(_, op, box_lhs, box_rhs) => {
                match op {
                    Op::Add | Op::Sub | Op::Mul | Op::Div => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(comptime, *box_lhs, expected_type)?;
                        let rval = self.emit_expr(comptime, *box_rhs, Some(lval.typ.clone()))?;
                        lval.typ.assert_number(lloc)?;
                        rval.typ.assert_number(rloc)?;
                        
                        let tag = self.ctx.alloc();
                        let typ = lval.typ.clone();
                        let _ = match op {
                            Op::Add => self.block_add_assign(temp![tag, lval.typ.clone()], Instruction::Add(Value::Temp(lval), Value::Temp(rval))),
                            Op::Sub => self.block_add_assign(temp![tag, lval.typ.clone()], Instruction::Sub(Value::Temp(lval), Value::Temp(rval))),
                            Op::Mul => self.block_add_assign(temp![tag, lval.typ.clone()], Instruction::Mul(Value::Temp(lval), Value::Temp(rval))),
                            Op::Div => {
                                if lval.typ.unsigned() {
                                    self.block_add_assign(temp![tag, lval.typ.clone()], Instruction::DivU(Value::Temp(lval), Value::Temp(rval)))
                                } else {
                                    self.block_add_assign(temp![tag, lval.typ.clone()], Instruction::Div(Value::Temp(lval), Value::Temp(rval)))
                                }
                            },
                            _ => unreachable!(),
                        };
                        Ok(temp![tag, typ])
                    },
                    Op::Eq => {
                        match *box_lhs {
                            Expr::Ident(Token::Ident(loc, text)) => {
                                // EQ => Assigning to a variable
                                let val = self.ctx.lookup(&text, loc.clone())?;

                                let new = self.emit_expr(comptime, *box_rhs, Some(val.typ.clone()))?;
                                if val.typ != new.typ {
                                    return Err(error!(loc, "Assignment expected {}, got {} instead", (val.typ), (new.typ)))
                                }
                                let _ = self.block_add_assign(temp![val.tag, new.typ.clone()], Instruction::Copy(Value::Temp(new.clone())));
                                Ok(new)
                            },
                            Expr::UnOp(t, Op::Mul, box_expr, postfix) => {
                                // EQ => Assigning to a dereferenced variable
                                let loc = t.loc();
                                let ptr = self.emit_expr(comptime, *box_expr, None)?;
                                
                                if !ptr.typ.is_ptr() {
                                    return Err(error!(loc, "Cannot dereference a non-pointer type {}", (ptr.typ)));
                                }

                                let new = self.emit_expr(comptime, *box_rhs, Some(ptr.typ.deref()))?;
                                
                                let deref = ptr.typ.deref();
                                let qtype = deref.qbe_type();
                                // TODO: won't be compatible with large data

                                // genf!(self, "store{qtype} %.s{}, %.s{}", (new.tag), (ptr.tag));
                                self.block_add_discard(Instruction::Store(Value::Temp(ptr), Value::Temp(new.clone()), new.typ.clone()));
                                Ok(new)
                            },
                            Expr::BinOp(_, Op::Arr, box_lhs2, box_rhs2) => {
                                // EQ => Assigning to an indexed variable
                                let lloc = box_lhs2.loc();
                                let rloc = box_rhs2.loc();
                                
                                let lval = self.emit_expr(comptime, *box_lhs2, None)?;
                                let rval = self.emit_expr(comptime, *box_rhs2, None)?;
                                lval.typ.assert_indexable(lloc)?;
                                rval.typ.assert_number(rloc)?;
                                let base = self.get_indexable_ptr(&lval);

                                let Some(ref inner) = lval.typ.inner else { unreachable!() };
                                let rtag = self.ctx.alloc();
                                let rtv = self.block_add_assign(
                                    temp![rtag, TypeKind::U64.into()],
                                    Instruction::Cast(Value::Temp(rval.clone()), TypeKind::U64.into(), rval.typ.clone())
                                );
                                let bytes = self.ctx.alloc();
                                let bytes_tv = self.block_add_assign(
                                    temp![bytes, TypeKind::U64.into()],
                                    Instruction::Mul(Value::Temp(rtv), Value::Constant(format!("{}", inner.sizeof())))
                                );
                                let ptr = self.ctx.alloc();
                                let ptr_tv = self.block_add_assign(
                                    temp![ptr, TypeKind::U64.into()],
                                    Instruction::Add(Value::Temp(temp![base, TypeKind::U64.into()]), Value::Temp(bytes_tv))
                                );

                                let val = self.emit_expr(comptime, *box_rhs, Some(*inner.clone()))?;
                                self.block_add_discard(Instruction::Store(Value::Temp(ptr_tv), Value::Temp(val.clone()), val.typ.clone()));
                                Ok(val)
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
                        self.block_add_discard(Instruction::Jnz(Value::Temp(lval), label!["l{l}_rhs"], label!["l{l}_false"]));
                        self.start_block(&format!("l{l}_rhs"));
                        self.block_add_discard(Instruction::Jnz(Value::Temp(rval), label!["l{l}_true"], label!["l{l}_false"]));

                        self.start_block(&format!("l{l}_true"));
                        let _ = self.block_add_assign(temp![tag, TypeKind::Bool.into()], Instruction::Copy(Value::Constant("1".into())));
                        self.block_add_discard(Instruction::Jmp(label!["l{l}_end"]));

                        self.start_block(&format!("l{l}_false"));
                        let _ = self.block_add_assign(temp![tag, TypeKind::Bool.into()], Instruction::Copy(Value::Constant("0".into())));

                        self.start_block(&format!("l{l}_end"));
                        Ok(temp![tag, TypeKind::Bool.into()])
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
                        self.block_add_discard(Instruction::Jnz(Value::Temp(lval), label!["l{l}_true"], label!["l{l}_rhs"]));
                        self.start_block(&format!("l{l}_rhs"));
                        self.block_add_discard(Instruction::Jnz(Value::Temp(rval), label!["l{l}_true"], label!["l{l}_false"]));

                        self.start_block(&format!("l{l}_true"));
                        let _ = self.block_add_assign(temp![tag, TypeKind::Bool.into()], Instruction::Copy(Value::Constant("1".into())));
                        self.block_add_discard(Instruction::Jmp(label!["l{l}_end"]));

                        self.start_block(&format!("l{l}_false"));
                        let _ = self.block_add_assign(temp![tag, TypeKind::Bool.into()], Instruction::Copy(Value::Constant("0".into())));

                        self.start_block(&format!("l{l}_end"));
                        Ok(temp![tag, TypeKind::Bool.into()])
                    },
                    Op::Gt | Op::Lt | Op::Ge | Op::Le | Op::EqEq | Op::NotEq => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();

                        // TODO: type checking bug
                        let lval = self.emit_expr(comptime, *box_lhs, expected_type)?;
                        lval.typ.assert_comparable(lloc)?;
                        let rval = self.emit_expr(comptime, *box_rhs, Some(lval.typ.clone()))?;
                        rval.typ.assert_comparable(rloc)?;

                        let tag = self.ctx.alloc();
                        let tv = self.block_add_assign(
                            temp![tag, TypeKind::Bool.into()],
                            Instruction::Cmp(op, lval.typ.clone(), Value::Temp(lval), Value::Temp(rval))
                        );
                        Ok(tv)
                    },
                    Op::Arr => {
                        // Slice
                        if let Expr::Range(ref t, ref lower, ref upper) = *box_rhs {
                            // TODO: always assumes we are slicing an array, might not always be true
                            let lloc = box_lhs.loc();
                            let rloc = box_rhs.loc();
                            
                            let lval = self.emit_expr(comptime, *box_lhs, None)?;
                            lval.typ.assert_indexable(lloc.clone())?;
                            let base = temp![self.get_indexable_ptr(&lval), TypeKind::U64.into()];
                            let base_count = match lval.typ.struct_kind {
                                StructKind::Array => {
                                    let bc = self.ctx.alloc();
                                    let tv = self.block_add_assign(
                                        temp![bc, TypeKind::U64.into()],
                                        Instruction::Copy(Value::Constant(format!("{}", lval.typ.elements)))
                                    );
                                    tv
                                }
                                StructKind::Slice => {
                                    let bc_ptr = self.ctx.alloc();
                                    let tv_ptr = self.block_add_assign(
                                        temp![bc_ptr, TypeKind::U64.into()],
                                        Instruction::Add(Value::Temp(lval.clone()), Value::Constant("8".into()))
                                    );
                                    let bc = self.ctx.alloc();
                                    let tv = self.block_add_assign(
                                        temp![bc, TypeKind::U64.into()],
                                        Instruction::Load(Value::Temp(tv_ptr), TypeKind::U64.into())
                                    );
                                    tv
                                },
                                _ => return Err(error!(lloc, "Cannot index type {}", (lval.typ))),
                            };

                            // Make the slice
                            let Some(ref inner) = lval.typ.inner else { unreachable!() };
                            let slice_type = Type::wrap(*inner.clone(), StructKind::Slice, None, false);

                            let tag = self.ctx.alloc();
                            let tag_tv = self.block_add_assign(
                                temp![tag, TypeKind::U64.into()],
                                Instruction::Alloc(slice_type.clone())
                            );
                            let sz_ptr = self.ctx.alloc();
                            let sz_ptr_tv = self.block_add_assign(
                                temp![sz_ptr, TypeKind::U64.into()],
                                Instruction::Add(Value::Temp(tag_tv.clone()), Value::Constant("8".into()))
                            );

                            // Calculate the pointer and the length based on the range provided
                            let (final_ptr, final_count) = match (lower.clone(), upper.clone()) {
                                (Some(bl), Some(bu)) => {
                                    let lower_loc = bl.loc();
                                    let upper_loc = bu.loc();
                                    let lower = self.emit_expr(comptime, *bl, None)?;
                                    let upper = self.emit_expr(comptime, *bu, None)?;
                                    lower.typ.assert_number(lower_loc)?;
                                    upper.typ.assert_number(upper_loc)?;

                                    let ltag = self.ctx.alloc();
                                    let ltv = self.block_add_assign(
                                        temp![ltag, TypeKind::U64.into()],
                                        Instruction::Cast(Value::Temp(lower.clone()), TypeKind::U64.into(), lower.typ.clone())
                                    );
                                    let utag = self.ctx.alloc();
                                    let utv = self.block_add_assign(
                                        temp![utag, TypeKind::U64.into()],
                                        Instruction::Cast(Value::Temp(upper.clone()), TypeKind::U64.into(), upper.typ.clone())
                                    );

                                    let bytes = self.ctx.alloc();
                                    let bytes_tv = self.block_add_assign(
                                        temp![bytes, TypeKind::U64.into()],
                                        Instruction::Mul(Value::Temp(ltv.clone()), Value::Constant(format!("{}", inner.sizeof())))
                                    );
                                    let ptr = self.ctx.alloc();
                                    let ptr_tv = self.block_add_assign(
                                        temp![ptr, TypeKind::U64.into()],
                                        Instruction::Add(Value::Temp(base), Value::Temp(bytes_tv))
                                    );

                                    let count = self.ctx.alloc();
                                    let count_tv = self.block_add_assign(
                                        temp![count, TypeKind::U64.into()],
                                        Instruction::Sub(Value::Temp(utv), Value::Temp(ltv))
                                    );
                                    (ptr_tv, count_tv)
                                },
                                (Some(bl), None) => {
                                    let lower_loc = bl.loc();
                                    let lower = self.emit_expr(comptime, *bl, None)?;
                                    lower.typ.assert_number(lower_loc)?;

                                    let ltag = self.ctx.alloc();
                                    let ltv = self.block_add_assign(
                                        temp![ltag, TypeKind::U64.into()],
                                        Instruction::Cast(Value::Temp(lower.clone()), TypeKind::U64.into(), lower.typ.clone())
                                    );

                                    let bytes = self.ctx.alloc();
                                    let bytes_tv = self.block_add_assign(
                                        temp![bytes, TypeKind::U64.into()],
                                        Instruction::Mul(Value::Temp(ltv.clone()), Value::Constant(format!("{}", inner.sizeof())))
                                    );
                                    let ptr = self.ctx.alloc();
                                    let ptr_tv = self.block_add_assign(
                                        temp![ptr, TypeKind::U64.into()],
                                        Instruction::Add(Value::Temp(base), Value::Temp(bytes_tv))
                                    );

                                    let count = self.ctx.alloc();
                                    let count_tv = self.block_add_assign(
                                        temp![count, TypeKind::U64.into()],
                                        Instruction::Sub(Value::Temp(base_count), Value::Temp(ltv))
                                    );
                                    (ptr_tv, count_tv)
                                },
                                (None, Some(bu)) => {
                                    let upper_loc = bu.loc();
                                    let upper = self.emit_expr(comptime, *bu, None)?;
                                    upper.typ.assert_number(upper_loc)?;

                                    let utag = self.ctx.alloc();
                                    let utv = self.block_add_assign(
                                        temp![utag, TypeKind::U64.into()],
                                        Instruction::Cast(Value::Temp(upper.clone()), TypeKind::U64.into(), upper.typ.clone())
                                    );

                                    (base, utv)
                                },
                                (None, None) => {
                                    (base, base_count)
                                },
                            };

                            // Store the range (no offsetting the ptr or anything here)
                            self.block_add_discard(Instruction::Store(Value::Temp(tag_tv), Value::Temp(final_ptr), TypeKind::U64.into()));
                            self.block_add_discard(Instruction::Store(Value::Temp(sz_ptr_tv), Value::Temp(final_count), TypeKind::U64.into()));
                            return Ok(TempValue{tag, typ: Type::wrap(*inner.clone(), StructKind::Slice, None, false)});
                        }

                        // Array
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(comptime, *box_lhs, None)?;
                        let rval = self.emit_expr(comptime, *box_rhs, None)?;
                        lval.typ.assert_indexable(lloc)?;
                        rval.typ.assert_number(rloc)?;
                        let base = temp![self.get_indexable_ptr(&lval), TypeKind::U64.into()];
 
                        // We need the index to be a 64 bit value
                        // TODO: maybe factor this out too?
                        let rtag = self.ctx.alloc();
                        let rtv = self.block_add_assign(
                            temp![rtag, TypeKind::U64.into()],
                            Instruction::Cast(Value::Temp(rval.clone()), TypeKind::U64.into(), rval.typ.clone())
                        );

                        let bytes = self.ctx.alloc();
                        let ptr = self.ctx.alloc();

                        if lval.typ.is_ptr() {
                            let deref = lval.typ.deref();
                            let bytes_tv = self.block_add_assign(
                                temp![bytes, TypeKind::U64.into()],
                                Instruction::Mul(Value::Temp(rtv), Value::Constant(format!("{}", deref.sizeof())))
                            );
                            let ptr_tv = self.block_add_assign(
                                temp![ptr, TypeKind::U64.into()],
                                Instruction::Add(Value::Temp(base), Value::Temp(bytes_tv))
                            );

                            let tag = self.ctx.alloc();
                            let tag_tv = self.block_add_assign(
                                temp![tag, deref.clone()],
                                Instruction::Load(Value::Temp(ptr_tv), deref)
                            );
                            Ok(tag_tv)
                        } else {
                            let Some(ref inner) = lval.typ.inner else { unreachable!() };
                            let bytes_tv = self.block_add_assign(
                                temp![bytes, TypeKind::U64.into()],
                                Instruction::Mul(Value::Temp(rtv), Value::Constant(format!("{}", inner.sizeof())))
                            );
                            let ptr_tv = self.block_add_assign(
                                temp![ptr, TypeKind::U64.into()],
                                Instruction::Add(Value::Temp(base), Value::Temp(bytes_tv))
                            );

                            let tag = self.ctx.alloc();
                            let tag_tv = self.block_add_assign(
                                temp![tag, *inner.clone()],
                                Instruction::Load(Value::Temp(ptr_tv), *inner.clone())
                            );
                            Ok(tag_tv)
                        }
                    },
                    Op::Dot => {
                        let lloc = box_lhs.loc();
                        let rloc = box_rhs.loc();
                        
                        let lval = self.emit_expr(comptime, *box_lhs, None)?;
                        let Expr::Call(box_expr, _) = *box_rhs else {
                            return Err(error!(rloc, "Rhs of . operator does not look like a method call"));
                        };
                        let Expr::Ident(Token::Ident(loc, text)) = *box_expr else {
                            return Err(error!(rloc, "Rhs of . operator does not look like a method call"));
                        };
                        if let Some(mtd_map) = comptime.method_map.get(&Generator::type_to_builtin_check(&lval.typ)) {
                            if let Some(decl) = mtd_map.get(&text) {
                                if lval.typ.is_struct() {
                                    match lval.typ.struct_kind {
                                        StructKind::Slice => {
                                            // Built in
                                            let tag = self.ctx.alloc();
                                            let tv = self.block_add_assign(
                                                temp![tag, decl.ret_type.clone().unwrap_or(TypeKind::Void.into())],
                                                // Note: for methods we pass the object by a pointer
                                                Instruction::Call(Value::Global(format!(".slice.{text}")), vec![temp![lval.tag, lval.typ.ptr()]])
                                            );
                                            Ok(tv)
                                            //genf!(self, "%.s{tag} =l call $.slice.{}(l %.s{})", text, lval);
                                            //Ok(StackValue{tag, typ: decl.ret_type.clone().unwrap_or(TypeKind::Void.into())})
                                        },
                                        _ => todo!()
                                    }
                                } else {
                                    todo!()
                                }
                            } else {
                                return Err(error!(loc, "No method `{}` found on type {}", text, (lval.typ)));
                            }
                        } else {
                            Err(error!(lloc, "No methods exist for type {}", (lval.typ)))
                        }
                    },
                    op => todo!("all remaining binary operators: {op:?}"),
                }
            },
            Expr::UnOp(_, ch, box_expr, postfix) => {
                match ch {
                    Op::Sub => {
                        match *box_expr {
                            Expr::Number(token) => {
                                let Token::Int(_, i) = token else { unreachable!() };

                                let tag = self.ctx.alloc();
                                let typ = expected_type.unwrap_or(TypeKind::S32.into());
                                let tv = self.block_add_assign(
                                    temp![tag, typ],
                                    Instruction::Copy(Value::Constant(format!("-{i}")))
                                );
                                Ok(tv)
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
                                Ok(temp![val.tag, val.typ.ptr()])
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
                        
                        let deref = ptr.typ.deref();
                        let tv = load!(self, deref.clone(), ptr);
                        Ok(tv)
                    },
                    Op::Implicit => {
                        let loc = box_expr.loc();
                        let val = self.emit_expr(comptime, *box_expr, None)?;
                        if let Some(typ) = expected_type {
                            if !typ.assert_number(loc.clone()).is_ok() && !val.typ.assert_number(loc.clone()).is_ok() {
                                return Err(error!(loc, "Only implicit conversions between integers are supported!"));
                            }
                            let tag = self.ctx.alloc();
                            let tv = self.block_add_assign(
                                temp![tag, typ.clone()],
                                Instruction::Cast(Value::Temp(val.clone()), typ, val.typ.clone())
                            );
                            Ok(tv)
                        } else {
                            return Err(error!(loc, "Need a type to infer for implicit conversion!"))
                        }
                    },
                    c => todo!("op `{c:?}`"),
                }
            },
            Expr::Func(_, params, ret_type, stmts, _, _) => {
                unreachable!("TBD: Should I put emit_function in here?")
            },
            Expr::FuncDecl(_, _, _, _) => {
                unreachable!("can't declare functions within functions")
            },
            Expr::Call(box_expr, mut args) => {
                match *box_expr {
                    Expr::Ident(token) => {
                        let Token::Ident(loc, text) = token else { unreachable!() };
                        let local_func = self.decorated_mod.parse_module.function_map.get(&text);
                        gen_funcall_from_funcdef!(self, comptime, (self.generated_mod.name),local_func, &text, args, loc)
                    },
                    Expr::Path(token, box_expr) => {
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
                    let tv = self.block_add_assign(
                        temp![tag, typ],
                        Instruction::Copy(Value::Constant("0".into()))
                    );
                    Ok(tv)
                } else {
                    Err(error!(token.loc(), "Cannot infer type of null pointer"))
                }
            },
            Expr::InitList(token, mut exprs) => {
                if let Some(mut typ) = expected_type {
                    if typ.kind != TypeKind::Structure {
                        return Err(error!(token.loc(), "Cannot initialize {typ} with initializer list"));
                    }
                    match typ.struct_kind {
                        StructKind::Array => {
                            if typ.infer_elements {
                                typ.elements = exprs.len();
                                typ.infer_elements = false;
                            }
                            if typ.elements != exprs.len() {
                                return Err(error!(token.loc(), "Type expected {} arguments for initializer list", (typ.elements)));
                            }

                            // Make the array
                            let Some(ref inner) = typ.inner else { unreachable!() };
                            let sz = typ.elements * inner.sizeof();
                            if sz == 0 {
                                return Err(error!(token.loc(), "Cannot make an array of size '0'!"));
                            }

                            let tag = self.ctx.alloc();
                            let tv = self.block_add_assign(
                                temp![tag, typ.clone()],
                                Instruction::Alloc(typ.clone())
                            );
                            
                            // Get the expressions
                            let mut vals = Vec::new();
                            for expr in exprs {
                                let val = self.emit_expr(comptime, expr, Some(*inner.clone()))?;
                                vals.push(val);
                            }

                            // Type check the expressions and copy
                            for (i, val) in vals.iter().enumerate() {
                                if val.typ != **inner {
                                    return Err(error!(token.loc(), "Expected {} for array member, got {} instead", (*inner), (val.typ)));
                                }
                                let ptr = array_offset!(self, tv, inner, i);
                                self.block_add_discard(Instruction::Store(Value::Temp(ptr), Value::Temp(val.clone()), val.typ.clone()))
                            }
                            Ok(tv)
                        },
                        StructKind::Slice => {
                            if exprs.len() != 2 {
                                return Err(error!(token.loc(), "Need exactly 2 arguments to initialize slice: {{ptr, len}}"));
                            }
                            let Some(ref inner) = typ.inner else { unreachable!() };
                            let ptr_loc = exprs[0].loc();
                            let len_loc = exprs[1].loc();
                            let expr_1 = exprs.pop().unwrap();
                            let expr_0 = exprs.pop().unwrap();
                            let ptr = self.emit_expr(comptime, expr_0, Some(*inner.clone()))?;
                            let len = self.emit_expr(comptime, expr_1, None)?;
                            if !ptr.typ.is_ptr() {
                                return Err(error!(ptr_loc, "Expected pointer for first field of slice"));
                            }
                            let mut deref = ptr.typ.deref();
                            if !deref.soft_equals(inner) {
                                return Err(error!(ptr_loc, "Expected type of {typ}, got type of {} instead", (ptr.typ)));
                            }
                            if len.typ.assert_number(len_loc).is_err() {
                                return Err(error!(ptr_loc, "Expected number for second field of slice"));
                            }
                            let ltag = self.ctx.alloc();
                            let long = self.block_add_assign(
                                temp![ltag, TypeKind::U64.into()],
                                Instruction::Cast(Value::Temp(len.clone()), TypeKind::U64.into(), len.typ.clone())
                            );

                            let tag = self.ctx.alloc();
                            let offset = self.ctx.alloc();
                            let slice_type = Type::wrap(*inner.clone(), StructKind::Slice, None, false);

                            let tagtv = self.block_add_assign(
                                temp![tag, Into::<Type>::into(TypeKind::Void).ptr()],
                                Instruction::Alloc(slice_type.clone())
                            );
                            self.block_add_discard(Instruction::Store(Value::Temp(tagtv.clone()), Value::Temp(ptr.clone()), ptr.typ.clone()));
                            let offsettv = self.block_add_assign(
                                temp![offset, Into::<Type>::into(TypeKind::Void).ptr()],
                                Instruction::Add(Value::Temp(tagtv.clone()), Value::Constant("8".into()))
                            );
                            self.block_add_discard(Instruction::Store(Value::Temp(offsettv.clone()), Value::Temp(long.clone()), long.typ.clone()));
                            Ok(temp![tagtv.tag, slice_type])
                        },
                        _ => return Err(error!(token.loc(), "Cannot initialize {typ} with initializer list")),
                    }
                } else {
                    Err(error!(token.loc(), "Cannot infer type of initializer list"))
                }
            },
            Expr::Range(token, upper, lower) => {
                todo!("probably unreachable!");
            },
            Expr::Cast(token, box_expr, to_typ) => {
                let loc = box_expr.loc();
                let val = self.emit_expr(comptime, *box_expr, Some(to_typ.clone()))?;
                if val.typ.assert_number(loc.clone()).is_ok() && to_typ.assert_number(loc).is_ok() {
                    let tag = self.ctx.alloc();
                    let tv = self.block_add_assign(
                        temp![tag, to_typ.clone()],
                        Instruction::Cast(Value::Temp(val.clone()), to_typ, val.typ.clone())
                    );
                    Ok(tv)
                } else {
                    todo!("unsupported conversion");
                }
            },
        }
    }
}

////////////////////// COMPILETIME //////////////////////

pub struct Compiletime {
    module_map: HashMap<String, Module>,
    method_map: HashMap<Type, HashMap<String, FunctionDecl>>,
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

impl Compiletime {
    pub fn new() -> Self {
        Self {
            module_map: HashMap::new(),
            method_map: HashMap::new(),
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
            let modname = path_to_string(decorated_mod.parse_module.name.clone());
            let name = format!("{modname}.{name}");

            let mut generator = Generator::new(decorated_mod);
            generator.emit(self)?;

            let bf = "./.build/"; // build folder
            if !std::path::Path::new(&bf).exists() {
                std::fs::create_dir(bf).unwrap();
            }

            let mut file = File::create(&format!("{bf}{name}.ssa")).or(Err(error_orphan!("Could not create qbe output file")))?;
            let _ = write!(file, "{}", generator.generated_mod.output);

            // .ssa -> .s
            let qbe_path = options.qbe_path.clone().unwrap_or("qbe".to_string());
            if options.verbose_shell { println!("[CMD] {qbe_path} {bf}{name}.ssa -o {bf}{name}.s") }
            if !Command::new(&qbe_path)
                .arg(&format!("{bf}{name}.ssa"))
                .arg("-o")
                .arg(&format!("{bf}{name}.s"))
                .status()
                .expect("ERROR: qbe not found")
                .success()
            {
                return Err(error_orphan!("Failure with getting assembly from QBE"));
            }

            // .s -> .o
            let assembler_path = options.assembler_path.clone().unwrap_or("cc".to_string());
            if options.verbose_shell { println!("[CMD] {assembler_path} -c {bf}{name}.s -o {bf}{name}.o") }
            if !Command::new(&assembler_path)
                .arg("-c")
                .arg(&format!("{bf}{name}.s"))
                .arg("-o")
                .arg(&format!("{bf}{name}.o"))
                .status()
                .expect("ERROR: qbe not found")
                .success()
            {
                return Err(error_orphan!("Failure with getting object file from assembly"));
            }

            if !options.emit_qbe {
                let path = format!("{bf}{name}.ssa");
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
                let path = format!("{bf}{name}.s");
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

            objs.push(format!("{bf}{name}.o"));
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
}
