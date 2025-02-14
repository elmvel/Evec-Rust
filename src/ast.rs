use std::fmt;

use crate::lexer::{Token, Location};
use crate::parser::Result;
use crate::errors::SyntaxError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Dot,
    Eq,
    Excl,
    Arr,
    Semi,
    AndAnd,
    OrOr,
    Gt,
    Lt,
    Ge,
    Le,
    EqEq,
    NotEq,
    And,
    Range,
    As,
    Implicit,
}

impl Op {
    pub fn qbe_depends_sign(&self) -> bool {
        return match self {
            Op::Gt | Op::Lt | Op::Ge | Op::Le => true,
            _ => false,
        };
    }
}

impl TryInto<Op> for char {
    type Error = SyntaxError;

    fn try_into(self) -> std::result::Result<Op, Self::Error> {
        match self {
            '+' => Ok(Op::Add),
            '-' => Ok(Op::Sub),
            '*' => Ok(Op::Mul),
            '/' => Ok(Op::Div),
            '.' => Ok(Op::Dot),
            '=' => Ok(Op::Eq),
            '!' => Ok(Op::Excl),
            '[' => Ok(Op::Arr),
            ';' => Ok(Op::Semi),
            '>' => Ok(Op::Gt),
            '<' => Ok(Op::Lt),
            '&' => Ok(Op::And),
            c => Err(error_orphan!("Could not convert to op: {c}")),
        }
    }
}

impl TryInto<Op> for (char, char) {
    type Error = SyntaxError;

    fn try_into(self) -> std::result::Result<Op, Self::Error> {
        match self {
            ('&', '&') => Ok(Op::AndAnd),
            ('|', '|') => Ok(Op::OrOr),
            ('>', '=') => Ok(Op::Ge),
            ('<', '=') => Ok(Op::Le),
            ('=', '=') => Ok(Op::EqEq),
            ('!', '=') => Ok(Op::NotEq),
            ('.', '.') => Ok(Op::Range),
            ('i', 'm') => Ok(Op::Implicit),
            c => Err(error_orphan!("Could not convert to op: {c:?}")),
        }
    }
}

#[derive(Debug)]
pub enum Global {
    DeclModule(Expr), // module main;
    Import(Expr), //import std::io;
    Decl(Token, Expr), // main :: <expr> \ main :: fn() { ... }
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Dbg(Expr),
    Let(Token, Option<Type>, Expr),
    Scope(Vec<Stmt>),
    Ex(Expr), // C-style: a+b; foo();
    If(Expr, Box<Stmt>, Option<Box<Stmt>>),
    While(Expr, Box<Stmt>),
    Break(Location),
    Continue(Location),
    Return(Location, Option<Expr>, bool, bool), // bools are ugly hacks
    Defer(Location, Box<Stmt>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param(pub Token, pub Type);

#[derive(Debug, Clone)]
pub enum Expr {
    Ident(Token), // foo
    Path(Token, Box<Expr>), // std::io => (String std) (::) (*Expr(io))
    Number(Token),
    String(Token),
    CString(Token),
    Bool(Token),
    BinOp(Token, Op, Box<Expr>, Box<Expr>),
    UnOp(Token, Op, Box<Expr>, bool), // bool stores prefix/postfix
    Func(Token, Vec<Param>, Option<Type>, Vec<Stmt>, bool, Vec<Attribute>),
    FuncDecl(Token, Vec<Param>, Option<Type>, Vec<Attribute>),
    Call(Box<Expr>, Vec<Expr>), // TODO: add parameters
    Null(Token),
    InitList(Token, Vec<Expr>), // First token is just for easy location
    Range(Token, Option<Box<Expr>>, Option<Box<Expr>>),
    Cast(Token, Box<Expr>, Type),
}

impl Expr {
    pub fn loc(&self) -> Location {
        match self {
            Expr::Ident(t) => t.loc(),
            Expr::Path(t, _) => t.loc(),
            Expr::Number(t) => t.loc(),
            Expr::String(t) => t.loc(),
            Expr::CString(t) => t.loc(),
            Expr::Bool(t) => t.loc(),
            Expr::BinOp(t, _, _, _) => t.loc(),
            Expr::UnOp(t, _, _, _) => t.loc(),
            Expr::Func(t, _, _, _, _, _) => t.loc(),
            Expr::FuncDecl(t, _, _, _) => t.loc(),
            Expr::Call(t, _) => t.loc(),
            Expr::Null(t) => t.loc(),
            Expr::InitList(t, _) => t.loc(),
            Expr::Range(t, _, _) => t.loc(),
            Expr::Cast(t, _, _) => t.loc(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Attribute {
    Extern(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Type {
    pub kind: TypeKind,
    pub indirection: u8, // How many pointers do we have
    pub struct_kind: StructKind,
    // pub inner_type: u64, // We don't need this to exist now, but it should point to the typekind of the inner field?
    pub elements: usize, // Compile time only
    pub infer_elements: bool,
    pub inner: Option<Box<Type>>,
    pub alias: Option<String>,
}

impl Into<Type> for TypeKind {
    fn into(self) -> Type {
        Type {
            kind: self,
            indirection: 0,
            struct_kind: StructKind::CountStructs,
            elements: 0,
            infer_elements: false,
            inner: None,
            alias: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum TypeKind {
    Unresolved,
    Void,
    U64,
    U32,
    U16,
    U8,
    S64,
    S32,
    S16,
    S8,
    Bool,
    Structure,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum StructKind {
    Array,
    Slice,
    CountStructs,
}

impl Type {
    pub fn copy(other: &Type) -> Self {
        Self {
            kind: other.kind.clone(),
            indirection: other.indirection,
            struct_kind: other.struct_kind.clone(),
            elements: other.elements,
            infer_elements: other.infer_elements,
            inner: other.inner.clone(),
            alias: None,
        }
    }

    pub fn wrap(typ: Type, struct_kind: StructKind, elements: Option<usize>, infer_elements: bool) -> Self {
        Self {
            kind: TypeKind::Structure,
            indirection: 0,
            struct_kind: struct_kind,
            elements: elements.unwrap_or(0),
            infer_elements,
            inner: Some(Box::new(typ)),
            alias: None,
        }
    }

    pub fn alias(name: String) -> Self {
        let mut typ: Type = TypeKind::Unresolved.into();
        typ.alias = Some(name);
        typ
    }

    pub fn is_struct(&self) -> bool {
        self.kind == TypeKind::Structure
    }

    pub fn is_ptr(&self) -> bool {
        self.indirection > 0
    }
    
    pub fn is_void_ptr(&self) -> bool {
        self.is_ptr() && self.kind == TypeKind::Void
    }
    
    pub fn ptr(&self) -> Self {
        Self {
            kind: self.kind.clone(),
            indirection: self.indirection + 1,
            struct_kind: self.struct_kind.clone(),
            elements: self.elements,
            infer_elements: self.infer_elements,
            inner: self.inner.clone(),
            alias: self.alias.clone(),
        }
    }

    pub fn deref(&self) -> Self {
        Self {
            kind: self.kind.clone(),
            indirection: self.indirection.checked_sub(1).unwrap_or(0),
            struct_kind: self.struct_kind.clone(),
            elements: self.elements,
            infer_elements: self.infer_elements,
            inner: self.inner.clone(),
            alias: self.alias.clone(),
        }
    }
    
    pub fn qbe_type(&self) -> &str {
        if self.is_ptr() {
            return "l"; // Must be a pointer
        }
        match self.kind {
            TypeKind::U64 => "l",
            TypeKind::U32 | TypeKind::U16 | TypeKind::U8 => "w",
            TypeKind::S64 => "l",
            TypeKind::S32 | TypeKind::S16 | TypeKind::S8 => "w",
            TypeKind::Void | TypeKind::Bool => "w",
            TypeKind::Unresolved => unreachable!(),
            TypeKind::Structure => {
                match self.struct_kind {
                    StructKind::Array => {
                        "l"
                    },
                    StructKind::Slice => {
                        "l"
                    },
                    _ => todo!("Should be able to determine the structure qbe type based on the struct id"),
                }
            },
        }
    }

    // NOTE: NOT equivalent to ABITY in QBE docs
    // This is strictly for temporaries, where we may want to indicate that we are
    // recieving a struct from a call
    pub fn qbe_abi_type(&self) -> &str {
        if self.kind == TypeKind::Structure {
            self.qbe_ext_type()
        } else {
            self.qbe_type()
        }
    }

    pub fn qbe_ext_type(&self) -> &str {
        if self.is_ptr() {
            return "l";
        }
        match self.kind {
            TypeKind::U64 | TypeKind::S64 => "l",
            TypeKind::U32 | TypeKind::S32 => "w",
            TypeKind::U16 => "uh",
            TypeKind::S16 => "sh",
            TypeKind::U8  => "ub",
            TypeKind::S8  => "sb",
            TypeKind::Void | TypeKind::Bool => "w",
            TypeKind::Unresolved => unreachable!(),
            TypeKind::Structure => {
                match self.struct_kind {
                    StructKind::Array => {
                        "l"
                    },
                    StructKind::Slice => {
                        ":slice"
                    },
                    _ => todo!("Should be able to determine the structure qbe type based on the struct id"),
                }
            },
        }
    }

    pub fn sizeof(&self) -> usize {
        if self.is_ptr() {
            return 8;
        }
        match self.kind {
            TypeKind::U64 | TypeKind::S64 => 8,
            TypeKind::U32 | TypeKind::S32 => 4,
            TypeKind::U16 | TypeKind::S16 => 2,
            TypeKind::U8  | TypeKind::S8 => 1,
            TypeKind::Bool => 4,
            TypeKind::Void => 0,
            TypeKind::Unresolved => unreachable!(),
            TypeKind::Structure => {
                match self.struct_kind {
                    StructKind::Array => {
                        let Some(ref inner) = self.inner else { unreachable!() };
                        self.elements * inner.sizeof()
                    },
                    StructKind::Slice => {
                        16
                    },
                    _ => todo!("need to lookup in some strucure table"),
                }
            },
        }
    }

    pub fn assert_number(&self, loc: Location) -> Result<()> {
        if self.is_ptr() {
            return Err(error!(loc, "Expected type to be a number"));
        }
        match self.kind {
            TypeKind::U64 | TypeKind::U32 | TypeKind::U16 | TypeKind::U8 |
            TypeKind::S64 | TypeKind::S32 | TypeKind::S16 | TypeKind::S8 => Ok(()),
            _ => Err(error!(loc, "Expected type to be a number")),
        }
    }

    pub fn assert_comparable(&self, loc: Location) -> Result<()> {
        if self.is_ptr() {
            return Ok(());
        }
        match self.kind {
            TypeKind::U64 | TypeKind::U32 | TypeKind::U16 | TypeKind::U8 |
            TypeKind::S64 | TypeKind::S32 | TypeKind::S16 | TypeKind::S8 => Ok(()),
            _ => Err(error!(loc, "Expected type to be a number")),
        }
    }

    pub fn assert_bool(&self, loc: Location) -> Result<()> {
        if self.is_ptr() {
            return Err(error!(loc, "Expected boolean"));
        }
        match self.kind {
            TypeKind::Bool => Ok(()),
            _ => Err(error!(loc, "Expected boolean")),
        }
    }

    pub fn assert_indexable(&self, loc: Location) -> Result<()> {
        if self.is_ptr() {
            return Ok(());
        }
        if self.is_struct() {
            match self.struct_kind {
                StructKind::Array | StructKind::Slice => { Ok(()) },
                _ => todo!("Probably allow slices too, but nothing else (maybe strings)"),
            }
        } else {
            Err(error!(loc, "Cannot index type {self}"))
        }
    }

    pub fn unsigned(&self) -> bool {
        match self.kind {
            TypeKind::U64 | TypeKind::U32 | TypeKind::U16 | TypeKind::U8 => true,
            _ => false,
        }
    }

    pub fn soft_equals_array(&mut self, rhs: &mut Type) -> bool {
        if self.infer_elements && !rhs.infer_elements {
            self.elements = rhs.elements;
            self.infer_elements = false;
        }
        if !self.infer_elements && rhs.infer_elements {
            rhs.elements = self.elements;
            rhs.infer_elements = false;
        }
        if self.is_ptr() && rhs.is_void_ptr() {
            todo!("assigning void ptr?");
        }
        self.soft_equals(rhs)
    }

    pub fn soft_equals(&mut self, rhs: &Type) -> bool {
        // can convert between *void <=> *type
        if self.is_void_ptr() && rhs.is_ptr() || self.is_ptr() && rhs.is_void_ptr() {
            *self = Type::copy(rhs);
            return true;
        }
        self == rhs
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.indirection {
            write!(f, "*")?;
        }
        match &self.kind {
            TypeKind::Void => write!(f, "void"),
            TypeKind::U64 => write!(f, "u64"),
            TypeKind::U32 => write!(f, "u32"),
            TypeKind::U16 => write!(f, "u16"),
            TypeKind::U8 => write!(f, "u8"),
            TypeKind::S64 => write!(f, "s64"),
            TypeKind::S32 => write!(f, "s32"),
            TypeKind::S16 => write!(f, "s16"),
            TypeKind::S8 => write!(f, "s8"),
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Unresolved => write!(f, "<unknown type alias>"),
            TypeKind::Structure => {
                match self.struct_kind {
                    StructKind::Array => {
                        let Some(ref inner) = self.inner else { unreachable!("idk how to error out here") };
                        write!(f, "[{}]{}", self.elements, *inner)
                    }, 
                    StructKind::Slice => {
                        let Some(ref inner) = self.inner else { unreachable!("idk how to error out here") };
                        write!(f, "[]{}", *inner)
                    },
                    _ => todo!("Another structure table call"),
                }
            },
        }
    }
}
