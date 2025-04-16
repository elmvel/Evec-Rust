use std::fmt;

use crate::const_eval::*;
use crate::errors::SyntaxError;
use crate::gen::{Generator, Symbol, SymbolTable};
use crate::lexer::{Location, Token};
use crate::parser::Result;
use crate::Compiletime;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    DeclModule(Expr),  // module main;
    Import(Expr),      //import std::io;
    Decl(Token, Expr), // main :: <expr> \ main :: fn() { ... }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    Dbg(Expr),
    Let(Token, Option<AstType>, Expr, bool), // bool -> const?
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
pub struct AstParam(pub Token, pub AstType);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param(pub Token, pub Type);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Ident(Token),           // foo
    Path(Token, Box<Expr>), // std::io => (String std) (::) (*Expr(io))
    Number(Token),
    String(Token),
    CString(Token),
    Bool(Token),
    BinOp(Token, Op, Box<Expr>, Box<Expr>),
    UnOp(Token, Op, Box<Expr>, bool), // bool stores prefix/postfix
    Func(
        Token,
        Vec<AstParam>,
        Option<AstType>,
        Vec<Stmt>,
        bool,
        Vec<Attribute>,
    ),
    FuncDecl(Token, Vec<AstParam>, Option<AstType>, Vec<Attribute>),
    Call(Box<Expr>, Vec<Expr>), // TODO: add parameters
    Null(Token),
    InitList(Token, Vec<Expr>), // First token is just for easy location
    Range(Token, Option<Box<Expr>>, Option<Box<Expr>>),
    Cast(Token, Box<Expr>, AstType),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Attribute {
    Extern(Expr),
}

// This is a recursive, syntax representation of a type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AstType {
    Base(Type), // A non-recursive type, to avoid redundancy
    Alias(String),
    Ptr(Box<AstType>),
    Array(LazyExpr, Box<AstType>, bool),
    Slice(Box<AstType>),
}

impl AstType {
    // TODO: Don't Repeat Yourself
    pub fn as_type_table(self, comptime: &mut Compiletime) -> Type {
        match self {
            AstType::Base(typ) => typ.clone(),
            AstType::Alias(name) => {
                let typeid = comptime
                    .symbol_table
                    .get(&name)
                    .filter(|e| matches!(e, Symbol::TypeAlias(_)))
                    .map(|e| {
                        let Symbol::TypeAlias(tid) = e else {
                            unreachable!()
                        };
                        tid
                    })
                    .unwrap();
                comptime.fetch_type(*typeid).unwrap().clone()
            }
            AstType::Ptr(box_astype) => {
                let typ = box_astype.as_type_table(comptime);
                let typeid = comptime.fetch_typeid(&typ);
                Type::Ptr(typeid)
            }
            AstType::Array(lazyexpr, box_astype, _) => {
                let typ = box_astype.as_type_table(comptime);
                let typeid = comptime.fetch_typeid(&typ);
                Type::Array(lazyexpr, typeid)
            }
            AstType::Slice(box_astype) => {
                let typ = box_astype.as_type_table(comptime);
                let typeid = comptime.fetch_typeid(&typ);
                Type::Slice(typeid)
            }
        }
    }

    pub fn as_type(self, comptime: &mut Compiletime, gen: &mut Generator) -> Result<Type> {
        match self {
            AstType::Base(typ) => Ok(typ.clone()),
            AstType::Alias(name) => {
                let option = gen
                    .symbol_lookup_fuzzy(comptime, &name, false)
                    .filter(|e| matches!(e, (Symbol::TypeAlias(_), _)))
                    .map(|e| {
                        let (Symbol::TypeAlias(tid), _) = e else {
                            unreachable!()
                        };
                        tid
                    });
                if let Some(typeid) = option {
                    Ok(comptime.fetch_type(*typeid).unwrap().clone())
                } else {
                    return Err(error_orphan!("Unknown type alias `{name}`"));
                }
            }
            AstType::Ptr(box_astype) => {
                let typ = box_astype.as_type(comptime, gen)?;
                let typeid = comptime.fetch_typeid(&typ);
                Ok(Type::Ptr(typeid))
            }
            AstType::Array(lazyexpr, box_astype, _) => {
                let typ = box_astype.as_type(comptime, gen)?;
                let typeid = comptime.fetch_typeid(&typ);
                Ok(Type::Array(lazyexpr, typeid))
            }
            AstType::Slice(box_astype) => {
                let typ = box_astype.as_type(comptime, gen)?;
                let typeid = comptime.fetch_typeid(&typ);
                Ok(Type::Slice(typeid))
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TypeId(pub usize);

// This is a definitive internal representation of a type compiled from AstType
// This is necessary due to the usage of a TypeId system, which cannot be known
// during parsing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
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
    Ptr(TypeId),
    Array(LazyExpr, TypeId),
    Slice(TypeId), // Might not be correct
}

impl Type {
    // pub fn copy(other: &Type) -> Self {
    //     Self {
    //         kind: other.kind.clone(),
    //         indirection: other.indirection,
    //         struct_kind: other.struct_kind.clone(),
    //         elements: other.elements.clone(),
    //         infer_elements: other.infer_elements,
    //         inner: other.inner.clone(),
    //         alias: None,
    //     }
    // }

    // pub fn wrap(typ: Type, struct_kind: StructKind, elements: LazyExpr, infer_elements: bool) -> Self {
    //     Self {
    //         kind: TypeKind::Structure,
    //         indirection: 0,
    //         struct_kind: struct_kind,
    //         elements: elements,
    //         infer_elements,
    //         inner: Some(Box::new(typ)),
    //         alias: None,
    //     }
    // }

    // pub fn alias(name: String) -> Self {
    //     let mut typ: Type = TypeKind::Unresolved.into();
    //     typ.alias = Some(name);
    //     typ
    // }

    pub fn is_struct(&self) -> bool {
        match self {
            Type::Array(..) => true,
            Type::Slice(..) => true,
            _ => false,
        }
    }

    pub fn is_ptr(&self) -> bool {
        match self {
            Type::Ptr(..) => true,
            _ => false,
        }
    }

    pub fn is_void_ptr(&self, comptime: &mut Compiletime) -> bool {
        match self {
            Type::Ptr(tid) => {
                let result = comptime.fetch_type(*tid);
                if let Some(inner) = result {
                    *inner == Type::Void
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    pub fn ptr(&self, comptime: &mut Compiletime) -> Self {
        Type::Ptr(comptime.fetch_typeid(self))
    }

    pub fn deref(&self, comptime: &Compiletime) -> Self {
        match self {
            Type::Ptr(tid) => comptime.fetch_type(*tid).unwrap().clone(),
            t => t.clone(),
        }
    }

    pub fn qbe_type(&self) -> &str {
        match self {
            Type::U64 => "l",
            Type::U32 | Type::U16 | Type::U8 => "w",
            Type::S64 => "l",
            Type::S32 | Type::S16 | Type::S8 => "w",
            Type::Void | Type::Bool => "w",
            Type::Ptr(..) => "l",
            Type::Array(..) | Type::Slice(..) => "l",
        }
    }

    // NOTE: NOT equivalent to ABITY in QBE docs
    // This is strictly for temporaries, where we may want to indicate that we are
    // recieving a struct from a call
    pub fn qbe_abi_type(&self) -> &str {
        if self.is_struct() {
            self.qbe_ext_type()
        } else {
            self.qbe_type()
        }
    }

    pub fn qbe_ext_type(&self) -> &str {
        match self {
            Type::U64 | Type::S64 => "l",
            Type::U32 | Type::S32 => "w",
            Type::U16 => "uh",
            Type::S16 => "sh",
            Type::U8 => "ub",
            Type::S8 => "sb",
            Type::Void | Type::Bool => "w",
            Type::Ptr(..) => "l",
            Type::Array(..) => "l",
            Type::Slice(..) => ":slice",
        }
    }

    pub fn sizeof(&self, comptime: &Compiletime) -> usize {
        match self {
            Type::U64 | Type::S64 => 8,
            Type::U32 | Type::S32 => 4,
            Type::U16 | Type::S16 => 2,
            Type::U8 | Type::S8 => 1,
            Type::Bool => 4,
            Type::Void => 0,
            Type::Ptr(..) => 8,
            Type::Array(count, tid) => {
                let inner = comptime.fetch_type(*tid).unwrap();
                let constexpr = count.const_resolve();
                match constexpr {
                    ConstExpr::Number(n) => n as usize * inner.sizeof(comptime),
                }
            }
            Type::Slice(..) => 16,
        }
    }

    pub fn assert_number(&self, loc: Location) -> Result<()> {
        match self {
            Type::U64
            | Type::U32
            | Type::U16
            | Type::U8
            | Type::S64
            | Type::S32
            | Type::S16
            | Type::S8 => Ok(()),
            _ => Err(error!(loc, "Expected type to be a number")),
        }
    }

    pub fn assert_comparable(&self, loc: Location) -> Result<()> {
        match self {
            Type::U64
            | Type::U32
            | Type::U16
            | Type::U8
            | Type::S64
            | Type::S32
            | Type::S16
            | Type::S8
            | Type::Ptr(..) => Ok(()),
            _ => Err(error!(loc, "Expected type to be a number")),
        }
    }

    pub fn assert_bool(&self, loc: Location) -> Result<()> {
        match self {
            Type::Bool => Ok(()),
            _ => Err(error!(loc, "Expected boolean")),
        }
    }

    // TODO: Probably strings at some point too
    pub fn assert_indexable(&self, loc: Location, comptime: &Compiletime) -> Result<()> {
        if self.is_ptr() {
            return Ok(());
        }
        match self {
            Type::Ptr(..) => Ok(()),
            Type::Array(..) => Ok(()),
            Type::Slice(..) => Ok(()),
            _ => Err(error!(
                loc,
                "Cannot index type {}",
                (self.display(comptime))
            )),
        }
    }

    pub fn unsigned(&self) -> bool {
        match self {
            Type::U64 | Type::U32 | Type::U16 | Type::U8 => true,
            _ => false,
        }
    }

    pub fn check_coerce_array(
        &mut self,
        rhs: &mut Type,
        infer_elements: bool,
        comptime: &mut Compiletime,
    ) -> bool {
        if infer_elements {
            if let Type::Array(ref mut lhs_lazyexpr, _) = self {
                if let Type::Array(ref mut rhs_lazyexpr, _) = rhs {
                    *rhs_lazyexpr = lhs_lazyexpr.clone();
                }
            }
        }
        if self.is_ptr() && rhs.is_void_ptr(comptime) {
            todo!("assigning void ptr?");
        }
        self.check_coerce(rhs, comptime)
    }

    pub fn check_coerce(&mut self, rhs: &Type, comptime: &mut Compiletime) -> bool {
        // can convert between *void <=> *type
        if self.is_void_ptr(comptime) && rhs.is_ptr() || self.is_ptr() && rhs.is_void_ptr(comptime)
        {
            *self = rhs.clone();
            return true;
        }
        self == rhs
    }

    pub fn get_inner<'a>(&self, comptime: &'a Compiletime) -> Option<&'a Type> {
        match self {
            Type::Array(_, typeid) | Type::Slice(typeid) => comptime.fetch_type(*typeid),
            _ => None,
        }
    }

    pub fn display(&self, comptime: &Compiletime) -> String {
        match self {
            Type::Void => "void".into(),
            Type::U64 => "u64".into(),
            Type::U32 => "u32".into(),
            Type::U16 => "u16".into(),
            Type::U8 => "u8".into(),
            Type::S64 => "s64".into(),
            Type::S32 => "s32".into(),
            Type::S16 => "s16".into(),
            Type::S8 => "s8".into(),
            Type::Bool => "bool".into(),
            Type::Ptr(tid) => format!("*{}", comptime.fetch_type(*tid).unwrap().display(comptime)),
            Type::Array(count, tid) => {
                let inner = comptime.fetch_type(*tid).unwrap();
                let constexpr = count.const_resolve();
                format!("[{}]{}", constexpr, inner.display(comptime))
            }
            Type::Slice(tid) => {
                let inner = comptime.fetch_type(*tid).unwrap();
                format!("[]{}", inner.display(comptime))
            }
        }
    }
}

impl fmt::Display for AstType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AstType::Base(typ) => match typ {
                Type::Void => write!(f, "void"),
                Type::U64 => write!(f, "u64"),
                Type::U32 => write!(f, "u32"),
                Type::U16 => write!(f, "u16"),
                Type::U8 => write!(f, "u8"),
                Type::S64 => write!(f, "s64"),
                Type::S32 => write!(f, "s32"),
                Type::S16 => write!(f, "s16"),
                Type::S8 => write!(f, "s8"),
                Type::Bool => write!(f, "bool"),
                _ => unreachable!("missing a case?"),
            },
            AstType::Alias(name) => write!(f, "{name}"),
            AstType::Ptr(box_astype) => write!(f, "*{box_astype}"),
            AstType::Array(lazyexpr, box_astype, _) => write!(f, "[N]{box_astype}"),
            AstType::Slice(box_astype) => write!(f, "[]{box_astype}"),
        }
    }
}
