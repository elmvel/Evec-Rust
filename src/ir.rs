use std::fmt;

use crate::ast::{Type, TypeKind, Param, Op, StructKind};
use crate::lexer::Location;

pub trait BackendLLVM {
    fn dump(&self) -> String;
}

pub trait BackendC {
    fn dump(&self) -> String;
}

#[derive(Clone, Debug)]
pub struct TempValue {
    pub typ: Type,
    pub tag: usize,
}

#[derive(Debug)]
pub enum TopLevel {
    Type,
    Data,
    Function(String, Vec<Param>, Option<Type>, Vec<Block>, bool),
}

#[derive(Debug)]
pub struct Block {
    pub name: Value,
    pub stmts: Vec<Statement>,
    pub dead: bool,
}

#[derive(Debug)]
pub enum Value {
    Global(String),
    Constant(String),
    Temp(TempValue),
    Label(String),
}

#[derive(Debug)]
pub enum Statement {
    Assignment(TempValue, Instruction),
    Discard(Instruction),
    Raw(String),
}

#[derive(Debug)]
pub enum Instruction {
    Ret(Option<Value>),
    Copy(Value),
    Add(Value, Value),
    Sub(Value, Value),
    Mul(Value, Value),
    Div(Value, Value),
    DivU(Value, Value),
    Call(Value, Vec<TempValue>), // TODO
    Load(Value, Type), // ptr, as_type
    Store(Value, Value, Type), // ptr, src, into_type
    Alloc(Type), // TODO: will I need more?
    Jmp(Value), // label
    Jnz(Value, Value, Value), // test, labelT, labelF
    Cmp(Op, Type, Value, Value),
    Cast(Value, Type, Type), // value, as_type, from_type
}
