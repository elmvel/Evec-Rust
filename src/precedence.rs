// The general rule is that we use an odd priority as base, and bump it by one for associativity, if the operator is binary

use crate::ast::Op;
use crate::parser::Result;
use crate::errors::SyntaxError;

pub fn infix_binding_power(op: Op) -> Option<(u8, u8)> {
    let res = match op {
        Op::Eq => (2, 1),
        Op::OrOr => (4, 3),
        Op::AndAnd => (6, 5),
        Op::Add | Op::Sub => (7, 8),
        Op::Mul | Op::Div => (9, 10),
        Op::Dot => (16, 15),
        _ => return None,
    };
    Some(res)
}

pub fn prefix_binding_power(op: Op) -> Result<((), u8)> {
    match op {
        Op::Add | Op::Sub => Ok(((), 11)),
        _ => Err(error_orphan!("Bad expression op: {op:?}")),
    }
}

pub fn postfix_binding_power(op: Op) -> Option<(u8, ())> {
    let res = match op {
        Op::Excl | Op::Arr => (13, ()),
        _ => return None,
    };
    Some(res)
}
