// The general rule is that we use an odd priority as base, and bump it by one for associativity, if the operator is binary

use crate::ast::Op;
use crate::parser::Result;
use crate::errors::SyntaxError;

pub fn infix_binding_power(op: Op) -> Option<(u8, u8)> {
    let res = match op {
        Op::Eq => (2, 1),
        Op::OrOr => (3, 4),
        Op::AndAnd => (5, 6),
        Op::Gt => (7, 8),
        Op::Add | Op::Sub => (9, 10),
        Op::Mul | Op::Div => (11, 12),
        Op::Dot => (18, 17),
        _ => return None,
    };
    Some(res)
}

pub fn prefix_binding_power(op: Op) -> Result<((), u8)> {
    match op {
        Op::Add | Op::Sub => Ok(((), 13)),
        _ => Err(error_orphan!("Bad expression op: {op:?}")),
    }
}

pub fn postfix_binding_power(op: Op) -> Option<(u8, ())> {
    let res = match op {
        Op::Excl | Op::Arr => (15, ()),
        _ => return None,
    };
    Some(res)
}
