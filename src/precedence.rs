// The general rule is that we use an odd priority as base, and bump it by one for associativity, if the operator is binary

use crate::ast::Op;
use crate::parser::Result;
use crate::errors::SyntaxError;

pub fn infix_binding_power(op: Op) -> Option<(u8, u8)> {
    let res = match op {
        Op::Eq => (2, 1),
        Op::Range => (3, 4),
        Op::OrOr => (5, 6),
        Op::AndAnd => (7, 8),
        Op::EqEq | Op::NotEq => (9, 10),
        Op::Gt | Op::Lt | Op::Ge | Op::Le => (11, 12),
        Op::Add | Op::Sub => (13, 14),
        Op::Mul | Op::Div => (15, 16),
        Op::Dot => (24, 23),
        _ => return None,
    };
    Some(res)
}

pub fn prefix_binding_power(op: Op) -> Result<((), u8)> {
    match op {
        Op::Range => Ok(((), 3)),
        Op::Add | Op::Sub => Ok(((), 17)),
        Op::And | Op::Mul => Ok(((), 19)),
        _ => Err(error_orphan!("Bad expression op: {op:?}")),
    }
}

pub fn postfix_binding_power(op: Op) -> Option<(u8, ())> {
    let res = match op {
        Op::Range => (3, ()),
        Op::Excl | Op::Arr => (21, ()),
        _ => return None,
    };
    Some(res)
}
