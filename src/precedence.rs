// The general rule is that we use an odd priority as base, and bump it by one for associativity, if the operator is binary

use crate::parser::Result;
use crate::errors::SyntaxError;

pub fn infix_binding_power(op: char) -> Option<(u8, u8)> {
    let res = match op {
        '=' => (2, 1),
        '+' | '-' => (3, 4),
        '*' | '/' => (5, 6),
        '.' => (12, 11),
        _ => return None,
    };
    Some(res)
}

pub fn prefix_binding_power(op: char) -> Result<((), u8)> {
    match op {
        '+' | '-' => Ok(((), 7)),
        _ => Err(error_orphan!("Bad expression op: {op:?}")),
    }
}

pub fn postfix_binding_power(op: char) -> Option<(u8, ())> {
    let res = match op {
        '!' | '[' => (9, ()),
        _ => return None,
    };
    Some(res)
}
