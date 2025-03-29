use std::fmt;

use crate::ast::*;
use crate::errors::SyntaxError;
use crate::gen::{Generator, Compiletime};
use crate::lexer::{Location, Token};
use crate::parser::Result;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstExpr {
    Number(i64),
}

#[derive(Default, Debug, Clone, Hash)]
pub struct LazyExpr(Option<Box<Expr>>, Option<ConstExpr>);

impl LazyExpr {
    pub fn make_constant(constexpr: ConstExpr) -> Self {
        Self(None, Some(constexpr))
    }

    pub fn make_expr(expr: Expr) -> Self {
        Self(Some(Box::new(expr)), None)
    }

    pub fn const_eval(&mut self, gen: &mut Generator) -> Result<()> {
        if self.0.is_none() {
            return Ok(());
        }

        let Some(ref expr) = self.0 else {
            unreachable!()
        };
        let constexpr = match **expr {
            Expr::Number(Token::Int(_, n)) => ConstExpr::Number(n),
            Expr::Ident(Token::Ident(ref loc, ref text)) => {
                let expr = gen.ctx.lookup_constant(&text, loc.clone())?;
                expr.into()
            }
            _ => todo!("constant evaluate {expr:?}"),
        };

        self.0 = None;
        self.1 = Some(constexpr);
        Ok(())
    }

    pub fn const_resolve(&self) -> ConstExpr {
        self.1.clone().unwrap()
    }
}

pub fn type_resolve(gen: &mut Generator, mut typ: Type, comptime: &mut Compiletime) -> Result<Type> {
    match typ {
        Type::Array(ref mut count, ref mut typeid) => {
            count.const_eval(gen)?;

            let inner = comptime.fetch_type(*typeid).unwrap().clone();
            let resolved = type_resolve(gen, inner, comptime)?;
            comptime.fix_type(*typeid, resolved);
            
            Ok(typ)
        },
        Type::Slice(ref mut typeid) => {
            let inner = comptime.fetch_type(*typeid).unwrap().clone();
            let resolved = type_resolve(gen, inner, comptime)?;
            comptime.fix_type(*typeid, resolved);

            Ok(typ)
        },
        _ => Ok(typ),
    }
}

impl PartialEq for LazyExpr {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

impl Eq for LazyExpr {}

impl Into<Expr> for ConstExpr {
    fn into(self) -> Expr {
        match self {
            ConstExpr::Number(i) => Expr::Number(Token::Int(ldef!(), i)),
        }
    }
}

impl Into<ConstExpr> for Expr {
    fn into(self) -> ConstExpr {
        match self {
            Expr::Number(Token::Int(_, i)) => ConstExpr::Number(i),
            _ => todo!(),
        }
    }
}

impl fmt::Display for ConstExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstExpr::Number(i) => write!(f, "{i}"),
        }
    }
}
