use std::fmt::{self, Write, Display};

use crate::ast::*;
use crate::ir::*;
use crate::gen::Compiletime;
use crate::lexer::Location;

impl TempValue {
    fn dump_c<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a TempValue, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "__stack_{}", self.0.tag)
            }
        }
        Helper(self, comptime)
    }
}

impl Block {
    fn dump_c<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a Block, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                // TODO: Value dump_c not implemented yet
                // writeln!(f, "{}", self.0.name.dump_c(self.1))?;
                for stmt in &self.0.stmts {
                    write!(f, "{}", stmt.dump_c(self.1))?;
                }
                Ok(())
            }
        }
        Helper(self, comptime)
    }
}

impl Statement {
    fn dump_c<'a>(&'a self, comptime: &'a Compiletime) -> impl Display + 'a {
        struct Helper<'a>(&'a Statement, &'a Compiletime);
        impl<'a> Display for Helper<'a> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                todo!()
            }
        }
        Helper(self, comptime)
    }
}
