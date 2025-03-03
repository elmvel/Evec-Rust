use crate::ir::BackendC;

use crate::lexer::Location;
use crate::ast::*;
use crate::ir::*;

impl BackendC for TempValue {
    fn dump(&self) -> String {
        format!("__stack_{}", self.tag)
    }
}

impl BackendC for Block {
    fn dump(&self) -> String {
        let mut stmts = String::new();
        for stmt in &self.stmts {
            stmts.push_str(&format!("{}", stmt.dump()));
        }
        stmts
    }
}

impl BackendC for Statement {
    fn dump(&self) -> String {
        todo!()
    }
}
