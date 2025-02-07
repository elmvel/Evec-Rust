use std::collections::HashSet;

use crate::lexer::Token;
use crate::parser::ParseModule;
use crate::ast::*;

pub struct DecoratedModule {
    pub parse_module: ParseModule,
    pub addressed_vars: HashSet<String>,
}

impl DecoratedModule {
    pub fn new(parse_module: ParseModule) -> Self {
        Self {
            parse_module,
            addressed_vars: HashSet::new(),
        }
    }
}

pub struct Decorator {
    pub decorated_mod: DecoratedModule,
}

impl Decorator {
    pub fn new(parse_module: ParseModule) -> Self {
        Self {
            decorated_mod: DecoratedModule::new(parse_module),
        }
    }

    pub fn decorate(&mut self) {
        let addressed_vars = self.get_addressed_variables();
        self.decorated_mod.addressed_vars = addressed_vars;
        self.return_check();
    }

    // rtc
    pub fn return_check(&mut self) {
        for global in self.decorated_mod.parse_module.globals.iter_mut() {
            Self::rtc_global(global);
        }
    }

    pub fn rtc_global(global: &mut Global) {
        match global {
            Global::Decl(_, ref mut expr) => {
                Self::rtc_expr(expr);  
            },
            _ => (),
        }
    }

    pub fn rtc_expr(expr: &mut Expr) -> () {
        match expr {
            Expr::Ident(_) => { () },
            Expr::Path(_, _) => { () },
            Expr::Number(_) => { () },
            Expr::Bool(_) => { () },
            Expr::BinOp(_, _, _, _) => { () },
            Expr::UnOp(_, _, _, _) => { () },
            Expr::Func(_, _, _, stmts, ref mut ret) => {
                let mut returns = false;
                for stmt in stmts {
                    if Self::rtc_stmt(stmt) {
                        returns = true;
                    }
                }
                *ret = returns;
            },
            Expr::Call(_, _) => { () },
            Expr::Null(_) => { () },
            Expr::InitList(_, _) => { () },
            Expr::Range(_, _, _) => { () },
        }
    }

    pub fn rtc_stmt(stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Dbg(_) => { false },
            Stmt::Let(_, _, _) => { false },
            Stmt::Scope(stmts) => {
                let mut returns = false;
                for stmt in stmts {
                    if Self::rtc_stmt(stmt) {
                        returns = true;
                    }
                }
                returns
            },
            Stmt::Ex(_) => { false },
            Stmt::If(_, box_stmt, opt) => {
                // A condition is not enough, since it can be false
                // Only in if-else where both branches are always reached do we check for returns
                let mut returns = Self::rtc_stmt(box_stmt);
                if let Some(box_else_block) = opt {
                    if returns {
                        returns = Self::rtc_stmt(box_else_block);
                    }
                } else {
                    returns = false;
                }
                returns
            },
            Stmt::While(_, _) => { false },
            Stmt::Break(_) => { false },
            Stmt::Continue(_) => { false },
            Stmt::Return(_, _) => {
                true
            },
        }
    }

    // gav
    pub fn get_addressed_variables(&mut self) -> HashSet<String> {
        let mut addrvars = HashSet::new();
        for global in self.decorated_mod.parse_module.globals.iter() {
            Self::gav_global(global, &mut addrvars);
        }
        addrvars
    }

    pub fn gav_global(global: &Global, addrvars: &mut HashSet<String>) {
        match global {
            Global::Decl(_, expr) => Self::gav_expr(expr, addrvars),
            _ => ()
        }
    }

    pub fn gav_expr(expr: &Expr, addrvars: &mut HashSet<String>) {
        match expr {
            Expr::Ident(_) => { () },
            Expr::Path(_, _) => { () },
            Expr::Number(_) => { () },
            Expr::Bool(_) => { () },
            Expr::BinOp(_, _, box_lhs, box_rhs) => {
                Self::gav_expr(box_lhs, addrvars);
                Self::gav_expr(box_rhs, addrvars);
            },
            Expr::UnOp(_, op, box_expr, _) => {
                if *op == Op::And {
                    if let Expr::Ident(Token::Ident(_, ref text)) = **box_expr {
                        addrvars.insert(text.clone());
                    }
                }
            },
            Expr::Func(_, _, _, stmts, _) => {
                for stmt in stmts {
                    Self::gav_stmt(stmt, addrvars);
                }
            },
            Expr::Call(name, args) => {
                for expr in args {
                    Self::gav_expr(expr, addrvars);
                }
            },
            Expr::Null(_) => { () },
            Expr::InitList(_, exprs) => {
                for expr in exprs {
                    Self::gav_expr(expr, addrvars);
                }
            },
            Expr::Range(_, _, _) => { /* Even though we have expressions here, they cannot be pointers */ () },
        }
    }

    pub fn gav_stmt(stmt: &Stmt, addrvars: &mut HashSet<String>) {
        match stmt {
            Stmt::Dbg(expr) => {
                Self::gav_expr(expr, addrvars);
            },
            Stmt::Let(_, _, expr) => {
                Self::gav_expr(expr, addrvars);
            },
            Stmt::Scope(stmts) => {
                for stmt in stmts {
                    Self::gav_stmt(stmt, addrvars);
                }
            },
            Stmt::Ex(expr) => {
                Self::gav_expr(expr, addrvars);
            },
            Stmt::If(expr, box_stmt, opt) => {
                Self::gav_expr(expr, addrvars);
                Self::gav_stmt(box_stmt, addrvars);
                if let Some(box_else_block) = opt {
                    Self::gav_stmt(box_else_block, addrvars);
                }
            },
            Stmt::While(expr, box_stmt) => {
                Self::gav_expr(expr, addrvars);
                Self::gav_stmt(box_stmt, addrvars);
            },
            Stmt::Break(_) => { () },
            Stmt::Continue(_) => { () },
            Stmt::Return(_, opt) => {
                if let Some(expr) = opt {
                    Self::gav_expr(expr, addrvars);
                }
            },
        }
    }
}
