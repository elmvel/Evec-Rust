use crate::lexer::{Lexer, Token, Location};
use crate::ast::*;
use crate::Parser;
use crate::parser::Result;

impl Parser {
    pub fn parse_stmts(&mut self) -> Result<Vec<Stmt>> {
        let mut stmts = Vec::new();
        self.expect(Token::Op(ldef!(), '{'))?;
        while self.lexer.peek() != Token::Op(ldef!(), '}') {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(Token::Op(ldef!(), '}'))?;
        Ok(stmts)
    }

    pub fn parse_stmt(&mut self) -> Result<Stmt> {
        let stmt = self.parse_stmt_dbg()
            .or(self.parse_stmt_let())
            .or(Err(format!("Could not parse stmt: Unknown token `{:?}`", self.lexer.peek()).into()));
        stmt
    }

    /*
    <stmt.dbg> = 'dbg' <expr> ';'
    */
    pub fn parse_stmt_dbg(&mut self) -> Result<Stmt> {
        if !self.lexer.eat(Token::Dbg(ldef!())) {
            return Err("dbg failed".into());
        }

        let expr = self.parse_expr()?;
        self.expect(Token::Op(ldef!(), ';'))?;

        Ok(Stmt::Dbg(expr))
    }

    /*
    <stmt.let> = 'let' ID '=' <expr> ';'
    */
    pub fn parse_stmt_let(&mut self) -> Result<Stmt> {
        if !self.lexer.eat(Token::Let(ldef!())) {
            return Err("let failed".into());
        }

        let Expr::Ident(token) = self.parse_expr_ident()? else { unreachable!() };
        self.expect(Token::Op(ldef!(), '='))?;
        let expr = self.parse_expr()?;
        self.expect(Token::Op(ldef!(), ';'))?;

        Ok(Stmt::Let(token, expr))
    }
}
