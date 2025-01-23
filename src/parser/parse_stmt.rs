use crate::lexer::{Lexer, Token, Location};
use crate::ast::*;
use crate::Parser;
use crate::parser::Result;
use crate::errors::SyntaxError;

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
            .or_else(|_| {
                let token = self.lexer.peek();
                match token {
                    Token::Eof => Err(error_orphan!("Could not parse stmt: Unexpected end-of-file")),
                    t => Err(error!(t.loc(), "Could not parse stmt: Unexpected token `{t:?}`"))
                }
            });
        stmt
    }

    /*
    <stmt.dbg> = 'dbg' <expr> ';'
    */
    pub fn parse_stmt_dbg(&mut self) -> Result<Stmt> {
        if !self.lexer.eat(Token::Dbg(ldef!())) {
            return Err(error_orphan!("dbg failed"));
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
            return Err(error_orphan!("let failed"));
        }

        let Expr::Ident(token) = self.parse_expr_ident()? else { unreachable!() };
        self.expect(Token::Op(ldef!(), '='))?;
        let expr = self.parse_expr()?;
        self.expect(Token::Op(ldef!(), ';'))?;

        Ok(Stmt::Let(token, expr))
    }
}
