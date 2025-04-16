use crate::ast::*;
use crate::const_eval::{ConstExpr, LazyExpr};
use crate::constants::MODULE_SEPARATOR;
use crate::errors::SyntaxError;
use crate::lexer::{Lexer, Location, Token};
use crate::parser::Result;
use crate::Parser;

// This only bubbles out if we have a successful parse OR we have an error
// Getting a None value signals the parser to ONLY soft fail, hence the macro
macro_rules! bubble_stmt {
    ($result:expr) => {
        match $result {
            Ok(opt) => {
                if let Some(stmt) = opt {
                    return Ok(stmt);
                }
            }
            Err(e) => return Err(e),
        }
    };
}

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
        bubble_stmt!(self.parse_stmt_scope());
        bubble_stmt!(self.parse_stmt_dbg());
        bubble_stmt!(self.parse_stmt_let());
        bubble_stmt!(self.parse_stmt_if());
        bubble_stmt!(self.parse_stmt_while());
        bubble_stmt!(self.parse_stmt_break());
        bubble_stmt!(self.parse_stmt_continue());
        bubble_stmt!(self.parse_stmt_return());
        bubble_stmt!(self.parse_stmt_defer());

        bubble_stmt!(self.parse_stmt_expr());

        let token = self.lexer.peek();
        match token {
            Token::Eof => Err(error_orphan!(
                "Could not parse stmt: Unexpected end-of-file"
            )),
            t => Err(error!(
                t.loc(),
                "Could not parse stmt: Unexpected token `{t:?}`"
            )),
        }
    }

    /*
    <stmt.dbg> ::= 'dbg' <expr> ';'
    */
    pub fn parse_stmt_dbg(&mut self) -> Result<Option<Stmt>> {
        if !self.lexer.eat(Token::Dbg(ldef!())) {
            return Ok(None);
        }

        let expr = self.parse_expr()?;
        self.expect(Token::Op(ldef!(), ';'))?;

        Ok(Some(Stmt::Dbg(expr)))
    }

    pub fn parse_type(&mut self) -> Result<AstType> {
        if self.lexer.eat(Token::Op(ldef!(), '*')) {
            Ok(AstType::Ptr(Box::new(self.parse_type()?)))
        } else if self.lexer.eat(Token::Op(ldef!(), '[')) {
            // Slice
            if self.lexer.eat(Token::Op(ldef!(), ']')) {
                let inner = self.parse_type()?;
                return Ok(AstType::Slice(Box::new(inner)));
            }
            // Array
            let size = self.parse_expr()?;
            match size {
                Expr::Ident(ref token) => {
                    if token.is_sink_ident() {
                        self.expect(Token::Op(ldef!(), ']'))?;
                        let inner = self.parse_type()?;
                        Ok(AstType::Array(LazyExpr::default(), Box::new(inner), true))
                    } else {
                        self.expect(Token::Op(ldef!(), ']'))?;
                        let inner = self.parse_type()?;
                        Ok(AstType::Array(
                            LazyExpr::make_expr(size),
                            Box::new(inner),
                            false,
                        ))
                    }
                }
                Expr::Number(Token::Int(_, n)) => {
                    self.expect(Token::Op(ldef!(), ']'))?;
                    let inner = self.parse_type()?;
                    Ok(AstType::Array(
                        LazyExpr::make_constant(ConstExpr::Number(n)),
                        Box::new(inner),
                        false,
                    ))
                }
                _ => Err(error!(size.loc(), "Expected numerical constant here!")),
            }
        } else {
            let typ = match self.lexer.next() {
                Token::U64(_) => AstType::Base(Type::U64),
                Token::U32(_) => AstType::Base(Type::U32),
                Token::U16(_) => AstType::Base(Type::U16),
                Token::U8(_) => AstType::Base(Type::U8),
                Token::S64(_) => AstType::Base(Type::S64),
                Token::S32(_) => AstType::Base(Type::S32),
                Token::S16(_) => AstType::Base(Type::S16),
                Token::S8(_) => AstType::Base(Type::S8),
                Token::Bool(_) => AstType::Base(Type::Bool),
                Token::Void(_) => AstType::Base(Type::Void),
                Token::Ident(_, text) => {
                    let mut combined: String = text;
                    while self.lexer.peek() == Token::WideOp(ldef!(), (':', ':')) {
                        let _ = self.lexer.next();
                        let ident = self.lexer.next();
                        if let Token::Ident(_, text) = ident {
                            combined.push_str(MODULE_SEPARATOR);
                            combined.push_str(&text);
                        } else {
                            return Err(error!(ident.loc(), "Expected identifier after `::`"));
                        }
                    }
                    AstType::Alias(combined)
                }
                Token::Eof => Err(error_orphan!("Expected type but got end-of-file"))?,
                t => Err(error!(t.loc(), "Expected type!"))?,
            };
            Ok(typ)
        }
    }

    pub fn parse_stmt_scope(&mut self) -> Result<Option<Stmt>> {
        if self.lexer.peek() != Token::Op(ldef!(), '{') {
            return Ok(None);
        }
        Ok(Some(Stmt::Scope(self.parse_stmts()?)))
    }

    /*
    <stmt.let> ::= 'let' ID '=' <expr> ';'
    */
    pub fn parse_stmt_let(&mut self) -> Result<Option<Stmt>> {
        if !self.lexer.eat(Token::Let(ldef!())) {
            return Ok(None);
        }

        let Expr::Ident(token) = self.parse_expr_ident()? else {
            unreachable!()
        };

        let mut typ = None;
        if self.lexer.eat(Token::Op(ldef!(), ':')) {
            typ = Some(self.parse_type()?);
        }

        if self.lexer.peek() == Token::WideOp(ldef!(), (':', '=')) {
            let _ = self.lexer.next();
            let expr = self.parse_expr()?;
            self.expect(Token::Op(ldef!(), ';'))?;
            Ok(Some(Stmt::Let(token, typ, expr, true)))
        } else {
            self.expect(Token::Op(ldef!(), '='))?;
            let expr = self.parse_expr()?;
            self.expect(Token::Op(ldef!(), ';'))?;

            Ok(Some(Stmt::Let(token, typ, expr, false)))
        }
    }

    /*
    <stmt.if> ::= 'if' <expr> 'then' <stmt> ';'
                 | 'if' <expr> '{' <stmts> '}'
    */
    pub fn parse_stmt_if(&mut self) -> Result<Option<Stmt>> {
        if !self.lexer.eat(Token::If(ldef!())) {
            return Ok(None);
        }

        let expr = self.parse_expr()?;

        if self.lexer.eat(Token::Then(ldef!())) {
            let stmt = self.parse_stmt()?;

            let else_block = if self.lexer.eat(Token::Else(ldef!())) {
                Some(Box::new(self.parse_stmt()?))
            } else {
                None
            };

            Ok(Some(Stmt::If(expr, Box::new(stmt), else_block)))
        } else {
            let stmts = self.parse_stmts()?;

            let else_block = if self.lexer.eat(Token::Else(ldef!())) {
                Some(Box::new(self.parse_stmt()?))
            } else {
                None
            };

            Ok(Some(Stmt::If(
                expr,
                Box::new(Stmt::Scope(stmts)),
                else_block,
            )))
        }
    }

    /*
    <stmt.while> ::= 'while' <expr> '{' <stmts> '}'
    */
    pub fn parse_stmt_while(&mut self) -> Result<Option<Stmt>> {
        if !self.lexer.eat(Token::While(ldef!())) {
            return Ok(None);
        }

        let expr = self.parse_expr()?;
        let stmts = self.parse_stmts()?;

        Ok(Some(Stmt::While(expr, Box::new(Stmt::Scope(stmts)))))
    }

    /*
    <stmt.break> ::= 'break' ';'
    */
    pub fn parse_stmt_break(&mut self) -> Result<Option<Stmt>> {
        if self.lexer.peek() != Token::Break(ldef!()) {
            return Ok(None);
        }
        let Token::Break(loc) = self.lexer.next() else {
            unreachable!()
        };
        self.expect(Token::Op(ldef!(), ';'))?;
        Ok(Some(Stmt::Break(loc)))
    }

    /*
    <stmt.continue> ::= 'continue' ';'
    */
    pub fn parse_stmt_continue(&mut self) -> Result<Option<Stmt>> {
        if self.lexer.peek() != Token::Continue(ldef!()) {
            return Ok(None);
        }
        let Token::Continue(loc) = self.lexer.next() else {
            unreachable!()
        };
        self.expect(Token::Op(ldef!(), ';'))?;
        Ok(Some(Stmt::Continue(loc)))
    }

    /*
    <stmt.return> ::= 'return' [<expr>] ';'
    */
    pub fn parse_stmt_return(&mut self) -> Result<Option<Stmt>> {
        if self.lexer.peek() != Token::Return(ldef!()) {
            return Ok(None);
        }
        let Token::Return(loc) = self.lexer.next() else {
            unreachable!()
        };

        let expr = if self.lexer.peek() != Token::Op(ldef!(), ';') {
            Some(self.parse_expr()?)
        } else {
            None
        };

        self.expect(Token::Op(ldef!(), ';'))?;
        Ok(Some(Stmt::Return(loc, expr, false, true)))
    }

    pub fn parse_stmt_defer(&mut self) -> Result<Option<Stmt>> {
        if self.lexer.peek() != Token::Defer(ldef!()) {
            return Ok(None);
        }
        let Token::Defer(loc) = self.lexer.next() else {
            unreachable!()
        };
        let stmt = self.parse_stmt()?;
        Ok(Some(Stmt::Defer(loc, Box::new(stmt))))
    }

    pub fn parse_stmt_expr(&mut self) -> Result<Option<Stmt>> {
        let expr = self.parse_expr()?;
        self.expect(Token::Op(ldef!(), ';'))?;
        Ok(Some(Stmt::Ex(expr)))
    }
}
