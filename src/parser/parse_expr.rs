use crate::lexer::{Lexer, Token, Location};
use crate::ast::*;

use crate::precedence::*;
use crate::Parser;
use crate::parser::Result;
use crate::errors::SyntaxError;

impl Parser {
    pub fn parse_expr(&mut self) -> Result<Expr> {
        let mut expr = self.parse_expr_bp(0)?;
        if self.lexer.peek() == Token::As(ldef!()) {
            let as_ = self.lexer.next();
            let typ = self.parse_type()?;
            expr = Expr::Cast(as_, Box::new(expr), typ);
        }
        Ok(expr)
    }

    // TODO: proper error reporting (-> Result<Option<Expr>>)
    pub fn parse_expr_funcall(&mut self) -> Option<Expr> {
        let path = self.parse_expr_path().ok()?;
        if let Token::Op(_, '(') = self.lexer.peek() {
            self.lexer.next();

            let mut args = Vec::new();
            while self.lexer.peek() != Token::Op(ldef!(), ')') {
                let arg = self.parse_expr().ok()?;
                if self.lexer.peek() != Token::Op(ldef!(), ')') {
                    self.expect(Token::Op(ldef!(), ',')).ok()?;
                }
                args.push(arg);
            }
            
            self.expect(Token::Op(ldef!(), ')')).ok()?;
            return Some(Expr::Call(Box::new(path), args));
        }
        Some(path)
    }

    pub fn parse_expr_func_params(&mut self) -> Result<Vec<Param>> {
        let mut params = Vec::new();
        
        while self.lexer.peek() != Token::Op(ldef!(), ')') {
            let Expr::Ident(token) = self.parse_expr_ident()? else { unreachable!() };
            self.expect(Token::Op(ldef!(), ':'))?;
            let typ = self.parse_type()?;

            if self.lexer.peek() != Token::Op(ldef!(), ')') {
                self.expect(Token::Op(ldef!(), ','))?;
            }
            
            params.push(Param(token, typ));
        }

        Ok(params)
    }

    pub fn parse_expr_term(&mut self) -> Result<Expr> {
        //todo!("Implement parsing function call term here (it may also support a path too, so make sure to have a match case in the gen.rs)");
        let expr = if let Some(call) = self.parse_expr_funcall() {
            call
        } else {
            let token = self.lexer.next();
            match token {
                Token::Ident(_, _) => Expr::Ident(token),
                Token::Int(_, _) => Expr::Number(token),
                Token::String(_, _) => Expr::String(token),
                Token::CString(_, _) => Expr::CString(token),
                Token::True(_) | Token::False(_) => Expr::Bool(token),
                Token::Null(loc) => Expr::Null(Token::Null(loc)),
                Token::WideOp(loc, ('.', '.')) => {
                    match self.lexer.peek() {
                        Token::Ident(_, _) | Token::Int(_, _) => {
                            let ((), r_bp) = prefix_binding_power(('.', '.').try_into()?)?;
                            let rhs = self.parse_expr_bp(r_bp);
                            Expr::UnOp(Token::WideOp(loc, ('.', '.')), ('.', '.').try_into()?, Box::new(rhs?), false)
                        },
                        _ => Expr::Range(Token::WideOp(loc, ('.', '.')), None, None),
                    }
                },

                Token::Op(_, '(') => {
                    let lhs = self.parse_expr_bp(0);
                    self.expect(Token::Op(ldef!(), ')'))?;
                    lhs?
                },
                Token::Op(loc, '{') => {
                    let mut exprs = Vec::new();
                    while self.lexer.peek() != Token::Op(ldef!(), '}') {
                        let expr = self.parse_expr()?;
                        if self.lexer.peek() != Token::Op(ldef!(), '}') {
                            self.expect(Token::Op(ldef!(), ','))?;
                        }
                        exprs.push(expr);
                    }
                    self.expect(Token::Op(ldef!(), '}'))?;
                    Expr::InitList(Token::Op(loc, '{'), exprs)
                },
                Token::Op(loc, op) => {
                    let ((), r_bp) = prefix_binding_power(op.try_into()?)?;
                    let rhs = self.parse_expr_bp(r_bp);
                    Expr::UnOp(Token::Op(loc, op), op.try_into()?, Box::new(rhs?), false)
                },
                Token::Fn(loc) => {
                    self.expect(Token::Op(ldef!(), '('))?;
                    let params = self.parse_expr_func_params()?;
                    self.expect(Token::Op(ldef!(), ')'))?;

                    let return_type = if self.lexer.eat(Token::WideOp(ldef!(), ('-', '>'))) {
                        Some(self.parse_type()?)
                    } else { None };

                    let mut attrs = Vec::new();
                    while let Some(attr) = self.parse_attribute()? {
                        attrs.push(attr);
                    }

                    if self.lexer.peek() == Token::Op(ldef!(), ';') {
                        self.lexer.next();
                        Expr::FuncDecl(Token::Fn(loc), params, return_type, attrs)
                    } else {
                        if self.lexer.peek() != Token::Op(ldef!(), '{') {
                            return Err(error!(loc, "Missing function body"));
                        }
                        let stmts = self.parse_stmts()?;
                        Expr::Func(Token::Fn(loc), params, return_type, stmts, false, attrs)
                    }
                },
                Token::Eof => Err(error_orphan!("Could not parse expr term from end-of-file"))?,
                t => Err(error!(t.loc(), "Could not parse expr term from {t:?}"))?,
            }
        };
        Ok(expr)
    }
    
    pub fn parse_expr_bp(&mut self, min_bp: u8) -> Result<Expr> { 
        // These are term expressions i.e. primary expressions
        let mut lhs = self.parse_expr_term()?;       
        loop {
            // TODO: the termination condition could potentially not be sufficient in the future
            // This is 
            let op = match self.lexer.peek() {
                Token::Eof => break,
                Token::Op(_, op) => {
                    let conversion = TryInto::<Op>::try_into(op);
                    if conversion.is_err() { break }
                    conversion.unwrap()
                },
                Token::WideOp(_, op) => {
                    let conversion = TryInto::<Op>::try_into(op);
                    if conversion.is_err() { break }
                    conversion.unwrap()
                },
                t => break,
            };
            
            // Postfix
            if let Some((l_bp, ())) = postfix_binding_power(op.clone()) {
                if l_bp < min_bp { 
                    break;
                }
                let optok = self.lexer.next();
                
                lhs = if op == Op::Arr {
                    let rhs = self.parse_expr_bp(0);
                    assert_eq!(self.lexer.next(), Token::Op(ldef!(), ']'));
                    match rhs? {
                        Expr::BinOp(t, Op::Range, box_lhs, box_rhs) => {
                            let range = Expr::Range(t, Some(box_lhs), Some(box_rhs));
                            Expr::BinOp(optok, op, Box::new(lhs), Box::new(range))
                        },
                        Expr::UnOp(t, Op::Range, box_expr, postfix) => {
                            let range = if postfix {
                                Expr::Range(t, Some(box_expr), None)
                            } else {
                                Expr::Range(t, None, Some(box_expr))
                            };
                            Expr::BinOp(optok, op, Box::new(lhs), Box::new(range))
                        },
                        rhs => Expr::BinOp(optok, op, Box::new(lhs), Box::new(rhs)),
                    }
                } else {
                    if op == Op::Range {
                        match self.lexer.peek() {
                            Token::Ident(_, _) | Token::Int(_, _) => {
                                let rhs = self.parse_expr_bp(0)?;
                                Expr::BinOp(optok, op, Box::new(lhs), Box::new(rhs))
                            },
                            _ =>  Expr::UnOp(optok, op, Box::new(lhs), true),
                        }
                    } else {
                        Expr::UnOp(optok, op, Box::new(lhs), true)
                    }
                };
                
                continue;
            }
            
            if let Some((l_bp, r_bp)) = infix_binding_power(op.clone()) {
                if l_bp < min_bp { 
                    break;
                }
                
                let optok = self.lexer.next();
                let rhs = self.parse_expr_bp(r_bp);
                
                lhs = Expr::BinOp(optok, op, Box::new(lhs), Box::new(rhs?));
                continue;
            }
            
            break;
        }
        
        Ok(lhs)
    }
    
    fn try_parse_range() -> Result<Option<Expr>> {
        todo!()
    }
    
}
