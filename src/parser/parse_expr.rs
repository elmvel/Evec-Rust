use crate::lexer::{Lexer, Token, Location};
use crate::ast::*;

use crate::precedence::*;
use crate::Parser;
use crate::parser::Result;
use crate::errors::SyntaxError;

impl Parser {
    pub fn parse_expr(&mut self) -> Result<Expr> {
        self.parse_expr_bp(0) 
    }

    pub fn parse_expr_funcall(&mut self) -> Option<Expr> {
        let path = self.parse_expr_path().ok()?;
        if let Token::Op(_, '(') = self.lexer.peek() {
            self.lexer.next();
            // TODO: handle arguments
            self.expect(Token::Op(ldef!(), ')'));
            return Some(Expr::Call(Box::new(path)));
        }
        Some(path)
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
                Token::True(_) | Token::False(_) => Expr::Bool(token),
                Token::Op(_, '(') => {
                    let lhs = self.parse_expr_bp(0);
                    self.expect(Token::Op(ldef!(), ')'))?;
                    lhs?
                },
                Token::Op(_, op) => {
                    let ((), r_bp) = prefix_binding_power(op.try_into()?)?;
                    let rhs = self.parse_expr_bp(r_bp);
                    Expr::UnOp(op.try_into()?, Box::new(rhs?))
                },
                Token::Fn(loc) => {
                    self.expect(Token::Op(ldef!(), '('))?;
                    // TODO: params
                    self.expect(Token::Op(ldef!(), ')'))?;
                    // TODO: return type

                    if self.lexer.peek() != Token::Op(ldef!(), '{') {
                        return Err(error!(loc, "Missing function body"));
                    }
                    let stmts = self.parse_stmts()?;
                    Expr::Func(stmts)
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
                self.lexer.next();
                
                lhs = if op == Op::Arr {
                    let rhs = self.parse_expr_bp(0);
                    assert_eq!(self.lexer.next(), Token::Op(ldef!(), ']'));
                    Expr::BinOp(op, Box::new(lhs), Box::new(rhs?))
                } else {
                    Expr::UnOp(op, Box::new(lhs))
                };
                
                continue;
            }
            
            if let Some((l_bp, r_bp)) = infix_binding_power(op.clone()) {
                if l_bp < min_bp { 
                    break;
                }
                
                self.lexer.next();
                let rhs = self.parse_expr_bp(r_bp);
                
                lhs = Expr::BinOp(op, Box::new(lhs), Box::new(rhs?));
                continue;
            }
            
            break;
        }
        
        Ok(lhs)
    }
    
}
