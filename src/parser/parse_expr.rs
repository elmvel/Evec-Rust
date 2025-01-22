use crate::lexer::{Lexer, Token};
use crate::ast::*;

use crate::precedence::*;
use crate::Parser;
use crate::parser::Result;

impl Parser {
    pub fn parse_expr(&mut self) -> Result<Expr> {
        self.parse_expr_bp(0) 
    }

    pub fn parse_expr_term(&mut self) -> Result<Expr> {
        let token = self.lexer.next();
        let expr = match token {
            Token::Ident(_) => Expr::Ident(token),
            Token::Int(_) => Expr::Number(token),
            Token::Op('(') => {
                let lhs = self.parse_expr_bp(0);
                self.expect(Token::Op(')'))?;
                lhs?
            },
            Token::Op(op) => {
                let ((), r_bp) = prefix_binding_power(op);
                let rhs = self.parse_expr_bp(r_bp);
                Expr::UnOp(op, Box::new(rhs?))
            },
            Token::Fn => {
                self.expect(Token::Op('('))?;
                // TODO: params
                self.expect(Token::Op(')'))?;
                // TODO: return type

                if self.lexer.peek() != Token::Op('{') {
                    return Err("Missing function body".into());
                }
                let stmts = self.parse_stmts()?;
                Expr::Func(stmts)
            },
            t => Err(format!("Could not parse expr term from {t:?}").into())?,
        };
        Ok(expr)
    }
    
    pub fn parse_expr_bp(&mut self, min_bp: u8) -> Result<Expr> { 
        // These are term expressions i.e. primary expressions
        let mut lhs = self.parse_expr_term()?;       
        loop {
            let op = match self.lexer.peek() {
                Token::Eof => break,
                Token::Op(op) => op,
                t => panic!("bad token: {:?}", t),
            };
            
            // Postfix
            if let Some((l_bp, ())) = postfix_binding_power(op) {
                if l_bp < min_bp { 
                    break;
                }
                self.lexer.next();
                
                lhs = if op == '[' {
                    let rhs = self.parse_expr_bp(0);
                    assert_eq!(self.lexer.next(), Token::Op(']'));
                    Expr::BinOp(op, Box::new(lhs), Box::new(rhs?))
                } else {
                    Expr::UnOp(op, Box::new(lhs))
                };
                
                continue;
            }
            
            if let Some((l_bp, r_bp)) = infix_binding_power(op) {
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
