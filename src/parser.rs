use crate::lexer::{Lexer, Token};
use crate::ast::*;

use crate::precedence::*;
use crate::errors::SyntaxError;

mod parse_expr;
mod parse_stmt;

pub type Result<T> = std::result::Result<T, SyntaxError>;

pub struct ParseModule {
    pub name: Expr,
    pub globals: Vec<Global>,
}

pub struct Parser {
    lexer: Lexer,
}

// Welcome home :/
// Next step needed is to encapsulate the parse functions into the parser class,
// And then start parsing globals -> functions -> statements

// maybe create a wrapper for Expr for identifiers and use .into functions to go
// between types
impl Parser {
    pub fn from(lexer: Lexer) -> Self {
        Self { lexer }
    }

    fn expect(&mut self, token: Token) -> Result<()> {
        let next = self.lexer.next();
        if next != token {
            return Err(format!("Expected `{token:?}`, got `{next:?}` instead!").into());
        }
        Ok(())
    }

    fn eof(&mut self) -> bool {
        self.lexer.peek() == Token::Eof
    }

    pub fn parse(&mut self) -> Result<ParseModule> {
        let Global::DeclModule(name) = self.parse_module_decl()? else { unreachable!() };
        let mut globals = Vec::new();
        
        while !self.eof() {
            let global = self.parse_global()?;
            globals.push(global);
        }

        Ok(ParseModule{name, globals})
    }

    pub fn parse_expr_ident(&mut self) -> Result<Expr> {
        let token = self.lexer.peek();
        match token {
            Token::Ident(_) => {
                self.lexer.next();
                Ok(Expr::Ident(token))
            },
            _ => Err("No identifier present".into())
        }
    }
    
    pub fn parse_expr_path(&mut self) -> Result<Expr> {
        let mut path = self.parse_expr_ident()?;
        while let Token::Op('D') = self.lexer.peek() {
            self.lexer.next();

            let Expr::Ident(token) = path else { unreachable!() };
            let rhs = self.parse_expr_path()?;
            path = Expr::Path(token, Box::new(rhs))
        }
        Ok(path)
    }

    /*
    <global.mod_decl> ::= 'module' <expr.path> ';'
    */
    pub fn parse_module_decl(&mut self) -> Result<Global> {
        if !self.lexer.eat(Token::Module) {
            return Err("Module header is required!".into());
        }

        let decl = Global::DeclModule(self.parse_expr_path()?);
        self.expect(Token::Op(';'))?;
        Ok(decl)
    }

    /*
    <global> ::= ID '::' <expr>
    */
    pub fn parse_global(&mut self) -> Result<Global> {
        let Expr::Ident(token) = self.parse_expr_ident()? else { unreachable!() };
        self.expect(Token::Op('D'))?;
        let expr = self.parse_expr()?;
        Ok(Global::Decl(token, expr))
    }
}
