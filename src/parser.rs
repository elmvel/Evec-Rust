use std::collections::HashMap;

use crate::ast::*;
use crate::lexer::{Lexer, Location, Token};

use crate::const_eval::LazyExpr;
use crate::errors::SyntaxError;
use crate::gen::FunctionDecl;
use crate::precedence::*;

mod parse_expr;
mod parse_stmt;

macro_rules! insert_func_with_attributes {
    ($map:expr, $name:expr, $params:expr, $ret_type:expr, $attrs:expr) => {
        let mut extern_name = None;
        for attr in $attrs {
            match attr {
                Attribute::Extern(expr) => {
                    let Expr::String(Token::String(_, text)) = expr else {
                        unreachable!()
                    };
                    extern_name = Some(text);
                }
                _ => return Err(error_orphan!("Unsupported function attribute `{attr:?}`")),
            }
        }
        $map.insert(
            $name.clone(),
            FunctionDecl::new($params, $ret_type, $name, extern_name),
        );
    };
}

pub type Result<T> = std::result::Result<T, SyntaxError>;

pub struct ParseModule {
    pub name: Expr,
    pub file_stem: String,
    pub globals: Vec<Global>,
    pub function_map: HashMap<String, FunctionDecl>,
    pub type_alias_map: HashMap<String, AstType>,
}

pub struct Parser {
    lexer: Lexer,
    function_map: HashMap<String, FunctionDecl>,
    type_alias_map: HashMap<String, AstType>,
}

impl Parser {
    pub fn from(lexer: Lexer) -> Self {
        Self {
            lexer,
            function_map: HashMap::new(),
            type_alias_map: HashMap::new(),
        }
    }

    fn expect(&mut self, token: Token) -> Result<()> {
        let next = self.lexer.next();
        if next != token {
            return match next {
                Token::Eof => Err(error_orphan!(
                    "Expected `{token:?}`, got end-of-file instead!"
                )),
                t => Err(error!(
                    t.loc(),
                    "Expected `{token:?}`, got `{t:?}` instead!"
                )),
            };
        }
        Ok(())
    }

    fn eof(&mut self) -> bool {
        self.lexer.peek() == Token::Eof
    }

    fn default_type_aliases(&mut self) {
        self.type_alias_map.insert(
            "str".into(),
            AstType::Slice(Box::new(AstType::Base(Type::U8))),
        );
        let u: AstType = AstType::Base(Type::U8);
        self.type_alias_map
            .insert("cstr".into(), AstType::Ptr(Box::new(u)));
        let usz: AstType = AstType::Base(Type::U64);
        self.type_alias_map.insert("usize".into(), usz);
    }

    pub fn parse(&mut self, file_stem: String) -> Result<ParseModule> {
        self.default_type_aliases();
        let Global::DeclModule(name) = self.parse_module_decl()? else {
            unreachable!()
        };
        let mut globals = Vec::new();

        while !self.eof() {
            if let Some(import) = self.parse_import()? {
                globals.push(import);
            } else {
                if let Some(_) = self.parse_type_alias()? {
                    continue;
                } else {
                    let global = self.parse_global()?;
                    globals.push(global);
                }
            }
        }

        Ok(ParseModule {
            name,
            file_stem,
            globals,
            function_map: self.function_map.clone(),
            type_alias_map: self.type_alias_map.clone(),
        })
    }

    pub fn parse_expr_string(&mut self) -> Result<Expr> {
        let token = self.lexer.peek();
        match token {
            Token::String(_, _) => {
                self.lexer.next();
                Ok(Expr::String(token))
            }
            Token::Eof => Err(error_orphan!("No string present")),
            t => Err(error!(t.loc(), "No string present")),
        }
    }

    pub fn parse_expr_ident(&mut self) -> Result<Expr> {
        let token = self.lexer.peek();
        match token {
            Token::Ident(_, _) => {
                self.lexer.next();
                Ok(Expr::Ident(token))
            }
            Token::Eof => Err(error_orphan!("No identifier present")),
            t => Err(error!(t.loc(), "No identifier present")),
        }
    }

    pub fn parse_expr_path(&mut self) -> Result<Expr> {
        let mut path = self.parse_expr_ident()?;
        while let Token::WideOp(_, (':', ':')) = self.lexer.peek() {
            self.lexer.next();

            let Expr::Ident(token) = path else {
                unreachable!()
            };
            let rhs = self.parse_expr_path()?;
            path = Expr::Path(token, Box::new(rhs))
        }
        Ok(path)
    }

    /*
    <global.mod_decl> ::= 'module' <expr.path> ';'
    */
    pub fn parse_module_decl(&mut self) -> Result<Global> {
        if !self.lexer.eat(Token::Module(ldef!())) {
            return match self.lexer.peek() {
                Token::Eof => Err(error_orphan!(
                    "Module header is required! Got empty file instead."
                )),
                t => Err(error!(t.loc(), "Module header is required!")),
            };
        }

        let decl = Global::DeclModule(self.parse_expr_path()?);
        self.expect(Token::Op(ldef!(), ';'))?;
        Ok(decl)
    }

    /*
    <global.import> ::= 'import' <expr.path> ';'
    */
    pub fn parse_import(&mut self) -> Result<Option<Global>> {
        if !self.lexer.eat(Token::Import(ldef!())) {
            return Ok(None);
        }

        let import = Global::Import(self.parse_expr_path()?);
        self.expect(Token::Op(ldef!(), ';'))?;
        Ok(Some(import))
    }

    /*
    <global.typealias> ::= 'type' ID '=' <type> ';'
    */
    pub fn parse_type_alias(&mut self) -> Result<Option<()>> {
        if !self.lexer.eat(Token::Type(ldef!())) {
            return Ok(None);
        }

        let Expr::Ident(Token::Ident(loc, text)) = self.parse_expr_ident()? else {
            unreachable!()
        };
        self.expect(Token::Op(ldef!(), '='))?;
        let typ = self.parse_type()?;
        self.expect(Token::Op(ldef!(), ';'))?;

        if self.type_alias_map.get(&text).is_some() {
            return Err(error!(loc, "Type alias `{text}` already exists!"));
        }

        self.type_alias_map.insert(text, typ);

        Ok(Some(()))
    }

    /*
    <global> ::= ID '::' <expr>
    */
    pub fn parse_global(&mut self) -> Result<Global> {
        let Expr::Ident(token) = self.parse_expr_ident()? else {
            unreachable!()
        };
        self.expect(Token::WideOp(ldef!(), (':', '=')))?;
        let expr = self.parse_expr()?;

        if let Expr::Func(fn_, params, ret_type, stmts, returns, attrs) = expr {
            let Token::Ident(_, text) = token.clone() else {
                unreachable!()
            };
            insert_func_with_attributes!(
                (self.function_map),
                text,
                (params.clone()),
                (ret_type.clone()),
                (attrs.clone())
            );
            Ok(Global::Decl(
                token,
                Expr::Func(fn_, params, ret_type, stmts, returns, attrs),
            ))
        } else {
            if let Expr::FuncDecl(fn_, params, ret_type, attrs) = expr {
                let Token::Ident(_, text) = token.clone() else {
                    unreachable!()
                };
                insert_func_with_attributes!(
                    (self.function_map),
                    text,
                    (params.clone()),
                    (ret_type.clone()),
                    (attrs.clone())
                );
                Ok(Global::Decl(
                    token,
                    Expr::FuncDecl(fn_, params, ret_type, attrs),
                ))
            } else {
                Ok(Global::Decl(token, expr))
            }
        }
    }

    /*
    #extern("symbol")
    */
    pub fn parse_attribute(&mut self) -> Result<Option<Attribute>> {
        if std::mem::discriminant(&Token::Attribute(ldef!(), "".into()))
            != std::mem::discriminant(&self.lexer.peek())
        {
            return Ok(None);
        }
        let Token::Attribute(loc, name) = self.lexer.next() else {
            unreachable!()
        };
        match &name[..] {
            "#extern" => {
                self.expect(Token::Op(ldef!(), '('))?;
                let symbol = self.parse_expr_string()?;
                self.expect(Token::Op(ldef!(), ')'))?;
                Ok(Some(Attribute::Extern(symbol)))
            }
            _ => Err(error!(loc, "Unknown attribute `{name}`")),
        }
    }
}
