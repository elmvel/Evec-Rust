use std::iter;
use core::iter::from_fn;
use std::fmt;

// https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

#[derive(Debug)]
struct SyntaxError {
    message: String,
}

impl SyntaxError {
    fn new(message: String) -> Self {
        SyntaxError {
            message
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Int(i64),
    Op(char),
    Eof,
}

struct Lexer {
    tokens: Vec<Token>,
}

impl Lexer {
    fn new(input: &str) -> Result<Self, SyntaxError> {
        let mut tokens: Vec<Token> = Vec::new();
        let mut iter = input.chars().peekable();
        
        while let Some(ch) = iter.next() {
            match ch {
                ch if ch.is_whitespace() => continue,
                '+' | '-' | '*' | '/' | '.' | '!' | '(' | ')'
                    | '[' | ']' => tokens.push(Token::Op(ch)),
                'a'..='z' | 'A'..='Z' | '_' => {
                    let n: String = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_alphanumeric())))
                        .collect::<String>();

                    tokens.push(Token::Ident(n));  
                    //tokens.push(Token::Atom(ch));  
                },
                '1'..='9' => {
                    let n: i64 = iter::once(ch)
                        .chain(from_fn(|| iter.by_ref().next_if(|s| s.is_ascii_digit())))
                        .collect::<String>()
                        .parse()
                        .unwrap();

                    tokens.push(Token::Int(n));  
                },
                _ => return Err(SyntaxError::new(format!("Unknown character `{ch}`"))),
            }
        }
        
        tokens.reverse();
        
        Ok(Self {
            tokens
        })
    }

    fn next(&mut self) -> Token {
        self.tokens.pop().unwrap_or(Token::Eof)
    }

    fn peek(&mut self) -> Token {
        self.tokens.last().cloned().unwrap_or(Token::Eof)
    }
}

enum S {
    Atom(String),
    Cons(char, Vec<S>),
}

impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            S::Atom(i) => write!(f, "{}", i),
            S::Cons(head, rest) => {
                write!(f, "({}", head)?;
                for s in rest {
                    write!(f, " {}", s)?
                }
                write!(f, ")")
            }
        }
    }
}

fn expr(input: &str) -> S {
    let mut lexer = Lexer::new(input).map_err(|e| {
        eprintln!("ERROR: {}", e.message);
    }).unwrap();
    expr_bp(&mut lexer, 0) 
}

fn expr_bp(lexer: &mut Lexer, min_bp: u8) -> S { 
    // These are term expressions i.e. primary expressions
    let mut lhs = match lexer.next() {
        Token::Ident(it) => S::Atom(it),
        Token::Int(i) => S::Atom(i.to_string()),
        Token::Op('(') => {
            let lhs = expr_bp(lexer, 0);
            assert_eq!(lexer.next(), Token::Op(')'));
            lhs
        },
        Token::Op(op) => {
            let ((), r_bp) = prefix_binding_power(op);
            let rhs = expr_bp(lexer, r_bp);
            S::Cons(op, vec![rhs]) 
        },
        t => panic!("bad token: {:?}", t),
    };

    loop {
        let op = match lexer.peek() {
            Token::Eof => break,
            Token::Op(op) => op,
            t => panic!("bad token: {:?}", t),
        };
        
        // Postfix
        if let Some((l_bp, ())) = postfix_binding_power(op) {
            if l_bp < min_bp { 
                break;
            }
            lexer.next();
            
            lhs = if op == '[' {
                let rhs = expr_bp(lexer, 0);
                assert_eq!(lexer.next(), Token::Op(']'));
                S::Cons(op, vec![lhs, rhs])
            } else {
                S::Cons(op, vec![lhs])
            };
            
            continue;
        }

        if let Some((l_bp, r_bp)) = infix_binding_power(op) {
            if l_bp < min_bp { 
                break;
            }

            lexer.next();
            let rhs = expr_bp(lexer, r_bp);
            
            lhs = S::Cons(op, vec![lhs, rhs]);
            continue;
        }

        break;
    }

    lhs
}

// The general rule is that we use an odd priority as base, and bump it by one for associativity, if the operator is binary

fn infix_binding_power(op: char) -> Option<(u8, u8)> {
    let res = match op {
        '+' | '-' => (1, 2),
        '*' | '/' => (3, 4),
        '.' => (10, 9),
        _ => return None,
    };
    Some(res)
}

fn prefix_binding_power(op: char) -> ((), u8) {
    match op {
        '+' | '-' => ((), 5),
        _ => panic!("bad op: {:?}", op),
    }
}

fn postfix_binding_power(op: char) -> Option<(u8, ())> {
    let res = match op {
        '!' | '[' => (7, ()),
        _ => return None,
    };
    Some(res)
}

fn main() {
    let s = expr("arr[idx]");
    println!("sexpr: {s}");
}

#[test]
fn tests() {
    let s = expr("a");
    assert_eq!(s.to_string(), "a");

    let s = expr("69");
    assert_eq!(s.to_string(), "69");

    let s = expr("1 + 2 * 3");
    assert_eq!(s.to_string(), "(+ 1 (* 2 3))");

    let s = expr("f . g . h");
    assert_eq!(s.to_string(), "(. f (. g h))");

    let s = expr("-fov");
    assert_eq!(s.to_string(), "(- fov)");

    let s = expr("52!");
    assert_eq!(s.to_string(), "(! 52)");

    let s = expr("((((a))))");
    assert_eq!(s.to_string(), "a");

    let s = expr("arr[idx]");
    assert_eq!(s.to_string(), "([ arr idx)");
}
