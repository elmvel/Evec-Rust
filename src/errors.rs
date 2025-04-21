use crate::lexer::Location;
use std::fmt;

#[derive(Debug)]
pub struct SyntaxError {
    pub location: Option<Location>,
    pub message: String,
}

impl SyntaxError {
    pub fn new(location: Option<Location>, message: String) -> Self {
        SyntaxError { location, message }
    }
}

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.location {
            Some(loc) => write!(f, "{} error: {}", loc, self.message),
            None => write!(f, "error: {}", self.message),
        }
    }
}
