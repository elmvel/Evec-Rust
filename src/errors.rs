use std::fmt;
use crate::lexer::Location;

#[derive(Debug)]
pub struct SyntaxError {
    pub location: Option<Location>,
    pub message: String,
}

impl SyntaxError {
    pub fn new(location: Option<Location>, message: String) -> Self {
        SyntaxError {
            location, message
        }
    }
}

// impl Into<SyntaxError> for &str {
//     fn into(self) -> SyntaxError {
//         SyntaxError::new(self.to_string())
//     }
// }
// 
// impl Into<SyntaxError> for String {
//     fn into(self) -> SyntaxError {
//         SyntaxError::new(self)
//     }
// }

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.location {
            Some(loc) => write!(f, "{} error: {}", loc, self.message),
            None => write!(f, "error: {}", self.message),
        }
    }
}
