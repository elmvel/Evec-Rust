use std::fmt;

#[derive(Debug)]
pub struct SyntaxError {
    pub message: String,
}

impl SyntaxError {
    fn new(message: String) -> Self {
        SyntaxError {
            message
        }
    }
}

impl Into<SyntaxError> for &str {
    fn into(self) -> SyntaxError {
        SyntaxError::new(self.to_string())
    }
}

impl Into<SyntaxError> for String {
    fn into(self) -> SyntaxError {
        SyntaxError::new(self)
    }
}

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}
