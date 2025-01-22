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
