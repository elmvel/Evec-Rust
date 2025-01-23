macro_rules! error {
    ($loc:expr, $($l:tt),+) => {
        SyntaxError::new(Some($loc), format!($($l),+))
    }
}

// It's an orphan because there are no location present
macro_rules! error_orphan {
    ($($l:tt),+) => {
        SyntaxError::new(None, format!($($l),+))
    }
}
