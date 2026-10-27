//! The error every EthLib operation returns on bad input.

use std::fmt;

/// EthLib rejected an input.
///
/// - The specification defines which inputs are invalid, such as a blob of the wrong length.
/// - The message comes from Lean, and names the check that failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    /// The reason Lean gave, in plain text.
    message: String,
}

impl Error {
    /// An error carrying the reason Lean gave.
    pub(crate) fn new(message: String) -> Self {
        Self { message }
    }

    /// The reason Lean gave for rejecting the input.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Error {}
