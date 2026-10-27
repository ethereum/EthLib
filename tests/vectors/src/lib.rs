//! The EthLib test-vector format, and the check that pins the vectors.
//!
//! A vector pins one input to one output, as a YAML file on disk:
//!
//! ```text
//!     tests/cryptography/<kind>/<handler>/<case>/data.yaml
//!
//!     input:  ...      what the operation receives
//!     output: ...      what it returns, or null when it rejects the input
//! ```
//!
//! The layout and the encoding follow the consensus-specs reference tests.
//! Client teams run those tests unchanged against these files.

use std::path::{Path, PathBuf};

use serde::Serialize;

pub mod pins;

mod bytes;
mod yaml;

pub use bytes::Bytes;
pub use yaml::to_yaml;

/// The name of the file that holds one case.
pub const CASE_FILE: &str = "data.yaml";

/// The directory that holds every cryptography vector.
#[must_use]
pub fn root() -> PathBuf {
    // This crate lives in `tests/vectors`, next to `tests/cryptography`.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../cryptography")
}

/// The text of one case file.
///
/// The output is `None` when the operation must reject the input, and is then written as null.
///
/// # Panics
///
/// Panics on a value serde cannot represent as JSON, such as a map with non-string keys.
#[must_use]
pub fn encode<I: Serialize, O: Serialize>(input: &I, output: Option<&O>) -> String {
    /// The two fields of a case file, in file order.
    #[derive(Serialize)]
    struct Document<'a, I, O> {
        input: &'a I,
        output: Option<&'a O>,
    }
    let document = serde_json::to_value(Document { input, output }).expect("a vector is plain data");
    to_yaml(&document)
}
