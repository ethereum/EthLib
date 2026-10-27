//! The EthLib test-vector generators.
//!
//! Each handler is an operation: a typed input, a typed output, and the Lean definition that maps one to the other.
//! Its cases only declare inputs, and whether the specification accepts them.
//!
//! ```text
//!     case ──► input ──► ethlib (Lean) ──► outcome checked ──► data.yaml
//! ```
//!
//! The test suite in `tests/vectors.rs` runs every case and compares it with the committed file.

mod bls;
mod kzg;
mod memo;
mod operation;
mod python_random;

pub use operation::{Case, Cases, Operation};

/// Every case, in suite and then handler order.
#[must_use]
pub fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for collect in [bls::OPERATIONS.as_slice(), kzg::OPERATIONS.as_slice()].concat() {
        collect(&mut cases);
    }
    cases
}
