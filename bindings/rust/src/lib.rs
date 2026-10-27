//! Rust bindings to EthLib, formally verified Ethereum primitives written in Lean.
//!
//! Each function calls the Lean definition through its C export.
//! The Lean runtime boots on the first call, from any thread.
//!
//! ```text
//!     Rust caller ──► ethlib::kzg ──► eth_kzg_* (C export) ──► Lean definition
//! ```
//!
//! Inputs pass to Lean unchanged.
//! A malformed input reaches the Lean boundary check and comes back as an error.
//!
//! # Examples
//!
//! ```no_run
//! let blob = vec![0u8; ethlib::kzg::constants().bytes_per_blob];
//! let commitment = ethlib::kzg::blob_to_kzg_commitment(&blob)?;
//! assert_eq!(commitment.len(), ethlib::kzg::constants().bytes_per_commitment);
//! # Ok::<(), ethlib::Error>(())
//! ```

pub mod bls;
pub mod kzg;

mod error;
mod lean;

pub use error::Error;
