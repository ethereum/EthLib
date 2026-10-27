//! `compute_cells`: the cells of the extended blob, without proofs.

use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{INVALID_BLOBS, ValidBlob};
use crate::{Cases, Operation};

/// The blob to extend.
#[derive(Serialize)]
pub(crate) struct ComputeCells {
    blob: Bytes,
}

impl Operation for ComputeCells {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "compute_cells";
    type Output = Vec<Bytes>;

    fn run(&self) -> Result<Vec<Bytes>, Error> {
        kzg::compute_cells(&self.blob).map(|cells| cells.into_iter().map(Bytes).collect())
    }

    /// The cells of every well-formed blob, and a rejection for every malformed one.
    fn cases(cases: &mut Cases<'_, Self>) {
        for blob in ValidBlob::all() {
            cases.valid(format!("case_valid_{}", blob.index()), move || Self { blob: blob.bytes() });
        }
        // These names carry no `case_`, unlike the rest of the suite.
        for (i, blob) in INVALID_BLOBS.iter().enumerate() {
            cases.invalid(format!("invalid_blob_{i}"), || Self { blob: blob.into() });
        }
    }
}
