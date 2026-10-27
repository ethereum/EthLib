//! `compute_cells_and_kzg_proofs`: the cells of the extended blob, each with its proof.

use ethlib::Error;
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{self, CellsAndProofs, INVALID_BLOBS, ValidBlob};
use crate::{Cases, Operation};

/// The blob to extend.
#[derive(Serialize)]
pub(crate) struct ComputeCellsAndKzgProofs {
    blob: Bytes,
}

impl Operation for ComputeCellsAndKzgProofs {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "compute_cells_and_kzg_proofs";
    type Output = CellsAndProofs;

    fn run(&self) -> Result<CellsAndProofs, Error> {
        // Shared with every cell case, which builds on these cells and proofs.
        fixtures::compute_cells_and_kzg_proofs(&self.blob)
    }

    /// The cells and proofs of every well-formed blob, and a rejection for every malformed one.
    fn cases(cases: &mut Cases<'_, Self>) {
        for blob in ValidBlob::all() {
            cases.valid(format!("case_valid_{}", blob.index()), move || Self { blob: blob.bytes() });
        }
        for (i, blob) in INVALID_BLOBS.iter().enumerate() {
            cases.invalid(format!("case_invalid_blob_{i}"), || Self { blob: blob.into() });
        }
    }
}
