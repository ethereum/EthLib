//! `compute_blob_kzg_proof`: prove a blob against its commitment.

use ethlib::Error;
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{self, G1, INVALID_BLOBS, INVALID_G1_POINTS, ValidBlob};
use crate::{Cases, Operation};

/// A blob and its commitment.
#[derive(Serialize)]
pub(crate) struct ComputeBlobKzgProof {
    blob: Bytes,
    commitment: Bytes,
}

impl Operation for ComputeBlobKzgProof {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "compute_blob_kzg_proof";
    type Output = Bytes;

    fn run(&self) -> Result<Bytes, Error> {
        fixtures::compute_blob_kzg_proof(&self.blob, &self.commitment)
    }

    /// A proof for every well-formed blob, then each malformed input alone.
    fn cases(cases: &mut Cases<'_, Self>) {
        for blob in ValidBlob::all() {
            cases.valid(format!("case_valid_blob_{}", blob.index()), move || Self {
                blob: blob.bytes(),
                commitment: blob.commitment(),
            });
        }

        // A malformed blob, with the generator standing in as a well-formed commitment.
        for (i, blob) in INVALID_BLOBS.iter().enumerate() {
            cases
                .invalid(format!("case_invalid_blob_{i}"), || Self { blob: blob.into(), commitment: Bytes::from(*G1) });
        }

        // A malformed commitment, with a well-formed blob.
        for (i, commitment) in INVALID_G1_POINTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_commitment_{i}"), || Self {
                blob: ValidBlob::at(1).bytes(),
                commitment: commitment.into(),
            });
        }
    }
}
