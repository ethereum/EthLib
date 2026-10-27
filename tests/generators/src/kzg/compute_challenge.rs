//! `compute_challenge`: the Fiat-Shamir challenge of a blob and a commitment.

use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{G1_POINT_AT_INFINITY, ValidBlob};
use crate::{Cases, Operation};

/// A blob and a commitment, which need not match.
#[derive(Serialize)]
pub(crate) struct ComputeChallenge {
    blob: Bytes,
    commitment: Bytes,
}

impl Operation for ComputeChallenge {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "compute_challenge";
    type Output = Bytes;

    fn run(&self) -> Result<Bytes, Error> {
        kzg::compute_challenge(&self.blob, &self.commitment).map(Bytes)
    }

    /// The challenge hashes its inputs, so it is defined for any well-formed pair.
    fn cases(cases: &mut Cases<'_, Self>) {
        for blob in ValidBlob::all() {
            cases.valid(format!("case_valid_{}", blob.index()), move || Self {
                blob: blob.bytes(),
                commitment: blob.commitment(),
            });
        }

        // Blob 3 with the commitment to blob 4: nothing checks that they match.
        cases.valid("case_mismatched_commitment", || Self {
            blob: ValidBlob::at(3).bytes(),
            commitment: ValidBlob::at(4).commitment(),
        });

        // The identity point is a valid commitment encoding.
        cases.valid("case_commitment_at_infinity", || Self {
            blob: ValidBlob::at(4).bytes(),
            commitment: Bytes::from(*G1_POINT_AT_INFINITY),
        });
    }
}
