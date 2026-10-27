//! `compute_kzg_proof`: prove the value of a blob's polynomial at one point.

use ethlib::Error;
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{
    self, FIELD_ELEMENT_COUNT, INVALID_BLOBS, INVALID_FIELD_ELEMENTS, VALID_FIELD_ELEMENTS, ValidBlob,
};
use crate::{Cases, Operation};

/// A blob, and the point at which to open its polynomial.
#[derive(Serialize)]
pub(crate) struct ComputeKzgProof {
    blob: Bytes,
    z: Bytes,
}

impl Operation for ComputeKzgProof {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "compute_kzg_proof";
    type Output = (Bytes, Bytes);

    fn run(&self) -> Result<(Bytes, Bytes), Error> {
        // Shared with the verification cases, which check these proofs.
        fixtures::compute_kzg_proof(&self.blob, &self.z)
    }

    /// Every well-formed blob at every well-formed point, then each malformed input alone.
    fn cases(cases: &mut Cases<'_, Self>) {
        // 7 blobs x 6 points.
        for blob in ValidBlob::all() {
            for (z, point) in VALID_FIELD_ELEMENTS.iter().enumerate().take(FIELD_ELEMENT_COUNT) {
                cases.valid(format!("case_valid_blob_{}_{z}", blob.index()), move || Self {
                    blob: blob.bytes(),
                    z: point.into(),
                });
            }
        }

        // A malformed blob, at the point zero.
        for (i, blob) in INVALID_BLOBS.iter().enumerate() {
            cases.invalid(format!("case_invalid_blob_{i}"), || Self {
                blob: blob.into(),
                z: VALID_FIELD_ELEMENTS[0].into(),
            });
        }

        // A point that is not a field element, on a well-formed blob.
        for (i, z) in INVALID_FIELD_ELEMENTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_z_{i}"), || Self { blob: ValidBlob::at(4).bytes(), z: z.into() });
        }
    }
}
