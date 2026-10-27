//! `blob_to_kzg_commitment`: commit to a blob.

use ethlib::Error;
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{self, INVALID_BLOBS, ValidBlob};
use crate::{Cases, Operation};

/// The blob to commit to.
#[derive(Serialize)]
pub(crate) struct BlobToKzgCommitment {
    blob: Bytes,
}

impl Operation for BlobToKzgCommitment {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "blob_to_kzg_commitment";
    type Output = Bytes;

    fn run(&self) -> Result<Bytes, Error> {
        fixtures::blob_to_kzg_commitment(&self.blob)
    }

    /// Every well-formed blob commits, and every malformed one is rejected.
    fn cases(cases: &mut Cases<'_, Self>) {
        for blob in ValidBlob::all() {
            cases.valid(format!("case_valid_blob_{}", blob.index()), move || Self { blob: blob.bytes() });
        }
        for (i, blob) in INVALID_BLOBS.iter().enumerate() {
            cases.invalid(format!("case_invalid_blob_{i}"), || Self { blob: blob.into() });
        }
    }
}
