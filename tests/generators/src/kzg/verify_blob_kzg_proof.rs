//! `verify_blob_kzg_proof`: check that a commitment commits to a blob.

use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{G1, G1_POINT_AT_INFINITY, INVALID_BLOBS, INVALID_G1_POINTS, ValidBlob, add_generator};
use crate::{Cases, Operation};

/// A blob, a commitment, and a proof that the commitment is to the blob.
#[derive(Serialize)]
pub(crate) struct VerifyBlobKzgProof {
    blob: Bytes,
    commitment: Bytes,
    proof: Bytes,
}

impl VerifyBlobKzgProof {
    /// The honest commitment and proof for `blob`.
    fn honest(blob: ValidBlob) -> Self {
        Self { blob: blob.bytes(), commitment: blob.commitment(), proof: blob.blob_kzg_proof() }
    }
}

impl Operation for VerifyBlobKzgProof {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "verify_blob_kzg_proof";
    type Output = bool;

    fn run(&self) -> Result<bool, Error> {
        kzg::verify_blob_kzg_proof(&self.blob, &self.commitment, &self.proof)
    }

    /// Correct and incorrect proofs for every blob, then each malformed input alone.
    fn cases(cases: &mut Cases<'_, Self>) {
        for blob in ValidBlob::all() {
            let b = blob.index();
            cases.returns(format!("case_correct_proof_{b}"), true, move || Self::honest(blob));

            // Mutation: proof + G1, a valid point that proves nothing.
            cases.returns(format!("case_incorrect_proof_{b}"), false, move || {
                let mut input = Self::honest(blob);
                input.proof = add_generator(&input.proof);
                input
            });
        }

        // The identity point as the proof.
        //
        //     blob 2 : not constant, so the identity proves nothing
        //     p = 0  : the quotient is 0, so the identity is the honest proof
        //     p = 2  : likewise, for a constant polynomial
        let identity = |blob| Self { proof: Bytes::from(*G1_POINT_AT_INFINITY), ..Self::honest(blob) };
        cases.returns("case_incorrect_proof_point_at_infinity", false, move || identity(ValidBlob::RANDOM_VALID1));
        cases.returns("case_correct_proof_point_at_infinity_for_zero_poly", true, move || {
            identity(ValidBlob::ALL_ZEROS)
        });
        cases
            .returns("case_correct_proof_point_at_infinity_for_twos_poly", true, move || identity(ValidBlob::ALL_TWOS));

        // Each malformed input, with the generator standing in for the well-formed points.
        let input = |blob: Bytes, commitment: &[u8], proof: &[u8]| Self {
            blob,
            commitment: commitment.into(),
            proof: proof.into(),
        };
        for (i, blob) in INVALID_BLOBS.iter().enumerate() {
            cases.invalid(format!("case_invalid_blob_{i}"), move || input(blob.into(), &*G1, &*G1));
        }
        for (i, point) in INVALID_G1_POINTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_commitment_{i}"), move || input(ValidBlob::at(1).bytes(), point, &*G1));
        }
        for (i, point) in INVALID_G1_POINTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_proof_{i}"), move || input(ValidBlob::at(1).bytes(), &*G1, point));
        }
    }
}
