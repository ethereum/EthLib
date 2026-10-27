//! `verify_kzg_proof`: check a claimed value of a committed polynomial at one point.

use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{
    FIELD_ELEMENT_COUNT, G1_POINT_AT_INFINITY, INVALID_FIELD_ELEMENTS, INVALID_G1_POINTS, VALID_FIELD_ELEMENTS,
    ValidBlob, add_generator,
};
use crate::{Cases, Operation};

/// The claim `p(z) = y` about the polynomial behind a commitment, and its proof.
#[derive(Serialize)]
pub(crate) struct VerifyKzgProof {
    commitment: Bytes,
    z: Bytes,
    y: Bytes,
    proof: Bytes,
}

impl VerifyKzgProof {
    /// The honest claim and proof for `blob` at the well-formed field element `z`.
    fn honest(blob: ValidBlob, z: usize) -> Self {
        let (proof, y) = blob.kzg_proof(z);
        Self { commitment: blob.commitment(), z: VALID_FIELD_ELEMENTS[z].into(), y, proof }
    }
}

impl Operation for VerifyKzgProof {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "verify_kzg_proof";
    type Output = bool;

    fn run(&self) -> Result<bool, Error> {
        kzg::verify_kzg_proof(&self.commitment, &self.z, &self.y, &self.proof)
    }

    /// Correct and incorrect proofs for every blob and point, then each malformed input alone.
    fn cases(cases: &mut Cases<'_, Self>) {
        for blob in ValidBlob::all() {
            let b = blob.index();
            for z in 0..FIELD_ELEMENT_COUNT {
                cases.returns(format!("case_correct_proof_{b}_{z}"), true, move || Self::honest(blob, z));

                // Mutation: proof + G1, a valid point that proves nothing.
                cases.returns(format!("case_incorrect_proof_{b}_{z}"), false, move || {
                    let mut input = Self::honest(blob, z);
                    input.proof = add_generator(&input.proof);
                    input
                });
            }
        }

        // The identity point as the proof.
        //
        //     blob 2 : not constant, so the identity proves nothing
        //     p = 0  : the quotient (p(X) - p(z)) / (X - z) is 0, whose commitment is the identity
        //     p = 2  : the quotient is 0 too, a constant minus its own value
        let identity = |blob, z| Self { proof: Bytes::from(*G1_POINT_AT_INFINITY), ..Self::honest(blob, z) };
        for z in 0..FIELD_ELEMENT_COUNT {
            cases.returns(format!("case_incorrect_proof_point_at_infinity_{z}"), false, move || {
                identity(ValidBlob::RANDOM_VALID1, z)
            });
            cases.returns(format!("case_correct_proof_point_at_infinity_for_zero_poly_{z}"), true, move || {
                identity(ValidBlob::ALL_ZEROS, z)
            });
            cases.returns(format!("case_correct_proof_point_at_infinity_for_twos_poly_{z}"), true, move || {
                identity(ValidBlob::ALL_TWOS, z)
            });
        }

        // Each malformed input, with every other input taken from an honest proof at z = 1.
        for (i, point) in INVALID_G1_POINTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_commitment_{i}"), || Self {
                commitment: point.into(),
                ..Self::honest(ValidBlob::at(2), 1)
            });
        }
        for (i, element) in INVALID_FIELD_ELEMENTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_z_{i}"), || Self {
                z: element.into(),
                ..Self::honest(ValidBlob::at(4), 1)
            });
        }
        for (i, element) in INVALID_FIELD_ELEMENTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_y_{i}"), || Self {
                y: element.into(),
                ..Self::honest(ValidBlob::at(4), 1)
            });
        }
        for (i, point) in INVALID_G1_POINTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_proof_{i}"), || Self {
                proof: point.into(),
                ..Self::honest(ValidBlob::at(2), 1)
            });
        }
    }
}
