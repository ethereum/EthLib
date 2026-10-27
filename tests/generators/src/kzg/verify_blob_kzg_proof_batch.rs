//! `verify_blob_kzg_proof_batch`: check many blob proofs as one batch.

use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{G1_POINT_AT_INFINITY, INVALID_BLOBS, INVALID_G1_POINTS, ValidBlob, add_generator};
use crate::{Cases, Operation};

/// Three parallel lists: blobs, their commitments, and their proofs.
#[derive(Serialize)]
pub(crate) struct VerifyBlobKzgProofBatch {
    blobs: Vec<Bytes>,
    commitments: Vec<Bytes>,
    proofs: Vec<Bytes>,
}

/// A change applied to an honest batch.
type Mutation = fn(&mut VerifyBlobKzgProofBatch);

impl VerifyBlobKzgProofBatch {
    /// The honest batch of the first `length` well-formed blobs.
    fn honest(length: usize) -> Self {
        let blobs = ValidBlob::all().take(length);
        Self {
            blobs: blobs.clone().map(ValidBlob::bytes).collect(),
            commitments: blobs.clone().map(ValidBlob::commitment).collect(),
            proofs: blobs.map(ValidBlob::blob_kzg_proof).collect(),
        }
    }
}

impl Operation for VerifyBlobKzgProofBatch {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "verify_blob_kzg_proof_batch";
    type Output = bool;

    fn run(&self) -> Result<bool, Error> {
        kzg::verify_blob_kzg_proof_batch(&self.blobs, &self.commitments, &self.proofs)
    }

    /// Honest batches of every length, wrong proofs, malformed entries, and mismatched lengths.
    fn cases(cases: &mut Cases<'_, Self>) {
        let all = ValidBlob::COUNT;

        // Every prefix of the honest batch verifies, the empty one included.
        for length in 0..all {
            cases.returns(format!("case_{length}"), true, move || Self::honest(length));
        }

        // Mutation: the first proof + G1, a valid point that proves nothing.
        cases.returns("case_incorrect_proof_add_one", false, move || {
            let mut input = Self::honest(all);
            input.proofs[0] = add_generator(&input.proofs[0]);
            input
        });

        // The identity proves only a constant polynomial, and blob 2 is not constant.
        cases.returns("case_incorrect_proof_point_at_infinity", false, || {
            let blob = ValidBlob::RANDOM_VALID1;
            Self {
                blobs: vec![blob.bytes()],
                commitments: vec![blob.commitment()],
                proofs: vec![Bytes::from(*G1_POINT_AT_INFINITY)],
            }
        });

        // Mutation: one malformed entry in an otherwise honest batch.
        //
        //     blobs      : blob 4 replaced
        //     commitment : the first one replaced
        //     proof      : the first one replaced
        for (i, blob) in INVALID_BLOBS.iter().enumerate() {
            cases.invalid(format!("case_invalid_blob_{i}"), move || {
                let mut input = Self::honest(all);
                input.blobs[4] = blob.into();
                input
            });
        }
        for (i, point) in INVALID_G1_POINTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_commitment_{i}"), move || {
                let mut input = Self::honest(all);
                input.commitments[0] = point.into();
                input
            });
        }
        for (i, point) in INVALID_G1_POINTS.iter().enumerate() {
            cases.invalid(format!("case_invalid_proof_{i}"), move || {
                let mut input = Self::honest(all);
                input.proofs[0] = point.into();
                input
            });
        }

        // Mutation: drop the last entry of one list, so the lengths disagree.
        //
        //     7 blobs, 7 commitments, 6 proofs → rejected
        let shorten: [(&str, Mutation); 3] = [
            ("blob", |input| {
                input.blobs.pop();
            }),
            ("commitment", |input| {
                input.commitments.pop();
            }),
            ("proof", |input| {
                input.proofs.pop();
            }),
        ];
        for (list, shorten) in shorten {
            cases.invalid(format!("case_{list}_length_different"), move || {
                let mut input = Self::honest(all);
                shorten(&mut input);
                input
            });
        }
    }
}
