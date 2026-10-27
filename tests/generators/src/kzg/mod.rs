//! The KZG operations, one module per handler.
//!
//! The handlers follow consensus-specs, `deneb/polynomial-commitments.md` and `fulu/polynomial-commitments-sampling.md`.

mod fixtures;

mod blob_to_kzg_commitment;
mod compute_blob_kzg_proof;
mod compute_cells;
mod compute_cells_and_kzg_proofs;
mod compute_challenge;
mod compute_kzg_proof;
mod compute_verify_cell_kzg_proof_batch_challenge;
mod recover_cells_and_kzg_proofs;
mod verify_blob_kzg_proof;
mod verify_blob_kzg_proof_batch;
mod verify_cell_kzg_proof_batch;
mod verify_kzg_proof;

use crate::Case;

/// The suite directory of the KZG vectors.
const KIND: &str = "kzg";

/// Collects the cases of each KZG operation.
pub(crate) const OPERATIONS: [fn(&mut Vec<Case>); 12] = [
    Case::collect::<blob_to_kzg_commitment::BlobToKzgCommitment>,
    Case::collect::<compute_blob_kzg_proof::ComputeBlobKzgProof>,
    Case::collect::<compute_cells::ComputeCells>,
    Case::collect::<compute_cells_and_kzg_proofs::ComputeCellsAndKzgProofs>,
    Case::collect::<compute_challenge::ComputeChallenge>,
    Case::collect::<compute_kzg_proof::ComputeKzgProof>,
    Case::collect::<compute_verify_cell_kzg_proof_batch_challenge::ComputeVerifyCellKzgProofBatchChallenge>,
    Case::collect::<recover_cells_and_kzg_proofs::RecoverCellsAndKzgProofs>,
    Case::collect::<verify_blob_kzg_proof::VerifyBlobKzgProof>,
    Case::collect::<verify_blob_kzg_proof_batch::VerifyBlobKzgProofBatch>,
    Case::collect::<verify_cell_kzg_proof_batch::VerifyCellKzgProofBatch>,
    Case::collect::<verify_kzg_proof::VerifyKzgProof>,
];
