//! `compute_verify_cell_kzg_proof_batch_challenge`: the challenge that folds many cell proofs into one.

use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{ValidBlob, coset_evals};
use crate::{Cases, Operation};

/// A batch of cells, each pointing at its commitment by position.
#[derive(Serialize)]
pub(crate) struct ComputeVerifyCellKzgProofBatchChallenge {
    commitments: Vec<Bytes>,
    commitment_indices: Vec<u64>,
    cell_indices: Vec<u64>,
    /// Each cell, as its list of field elements.
    cosets_evals: Vec<Vec<Bytes>>,
    proofs: Vec<Bytes>,
}

impl ComputeVerifyCellKzgProofBatchChallenge {
    /// The honest batch that takes, for each pick `(k, c)`, cell `c` of the blob behind commitment `k`.
    fn honest(blobs: &[usize], picks: &[(usize, usize)]) -> Self {
        let blobs: Vec<ValidBlob> = blobs.iter().copied().map(ValidBlob::at).collect();
        let mut input = Self {
            commitments: blobs.iter().map(|blob| blob.commitment()).collect(),
            commitment_indices: Vec::new(),
            cell_indices: Vec::new(),
            cosets_evals: Vec::new(),
            proofs: Vec::new(),
        };
        for &(k, c) in picks {
            let (cells, proofs) = blobs[k].cells_and_proofs();
            input.commitment_indices.push(k as u64);
            input.cell_indices.push(c as u64);
            input.cosets_evals.push(coset_evals(&cells[c]));
            input.proofs.push(proofs[c].clone());
        }
        input
    }
}

impl Operation for ComputeVerifyCellKzgProofBatchChallenge {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "compute_verify_cell_kzg_proof_batch_challenge";
    type Output = Bytes;

    fn run(&self) -> Result<Bytes, Error> {
        // The binding takes each cell whole, so its field elements are joined back.
        let cells: Vec<Bytes> = self
            .cosets_evals
            .iter()
            .map(|evals| Bytes(evals.iter().flat_map(|e| e.iter().copied()).collect()))
            .collect();
        kzg::compute_verify_cell_kzg_proof_batch_challenge(
            &self.commitments,
            &self.commitment_indices,
            &self.cell_indices,
            &cells,
            &self.proofs,
        )
        .map(Bytes)
    }

    /// Batches of honest cells, from one or more blobs, in various orders.
    fn cases(cases: &mut Cases<'_, Self>) {
        let first = |n: usize| (0..n).map(|c| (0, c)).collect::<Vec<_>>();
        let half = kzg::constants().cells_per_ext_blob / 2;
        let last = kzg::constants().cells_per_ext_blob - 1;

        // Each batch: its name, the blobs behind its commitments, and its picks.
        let batches = [
            ("empty", vec![], vec![]),
            ("single_cell", vec![0], vec![(0, 0)]),
            ("multiple_cells_single_blob", vec![1], first(4)),
            ("multiple_cells_multiple_blobs", vec![2, 3], vec![(0, 0), (1, 1), (0, 2), (1, 3)]),
            ("duplicate_cells", vec![4], vec![(0, 5); 3]),
            ("many_cells", vec![5], first(half)),
            ("non_sequential_indices", vec![6], [10, 5, 20, 15, 0, 30].map(|c| (0, c)).to_vec()),
            ("mixed_commitment_indices", vec![0, 1, 2], vec![(2, 0), (0, 1), (1, 2), (0, 3), (2, 4), (1, 5)]),
            ("max_cell_indices", vec![3], [last, last - 1, last - 2].map(|c| (0, c)).to_vec()),
            ("all_cells", vec![4], first(last + 1)),
        ];
        for (name, blobs, picks) in batches {
            cases.valid(format!("case_{name}"), move || Self::honest(&blobs, &picks));
        }
    }
}
