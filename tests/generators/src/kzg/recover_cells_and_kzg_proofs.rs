//! `recover_cells_and_kzg_proofs`: rebuild every cell and proof from at least half of the cells.

use ethlib::{Error, kzg};
use ethlib_vectors::Bytes;
use serde::Serialize;

use super::KIND;
use super::fixtures::{CellsAndProofs, INVALID_CELLS, VALID_CELLS, ValidBlob};
use crate::python_random::PythonRandom;
use crate::{Cases, Operation};

/// Cell indices, and the cells of one blob at those indices.
#[derive(Serialize)]
pub(crate) struct RecoverCellsAndKzgProofs {
    cell_indices: Vec<u64>,
    cells: Vec<Bytes>,
}

impl RecoverCellsAndKzgProofs {
    /// The cells of blob `b` at `indices`, in that order.
    fn of(b: usize, indices: impl IntoIterator<Item = usize>) -> Self {
        let (cells, _) = ValidBlob::at(b).cells_and_proofs();
        let indices: Vec<usize> = indices.into_iter().collect();
        Self {
            cell_indices: indices.iter().map(|&i| i as u64).collect(),
            cells: indices.iter().map(|&i| cells[i].clone()).collect(),
        }
    }
}

/// `0..n` in the order `random.Random(42).shuffle` leaves it.
fn shuffled(n: usize) -> Vec<usize> {
    let mut indices: Vec<usize> = (0..n).collect();
    PythonRandom::new(42).shuffle(&mut indices);
    indices
}

impl Operation for RecoverCellsAndKzgProofs {
    const KIND: &'static str = KIND;
    const HANDLER: &'static str = "recover_cells_and_kzg_proofs";
    type Output = CellsAndProofs;

    fn run(&self) -> Result<CellsAndProofs, Error> {
        let bytes = |items: Vec<Vec<u8>>| items.into_iter().map(Bytes).collect();
        kzg::recover_cells_and_kzg_proofs(&self.cell_indices, &self.cells)
            .map(|(cells, proofs)| (bytes(cells), bytes(proofs)))
    }

    /// Recovery from enough cells, then every way an input can be malformed.
    fn cases(cases: &mut Cases<'_, Self>) {
        // The extended blob has 128 cells, and any 64 of them determine it.
        let n = kzg::constants().cells_per_ext_blob;
        let half = n / 2;

        // Recoverable inputs: all cells, or exactly half, in increasing order.
        cases.valid("case_valid_no_missing", move || Self::of(0, 0..n));
        cases.valid("case_valid_half_missing_every_other_cell", move || Self::of(1, (0..n).step_by(2)));
        cases.valid("case_valid_half_missing_first_half", move || Self::of(2, 0..half));
        cases.valid("case_valid_half_missing_second_half", move || Self::of(3, half..n));

        // Too few or too many cells.
        //
        //     all_cells_are_missing              : 0 cells
        //     more_than_half_missing             : 63 cells, one short of half
        //     more_cells_than_cells_per_ext_blob : 129 cells, every index then 0 again
        cases.invalid("case_invalid_all_cells_are_missing", || Self { cell_indices: vec![], cells: vec![] });
        cases.invalid("case_invalid_more_than_half_missing", move || Self::of(4, 0..half - 1));
        cases.invalid("case_invalid_more_cells_than_cells_per_ext_blob", move || Self::of(5, (0..n).chain([0])));

        // Index 128 is one past the last cell.
        cases.invalid("case_invalid_cell_index", move || {
            let mut input = Self::of(6, 0..half);
            input.cell_indices[0] = n as u64;
            input
        });

        // One malformed cell among 64 honest ones.
        for (i, cell) in INVALID_CELLS.iter().enumerate() {
            cases.invalid(format!("case_invalid_cell_{i}"), move || {
                let mut input = Self::of(6, 0..half);
                input.cells[0] = cell.into();
                input
            });
        }

        // The two lists differ in length by one.
        cases.invalid("case_invalid_more_cell_indices_than_cells", move || {
            let mut input = Self::of(0, (0..n).step_by(2));
            input.cell_indices.push(n as u64 - 1);
            input
        });
        cases.invalid("case_invalid_more_cells_than_cell_indices", move || {
            let mut input = Self::of(1, (0..n).step_by(2));
            input.cells.push(VALID_CELLS[0].clone().into());
            input
        });

        // 65 cells whose first index repeats the second.
        //
        //     indices: [1, 1, 2, 3, ..., 64]
        cases.invalid("case_invalid_duplicate_cell_index", move || {
            let mut input = Self::of(2, 0..=half);
            input.cell_indices[0] = input.cell_indices[1];
            input
        });

        // Honest cells in shuffled order: the indices must be strictly increasing.
        cases.invalid("case_invalid_shuffled_no_missing", move || Self::of(4, shuffled(n)));
        cases.invalid("case_invalid_shuffled_one_missing", move || Self::of(5, shuffled(n - 1)));
        cases.invalid("case_invalid_shuffled_half_missing", move || Self::of(5, shuffled(half)));
    }
}
