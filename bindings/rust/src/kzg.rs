//! KZG commitments to blobs and to their cells.
//!
//! - Blobs, commitments and proofs follow `ethereum/consensus-specs`, `deneb/polynomial-commitments.md`.
//! - Cells follow `ethereum/consensus-specs`, `fulu/polynomial-commitments-sampling.md`.
//!
//! Every input passes to Lean unchanged.
//! Lean checks each length and each encoding, and rejects a bad one with an error.

use std::sync::OnceLock;

use crate::Error;
use crate::lean::{self, LeanObject, Object, run_bool, run_bytes};

// The `@[export]` symbols of `EthLib/Cryptography/Kzg`.
//
// Each export consumes its arguments and returns an owned IO result.
unsafe extern "C" {
    fn eth_kzg_const_bytes_per_field_element(unit: *mut LeanObject) -> u64;
    fn eth_kzg_const_bytes_per_commitment(unit: *mut LeanObject) -> u64;
    fn eth_kzg_const_bytes_per_proof(unit: *mut LeanObject) -> u64;
    fn eth_kzg_const_field_elements_per_blob(unit: *mut LeanObject) -> u64;
    fn eth_kzg_const_bytes_per_blob(unit: *mut LeanObject) -> u64;
    fn eth_kzg_const_field_elements_per_cell(unit: *mut LeanObject) -> u64;
    fn eth_kzg_const_bytes_per_cell(unit: *mut LeanObject) -> u64;
    fn eth_kzg_const_cells_per_ext_blob(unit: *mut LeanObject) -> u64;

    fn eth_kzg_blob_to_kzg_commitment(blob: *mut LeanObject) -> *mut LeanObject;
    fn eth_kzg_compute_challenge(blob: *mut LeanObject, commitment: *mut LeanObject) -> *mut LeanObject;
    fn eth_kzg_compute_kzg_proof(blob: *mut LeanObject, z: *mut LeanObject) -> *mut LeanObject;
    fn eth_kzg_verify_kzg_proof(
        commitment: *mut LeanObject,
        z: *mut LeanObject,
        y: *mut LeanObject,
        proof: *mut LeanObject,
    ) -> *mut LeanObject;
    fn eth_kzg_compute_blob_kzg_proof(blob: *mut LeanObject, commitment: *mut LeanObject) -> *mut LeanObject;
    fn eth_kzg_verify_blob_kzg_proof(
        blob: *mut LeanObject,
        commitment: *mut LeanObject,
        proof: *mut LeanObject,
    ) -> *mut LeanObject;
    fn eth_kzg_verify_blob_kzg_proof_batch(
        blobs: *mut LeanObject,
        commitments: *mut LeanObject,
        proofs: *mut LeanObject,
    ) -> *mut LeanObject;
    fn eth_kzg_compute_cells(blob: *mut LeanObject) -> *mut LeanObject;
    fn eth_kzg_compute_cells_and_kzg_proofs(blob: *mut LeanObject) -> *mut LeanObject;
    fn eth_kzg_compute_verify_cell_kzg_proof_batch_challenge(
        commitments: *mut LeanObject,
        commitment_indices: *mut LeanObject,
        cell_indices: *mut LeanObject,
        cosets_evals: *mut LeanObject,
        proofs: *mut LeanObject,
    ) -> *mut LeanObject;
    fn eth_kzg_verify_cell_kzg_proof_batch(
        commitments: *mut LeanObject,
        cell_indices: *mut LeanObject,
        cells: *mut LeanObject,
        proofs: *mut LeanObject,
    ) -> *mut LeanObject;
    fn eth_kzg_recover_cells_and_kzg_proofs(cell_indices: *mut LeanObject, cells: *mut LeanObject) -> *mut LeanObject;
}

/// Every cell of an extended blob, and one proof per cell, both in cell order.
pub type CellsAndProofs = (Vec<Vec<u8>>, Vec<Vec<u8>>);

/// The sizes of the KZG objects, read from Lean.
///
/// The specification fixes these values.
/// Reading them from Lean keeps a single source for each one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct Constants {
    /// Bytes in one encoded scalar of the BLS12-381 scalar field.
    pub bytes_per_field_element: usize,
    /// Bytes in one compressed G1 commitment.
    pub bytes_per_commitment: usize,
    /// Bytes in one compressed G1 proof.
    pub bytes_per_proof: usize,
    /// Field elements in one blob: the evaluations of one polynomial.
    pub field_elements_per_blob: usize,
    /// Bytes in one blob.
    pub bytes_per_blob: usize,
    /// Field elements in one cell: one coset of the extended evaluation domain.
    pub field_elements_per_cell: usize,
    /// Bytes in one cell.
    pub bytes_per_cell: usize,
    /// Cells in one blob after the Reed-Solomon extension doubles it.
    pub cells_per_ext_blob: usize,
}

/// The KZG sizes, read from Lean on first use.
///
/// # Panics
///
/// Panics if the Lean modules failed to initialize.
#[must_use]
pub fn constants() -> &'static Constants {
    static CONSTANTS: OnceLock<Constants> = OnceLock::new();
    CONSTANTS.get_or_init(|| {
        lean::enter();
        Constants {
            bytes_per_field_element: size(eth_kzg_const_bytes_per_field_element),
            bytes_per_commitment: size(eth_kzg_const_bytes_per_commitment),
            bytes_per_proof: size(eth_kzg_const_bytes_per_proof),
            field_elements_per_blob: size(eth_kzg_const_field_elements_per_blob),
            bytes_per_blob: size(eth_kzg_const_bytes_per_blob),
            field_elements_per_cell: size(eth_kzg_const_field_elements_per_cell),
            bytes_per_cell: size(eth_kzg_const_bytes_per_cell),
            cells_per_ext_blob: size(eth_kzg_const_cells_per_ext_blob),
        }
    })
}

/// Read one size from its Lean accessor.
fn size(accessor: unsafe extern "C" fn(*mut LeanObject) -> u64) -> usize {
    // SAFETY: every accessor takes the unit value and returns a plain integer.
    let value = unsafe { accessor(lean::unit()) };
    usize::try_from(value).expect("a KZG size fits in memory")
}

/// Commit to the polynomial a blob encodes.
///
/// # Errors
///
/// Rejects a blob of the wrong length, or one holding a non-canonical field element.
pub fn blob_to_kzg_commitment(blob: &[u8]) -> Result<Vec<u8>, Error> {
    let blob = Object::byte_array(blob);
    // SAFETY: the export consumes its argument and returns an owned `IO ByteArray`.
    unsafe { run_bytes(eth_kzg_blob_to_kzg_commitment(blob.into_raw())) }
}

/// The Fiat-Shamir challenge that binds a blob to its commitment.
///
/// # Errors
///
/// Rejects a malformed blob, or a commitment that is not a valid G1 point.
pub fn compute_challenge(blob: &[u8], commitment: &[u8]) -> Result<Vec<u8>, Error> {
    let (blob, commitment) = (Object::byte_array(blob), Object::byte_array(commitment));
    // SAFETY: the export consumes its arguments and returns an owned `IO ByteArray`.
    unsafe { run_bytes(eth_kzg_compute_challenge(blob.into_raw(), commitment.into_raw())) }
}

/// Prove the value `y = p(z)` of the blob's polynomial at the point `z`.
///
/// Returns the proof and `y`, in that order.
///
/// # Errors
///
/// Rejects a malformed blob, or a `z` outside the scalar field.
pub fn compute_kzg_proof(blob: &[u8], z: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let (blob, z) = (Object::byte_array(blob), Object::byte_array(z));
    // SAFETY: the export consumes its arguments and returns an owned `IO ByteArray`.
    let mut proof = unsafe { run_bytes(eth_kzg_compute_kzg_proof(blob.into_raw(), z.into_raw())) }?;

    // Lean returns both values in one buffer:
    //
    //     [ proof: 48 | y: 32 ]
    let y = proof.split_off(constants().bytes_per_proof);
    Ok((proof, y))
}

/// Whether `proof` shows that the committed polynomial takes the value `y` at `z`.
///
/// # Errors
///
/// Rejects a point that is not a valid G1 encoding, or a scalar outside the field.
pub fn verify_kzg_proof(commitment: &[u8], z: &[u8], y: &[u8], proof: &[u8]) -> Result<bool, Error> {
    let (commitment, z) = (Object::byte_array(commitment), Object::byte_array(z));
    let (y, proof) = (Object::byte_array(y), Object::byte_array(proof));
    // SAFETY: the export consumes its arguments and returns an owned `IO UInt8`.
    unsafe { run_bool(eth_kzg_verify_kzg_proof(commitment.into_raw(), z.into_raw(), y.into_raw(), proof.into_raw())) }
}

/// Prove a blob against its commitment, at the challenge point the two of them fix.
///
/// # Errors
///
/// Rejects a malformed blob, or a commitment that is not a valid G1 point.
pub fn compute_blob_kzg_proof(blob: &[u8], commitment: &[u8]) -> Result<Vec<u8>, Error> {
    let (blob, commitment) = (Object::byte_array(blob), Object::byte_array(commitment));
    // SAFETY: the export consumes its arguments and returns an owned `IO ByteArray`.
    unsafe { run_bytes(eth_kzg_compute_blob_kzg_proof(blob.into_raw(), commitment.into_raw())) }
}

/// Whether `proof` shows that `commitment` commits to `blob`.
///
/// # Errors
///
/// Rejects a malformed blob, or a point that is not a valid G1 encoding.
pub fn verify_blob_kzg_proof(blob: &[u8], commitment: &[u8], proof: &[u8]) -> Result<bool, Error> {
    let (blob, commitment) = (Object::byte_array(blob), Object::byte_array(commitment));
    let proof = Object::byte_array(proof);
    // SAFETY: the export consumes its arguments and returns an owned `IO UInt8`.
    unsafe { run_bool(eth_kzg_verify_blob_kzg_proof(blob.into_raw(), commitment.into_raw(), proof.into_raw())) }
}

/// Whether every proof shows that its commitment commits to its blob, checked as one batch.
///
/// # Errors
///
/// Rejects lists of different lengths, and any input the single check rejects.
pub fn verify_blob_kzg_proof_batch<B: AsRef<[u8]>>(
    blobs: &[B],
    commitments: &[B],
    proofs: &[B],
) -> Result<bool, Error> {
    let (blobs, commitments) = (Object::byte_arrays(blobs), Object::byte_arrays(commitments));
    let proofs = Object::byte_arrays(proofs);
    // SAFETY: the export consumes its arguments and returns an owned `IO UInt8`.
    unsafe {
        run_bool(eth_kzg_verify_blob_kzg_proof_batch(blobs.into_raw(), commitments.into_raw(), proofs.into_raw()))
    }
}

/// The cells of the extended blob, in cell order.
///
/// # Errors
///
/// Rejects a malformed blob.
pub fn compute_cells(blob: &[u8]) -> Result<Vec<Vec<u8>>, Error> {
    let blob = Object::byte_array(blob);
    // SAFETY: the export consumes its argument and returns an owned `IO ByteArray`.
    let cells = unsafe { run_bytes(eth_kzg_compute_cells(blob.into_raw())) }?;
    Ok(split(&cells, constants().bytes_per_cell))
}

/// The cells of the extended blob, and one proof per cell.
///
/// Returns the cells and the proofs, in that order.
///
/// # Errors
///
/// Rejects a malformed blob.
pub fn compute_cells_and_kzg_proofs(blob: &[u8]) -> Result<CellsAndProofs, Error> {
    let blob = Object::byte_array(blob);
    // SAFETY: the export consumes its argument and returns an owned `IO ByteArray`.
    let buffer = unsafe { run_bytes(eth_kzg_compute_cells_and_kzg_proofs(blob.into_raw())) }?;
    Ok(split_cells_and_proofs(&buffer))
}

/// The random challenge that folds a batch of cell proofs into one check.
///
/// Each entry of `cosets_evals` is one coset: its field elements, concatenated.
///
/// # Errors
///
/// Rejects lists of different lengths, an index out of range, and any malformed point or scalar.
pub fn compute_verify_cell_kzg_proof_batch_challenge<B: AsRef<[u8]>>(
    commitments: &[B],
    commitment_indices: &[u64],
    cell_indices: &[u64],
    cosets_evals: &[B],
    proofs: &[B],
) -> Result<Vec<u8>, Error> {
    let commitments = Object::byte_arrays(commitments);
    let (commitment_indices, cell_indices) = (indices(commitment_indices), indices(cell_indices));
    let (cosets_evals, proofs) = (Object::byte_arrays(cosets_evals), Object::byte_arrays(proofs));
    // SAFETY: the export consumes its arguments and returns an owned `IO ByteArray`.
    unsafe {
        run_bytes(eth_kzg_compute_verify_cell_kzg_proof_batch_challenge(
            commitments.into_raw(),
            commitment_indices.into_raw(),
            cell_indices.into_raw(),
            cosets_evals.into_raw(),
            proofs.into_raw(),
        ))
    }
}

/// Whether every cell proof holds for its cell, its index and its commitment.
///
/// # Errors
///
/// Rejects lists of different lengths, an index out of range, and any malformed input.
pub fn verify_cell_kzg_proof_batch<B: AsRef<[u8]>>(
    commitments: &[B],
    cell_indices: &[u64],
    cells: &[B],
    proofs: &[B],
) -> Result<bool, Error> {
    let (commitments, cell_indices) = (Object::byte_arrays(commitments), indices(cell_indices));
    let (cells, proofs) = (Object::byte_arrays(cells), Object::byte_arrays(proofs));
    // SAFETY: the export consumes its arguments and returns an owned `IO UInt8`.
    unsafe {
        run_bool(eth_kzg_verify_cell_kzg_proof_batch(
            commitments.into_raw(),
            cell_indices.into_raw(),
            cells.into_raw(),
            proofs.into_raw(),
        ))
    }
}

/// Rebuild every cell and its proof from at least half of the cells.
///
/// Returns the cells and the proofs, in that order.
///
/// # Errors
///
/// Rejects too few cells, unsorted or repeated indices, and any malformed cell.
pub fn recover_cells_and_kzg_proofs<B: AsRef<[u8]>>(
    cell_indices: &[u64],
    cells: &[B],
) -> Result<CellsAndProofs, Error> {
    let (cell_indices, cells) = (indices(cell_indices), Object::byte_arrays(cells));
    // SAFETY: the export consumes its arguments and returns an owned `IO ByteArray`.
    let buffer = unsafe { run_bytes(eth_kzg_recover_cells_and_kzg_proofs(cell_indices.into_raw(), cells.into_raw())) }?;
    Ok(split_cells_and_proofs(&buffer))
}

/// Pack indices the way the exports read them: 8 bytes each, big-endian.
///
/// ```text
///     [ index_0: 8 | index_1: 8 | ... | index_(n-1): 8 ]
/// ```
fn indices(indices: &[u64]) -> Object {
    let packed: Vec<u8> = indices.iter().flat_map(|index| index.to_be_bytes()).collect();
    Object::byte_array(&packed)
}

/// Split the buffer Lean returns for every cell and its proof.
///
/// ```text
///     [ cell_0 | ... | cell_127 | proof_0 | ... | proof_127 ]
///       2048 bytes each          48 bytes each
/// ```
fn split_cells_and_proofs(buffer: &[u8]) -> CellsAndProofs {
    let c = constants();
    let (cells, proofs) = buffer.split_at(c.cells_per_ext_blob * c.bytes_per_cell);
    (split(cells, c.bytes_per_cell), split(proofs, c.bytes_per_proof))
}

/// Cut a buffer into consecutive chunks of `size` bytes.
///
/// # Panics
///
/// Panics if the buffer is not a whole number of chunks.
/// Lean builds each buffer from whole objects, so a remainder means a broken export.
fn split(buffer: &[u8], size: usize) -> Vec<Vec<u8>> {
    let chunks = buffer.chunks_exact(size);
    assert!(chunks.remainder().is_empty(), "a Lean export returned a partial object");
    chunks.map(<[u8]>::to_vec).collect()
}
