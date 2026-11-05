module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.BitReversal
public import EthLib.Cryptography.Kzg.Polynomials
public import EthLib.Cryptography.Kzg.Fft
public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Kzg.Errors

/-!
# `Recovery`

The Reed-Solomon recovery routine for cell proofs.

EIP-7594 adds it at the Fusaka fork.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)

open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal

/-- The polynomial that vanishes on the points of the missing cells.

At least one cell must be present.

If every cell were missing, the polynomial would be `Z(x) = x^n - 1`, with `n = 8192`.

Recovery needs at least half of the cells, so that case never arises. -/
def constructVanishingPolynomial
    (missingCellIndices : Array CellIndex) : Except KzgError PolynomialCoeff := do
  -- With every cell missing, the short polynomial has 129 coefficients, too many for the writes.
  if missingCellIndices.size ≥ CELLS_PER_EXT_BLOB then
    throw .tooManyMissingCells
  -- The small domain: the 128-th roots of unity.
  let rouReduced := computeRootsOfUnity CELLS_PER_EXT_BLOB

  -- The vanishing polynomial over the small domain, with roots in bit-reversed order.
  let xs : Array Fr := missingCellIndices.map fun mci =>
    rouReduced[reverseBits mci CELLS_PER_EXT_BLOB]'(by
      rw [size_computeRootsOfUnity]
      exact reverseBits_lt _ (by decide))
  let shortZeroPoly ← vanishingPolynomialcoeff xs

  -- Extend it to the full domain, by the closed form of the vanishing polynomial of a coset.
  --
  -- Coefficient `64 i` is coefficient `i` of the short polynomial, and the others are zero.
  return Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun j =>
    if h : j.val % FIELD_ELEMENTS_PER_CELL = 0 ∧
        j.val / FIELD_ELEMENTS_PER_CELL < shortZeroPoly.size then
      shortZeroPoly[j.val / FIELD_ELEMENTS_PER_CELL]
    else Fr.zero

/-- Value `j` of cell `ci` lies inside the extended blob. -/
theorem cell_slot_lt {ci j : Nat} (hci : ci < CELLS_PER_EXT_BLOB)
    (hj : j < FIELD_ELEMENTS_PER_CELL) :
    ci * FIELD_ELEMENTS_PER_CELL + j < FIELD_ELEMENTS_PER_EXT_BLOB := by
  have h1 : CELLS_PER_EXT_BLOB = 128 := rfl
  have h2 : FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
  have h3 : FIELD_ELEMENTS_PER_CELL = 64 := rfl
  rw [h1] at hci
  rw [h3] at hj ⊢
  rw [h2]
  omega

/-- Recover the polynomial in coefficient form whose values on the domain are the extended blob. -/
def recoverPolynomialcoeff
    (cellIndices : Array CellIndex) (cosetsEvals : Array CosetEvals)
    : Except KzgError PolynomialCoeff := do
  -- Each cell index needs its values, so a length mismatch fails instead of reading zeros.
  if cosetsEvals.size ≠ cellIndices.size then
    throw (.inputLengthMismatch "cosetsEvals" cellIndices.size cosetsEvals.size)
  -- The extended domain, called the FFT domain below.
  let rouExt := computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB

  -- Flatten the values of the cosets, with zeros for the missing cells.
  --
  -- Let E(x) be the polynomial of degree below 8192 through these values.
  --
  -- A cell index of 128 or more names no cell, and a cell shorter than 64 values reads as zeros.
  let extendedRbo : Vector Fr FIELD_ELEMENTS_PER_EXT_BLOB :=
    (cellIndices.zip cosetsEvals).foldl
      (init := Vector.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
      fun acc (ci, cell) =>
        if hci : ci < CELLS_PER_EXT_BLOB then
          (Array.finRange FIELD_ELEMENTS_PER_CELL).foldl (init := acc) fun acc j =>
            let v := if hj : j.val < cell.size then cell[j.val] else Fr.zero
            acc.set (ci * FIELD_ELEMENTS_PER_CELL + j.val) v (cell_slot_lt hci j.isLt)
        else acc

  let extended := bitReversalPermutation extendedRbo.toArray

  -- The vanishing polynomial Z(x) of the missing points, in coefficient form.
  --
  -- There are only 128 cells, so a linear lookup is fast enough.
  let missing : Array CellIndex :=
    (Array.range CELLS_PER_EXT_BLOB).filter fun ci => !cellIndices.contains ci
  let zeroPolyCoeff ← constructVanishingPolynomial missing

  -- Convert Z(x) to evaluation form over the FFT domain.
  let zeroPolyEval := fftField zeroPolyCoeff rouExt

  -- Compute (E*Z)(x) = E(x) * Z(x) in evaluation form over the FFT domain.
  --
  -- For the polynomial P(x) to recover, (E*Z)(x) and (P*Z)(x) agree over the FFT domain.
  let extTimesZero : Array Fr := Array.zipWith (· * ·) zeroPolyEval extended

  -- (P*Z)(x) has degree below 8192, so the inverse FFT of (E*Z)(x) gives its coefficients.
  let extTimesZeroCoeffs := fftField extTimesZero rouExt (inv := true)

  -- Next step is to divide the polynomial (P*Z)(x) by polynomial Z(x) to get P(x).
  -- We do this in evaluation form over a coset of the FFT domain to avoid division by 0,
  -- i.e. because Z(x) vanishes on (part of) the FFT domain itself. If Z(x) were zero
  -- anywhere on the coset too, the division below would silently produce 0 instead of
  -- failing (see the `Div Fr` docstring), masking a broken vanishing polynomial.

  -- Convert (P*Z)(x) to evaluation form over a coset of the FFT domain.
  let pzOverCoset := cosetFftField extTimesZeroCoeffs rouExt
  -- Convert Z(x) to evaluation form over a coset of the FFT domain.
  let zOverCoset  := cosetFftField zeroPolyCoeff       rouExt
  -- Compute P(x) = (P*Z)(x) / Z(x) in evaluation form over a coset of the FFT domain.
  -- One batch inversion gives every `1 / Z(x)`.
  let zInverses := Fr.batchInverse zOverCoset
  let pOverCoset : Array Fr := Array.zipWith (· * ·) pzOverCoset zInverses
  -- Convert P(x) to coefficient form.
  let pCoeff := cosetFftField pOverCoset rouExt (inv := true)

  return pCoeff.extract 0 FIELD_ELEMENTS_PER_BLOB

/-- Recover every cell and every cell proof from at least half of the cells.

The recovery uses FFTs, which is faster than Lagrange interpolation.

The method is the one of
<https://ethresear.ch/t/reed-solomon-erasure-code-recovery-in-n-log-2-n-time-with-ffts/3039>. -/
def recoverCellsAndKzgProofs (setup : TrustedSetup)
    (cellIndices : Array CellIndex) (cells : Array Cell)
    : Except KzgError (Array Cell × Array KZGProof) := do

  -- There must be an equal number of cells and indices.
  if cells.size ≠ cellIndices.size then
    throw (.inputLengthMismatch "cells" cellIndices.size cells.size)

  -- At least 50% of cells must be provided.
  if cellIndices.size < CELLS_PER_EXT_BLOB / 2 then
    throw .notEnoughCells

  -- There must not be more cells than can exist in a single blob.
  if cellIndices.size > CELLS_PER_EXT_BLOB then
    throw .tooManyCells

  -- Cell indices must be within bounds.
  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw .cellIndexOutOfBounds

  -- Cell indices must be strictly ascending. This enforces two requirements
  -- at once: no duplicates, and ascending order.
  if (cellIndices.zip (cellIndices.extract 1)).any (fun (prev, next) => next ≤ prev) then
    throw .indicesNotAscending

  -- Convert cells to coset evaluations.
  let cosetsEvals : Array CosetEvals ← cells.mapM fun c =>
    cellToCosetEvals c

  let polyCoeff ← recoverPolynomialcoeff cellIndices cosetsEvals
  computeCellsAndKzgProofsPolynomialcoeff setup polyCoeff

end EthLib.Cryptography.Kzg
