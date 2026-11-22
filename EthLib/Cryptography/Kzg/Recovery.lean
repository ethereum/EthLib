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

Consensus-specs writes this recovery out at `8a3df1d7`, as a reference point:
<https://github.com/ethereum/consensus-specs/blob/8a3df1d79d70000801407e33d660171be9cd06d1/specs/fulu/polynomial-commitments-sampling.md>

EIP-7594 links that file at `9d377fd5`; the later text has the interface used here.
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
  -- At least one cell must be present: the source assumes it, and EthLib checks it here.
  --
  -- With every cell missing, the short polynomial has 129 coefficients, too many for the writes.
  if missingCellIndices.size ≥ CELLS_PER_EXT_BLOB then
    throw .tooManyMissingCells
  -- The small domain: the 128-th roots of unity `u_0, ..., u_127`, one per cell.
  let rouReduced := computeRootsOfUnity CELLS_PER_EXT_BLOB

  -- The short polynomial `Zs(x) = prod_c (x - u_rev(c))`, over the missing cells `c`.
  --
  -- Here `rev` reverses the bits of a cell index below 128.
  let xs : Array Fr := missingCellIndices.map fun mci =>
    rouReduced[reverseBits mci CELLS_PER_EXT_BLOB]'(by
      rw [size_computeRootsOfUnity]
      exact reverseBits_lt _ (by decide))
  let shortZeroPoly ← vanishingPolynomialcoeff xs

  -- Coefficient `64 i` of `Z` is coefficient `i` of `Zs`, and the other coefficients are 0.
  --
  -- So `Z(x) = Zs(x^64)`, with 8192 coefficients.
  --
  -- That is the closed form of the vanishing polynomial over a coset, on the full domain.
  return Array.ofFn (n := FIELD_ELEMENTS_PER_EXT_BLOB) fun j =>
    if h : j.val % FIELD_ELEMENTS_PER_CELL = 0 ∧
        j.val / FIELD_ELEMENTS_PER_CELL < shortZeroPoly.size then
      shortZeroPoly[j.val / FIELD_ELEMENTS_PER_CELL]
    else Fr.zero

/-- Recover the polynomial in coefficient form whose values on the domain are the extended blob. -/
def recoverPolynomialcoeff
    (cellIndices : Array CellIndex) (cosetsEvals : Array CosetEvals)
    : Except KzgError PolynomialCoeff := do
  -- There must be as many cell values as cell indices.
  --
  -- Without the check, the cells without values would read as zeros.
  if cosetsEvals.size ≠ cellIndices.size then
    throw (.inputLengthMismatch "cosetsEvals" cellIndices.size cosetsEvals.size)
  -- The extended domain: the 8192-th roots of unity, in their natural order.
  --
  -- This extended domain is the FFT domain of the comments below.
  let rouExt := computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB

  -- Values `64 c` to `64 c + 63`, in bit-reversed order, hold cell `c`, or zeros if it is missing.
  --
  -- Let E(x) be the polynomial of degree below 8192 through these values.
  --
  -- The callers check the indices and lengths, so the guards below never apply.
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

  -- The values of `E`, put back from bit-reversed order to natural order.
  let extended := bitReversalPermutation extendedRbo.toArray

  -- The missing cells are the indices below 128 absent from the input.
  --
  -- The vanishing polynomial Z(x) of the points of those cells, in coefficient form.
  --
  -- There are only 128 cells, so a linear lookup is fast enough.
  let missing : Array CellIndex :=
    (Array.range CELLS_PER_EXT_BLOB).filter fun ci => !cellIndices.contains ci
  let zeroPolyCoeff ← constructVanishingPolynomial missing

  -- The values of Z(x) on the domain, by the FFT.
  let zeroPolyEval := fftField zeroPolyCoeff rouExt

  -- The values of (E*Z)(x) on the domain, one product per point.
  --
  -- For the polynomial P(x) to recover, (E*Z)(x) and (P*Z)(x) agree over the FFT domain.
  let extTimesZero : Array Fr := Array.zipWith (· * ·) zeroPolyEval extended

  -- The coefficients of (P*Z)(x), by the inverse FFT of the values of (E*Z)(x) on the domain.
  --
  -- (P*Z)(x) has degree below 8192 and the same values there, so those are its coefficients.
  let extTimesZeroCoeffs := fftField extTimesZero rouExt (inv := true)

  -- Next step is to divide the polynomial (P*Z)(x) by polynomial Z(x) to get P(x).
  --
  -- We do this in evaluation form over a coset of the FFT domain to avoid division by 0.
  --
  -- On the FFT domain itself, division by 0 would happen, since Z(x) vanishes on part of it.
  --
  -- If Z(x) were zero anywhere on the coset too, the division below would silently produce 0.
  --
  -- It would not fail, since division by 0 in `Fr` returns 0.
  --
  -- So it would mask a broken vanishing polynomial.

  -- The values of (P*Z)(x) on the coset, by the coset FFT of its coefficients.
  let pzOverCoset := cosetFftField extTimesZeroCoeffs rouExt
  -- The values of Z(x) on the coset, by the coset FFT of its coefficients.
  let zOverCoset  := cosetFftField zeroPolyCoeff       rouExt
  -- The values of P(x) = (P*Z)(x) / Z(x) on the coset, one quotient per point.
  --
  -- One batch inversion gives every `1 / Z(x)`.
  let zInverses := Fr.batchInverse zOverCoset
  let pOverCoset : Array Fr := Array.zipWith (· * ·) pzOverCoset zInverses
  -- The coefficients of P(x), by the inverse coset FFT.
  let pCoeff := cosetFftField pOverCoset rouExt (inv := true)

  -- The result is the first 4096 coefficients of P(x).
  return pCoeff.extract 0 FIELD_ELEMENTS_PER_BLOB

/-- Recover every cell and every cell proof from at least half of the cells.

The recovery uses FFTs, which is faster than Lagrange interpolation.

The method is the one of [the note on Reed–Solomon recovery with FFTs][rs].

[rs]: https://ethresear.ch/t/reed-solomon-erasure-code-recovery-in-n-log-2-n-time-with-ffts/3039
-/
def recoverCellsAndKzgProofs (setup : TrustedSetup)
    (cellIndices : Array CellIndex) (cells : Array Cell)
    : Except KzgError (Array Cell × Array KZGProof) := do

  -- There must be as many cells as cell indices.
  if cells.size ≠ cellIndices.size then
    throw (.inputLengthMismatch "cells" cellIndices.size cells.size)

  -- The number `k` of cell indices must satisfy `64 <= k <= 128`; here the lower bound.
  if cellIndices.size < CELLS_PER_EXT_BLOB / 2 then
    throw (.notEnoughCells cellIndices.size)

  -- The upper bound of the same requirement.
  if cellIndices.size > CELLS_PER_EXT_BLOB then
    throw (.tooManyCells cellIndices.size)

  -- Each cell index is below 128, checked here before the order.
  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw (.cellIndexOutOfBounds ((cellIndices.find? (· ≥ CELLS_PER_EXT_BLOB)).getD 0))

  -- The cell indices are distinct and in ascending order.
  --
  -- A strictly ascending list enforces both at once.
  if (cellIndices.zip (cellIndices.extract 1)).any (fun (prev, next) => next ≤ prev) then
    let pairs := cellIndices.zip (cellIndices.extract 1)
    let (previous, next) := (pairs.find? (fun (prev, next) => next ≤ prev)).getD (0, 0)
    throw (.indicesNotAscending previous next)

  -- Each cell is decoded into its 64 values in `Fr`.
  --
  -- Each cell has 2048 bytes by its type.
  let cosetsEvals : Array CosetEvals ← cells.mapM fun c =>
    cellToCosetEvals c

  -- The polynomial of the blob, in coefficient form, recovered from the cells.
  let polyCoeff ← recoverPolynomialcoeff cellIndices cosetsEvals
  -- Every cell and every cell proof, computed from that polynomial.
  computeCellsAndKzgProofsPolynomialcoeff setup polyCoeff

end EthLib.Cryptography.Kzg
