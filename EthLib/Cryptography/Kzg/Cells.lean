module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.BitReversal
public import EthLib.Cryptography.Kzg.Polynomials
public import EthLib.Cryptography.Kzg.Fft
public import EthLib.Cryptography.Kzg.Core
public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Kzg.Errors

/-!
# `Cells`

Cell proofs over a blob extended by a Reed-Solomon code.

EIP-7594 adds these operations at the Fusaka fork.

The values of the extended polynomial split into 128 cosets of 64 values each.

Each cell carries its own KZG multi-evaluation proof.

So a verifier can sample any set of cells without downloading the whole blob.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open EthLib.Cryptography.Bls (G1 G2 Fr)

/-! ## Type aliases -/

/-- A cell: 64 field elements of 32 bytes each. -/
abbrev Cell             := Vector UInt8 BYTES_PER_CELL
abbrev CellIndex        := Nat
abbrev CommitmentIndex  := Nat
abbrev Coset            := Array Fr
abbrev CosetEvals       := Array Fr

/-- Convert an untrusted `Cell` into a trusted `CosetEvals`. -/
def cellToCosetEvals (cell : Cell) : Except KzgError CosetEvals :=
  bytesToBlsFields (k := FIELD_ELEMENTS_PER_CELL) cell

/-- Convert a trusted `CosetEvals` back into an untrusted `Cell`. -/
def cosetEvalsToCell (cosetEvals : CosetEvals) : Cell :=
  (Vector.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i => blsFieldToBytes cosetEvals[i.val]!).flatten

/-! ## Cell cosets -/

/-- The coset of a cell.

Let `G = {1, g, g^2, ...}` be the subgroup of order 64 of the 8192-th roots of unity.

The coset is `h * G = {h, hg, hg^2, ...}` for a shift `h`.

It is block `i` of 64 points of the bit-reversed domain, for the cell index `i`. -/
def cosetForCell (cellIndex : CellIndex) : Except KzgError Coset := do
  if cellIndex ≥ CELLS_PER_EXT_BLOB then
    throw .cellIndexOutOfBounds
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  let start := FIELD_ELEMENTS_PER_CELL * cellIndex
  return Array.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i => domain[start + i.val]!

/-- Interpolate one cell: the polynomial `I` of degree below 64 with the values on the coset.

The coset has the shift `h`, and it is a shifted FFT domain, in bit-reversed order.

- Point `j` is `h * v^(rev(j))`, for a 64-th root of unity `v` and the 6-bit reversal `rev`.
- `J(Y) = I(h * Y)` takes the cell's values on the 64-th roots of unity.
- So `J` is the inverse FFT of the bit-reversed values.
- Then `I_i = J_i * h^(-i)`.

It returns the same polynomial as Lagrange interpolation.

Lagrange needs `64 * 63` field inversions.

This needs one inverse FFT and one inversion. -/
def interpolateCosetEvals (h : Fr) (evals : CosetEvals) : Except KzgError PolynomialCoeff := do
  if evals.size ≠ FIELD_ELEMENTS_PER_CELL then
    throw (.inputLengthMismatch "ys" FIELD_ELEMENTS_PER_CELL evals.size)
  let j := fftField (bitReversalPermutation evals) (computeRootsOfUnity FIELD_ELEMENTS_PER_CELL) (inv := true)
  return shiftVals j h.inverse

/-- The values of a polynomial on the extended domain, in bit-reversed order.

Cell `i` holds the values on its coset.

That coset is the `i`-th block of 64 points of the bit-reversed domain.

So the values are the 64 of cell 0, then the 64 of cell 1, up to cell 127.

One FFT of size 8192 gives every value, in `O(n log n)` field operations.

Horner's rule at each point would take `O(n^2)`.

The polynomial has at most 8192 coefficients. -/
def extendedEvaluations (polynomialCoeff : PolynomialCoeff) : Array Fr :=
  let padded := polynomialCoeff ++
    Array.replicate (FIELD_ELEMENTS_PER_EXT_BLOB - polynomialCoeff.size) Fr.zero
  bitReversalPermutation (fftField padded (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB))

/-- The cells of the extended blob, cut from its values in bit-reversed order. -/
def cellsOfExtendedEvaluations (evals : Array Fr) : Array Cell :=
  (Array.range CELLS_PER_EXT_BLOB).map fun i =>
    cosetEvalsToCell (evals.extract (i * FIELD_ELEMENTS_PER_CELL) ((i + 1) * FIELD_ELEMENTS_PER_CELL))

/-- Reed-Solomon-extend `blob` and return its cells. -/
def computeCells (blob : Blob) : Except KzgError (Array Cell) := do
  let polynomial ← blobToPolynomial blob
  return cellsOfExtendedEvaluations (extendedEvaluations (polynomialEvalToCoeff polynomial))

/-- Compute cells and proofs for a polynomial in coefficient form.

The direct method proves each cell on its own.

It divides `f` by the cell's vanishing polynomial, then commits to the quotient.

That costs one multi-scalar multiplication of 4032 points per cell.

The 128 quotients share their structure, so this computes them together.

- Cell `k` is the coset `h_k * mu_64`.
- Its vanishing polynomial is `Z_k = X^64 - c_k`, with `c_k = h_k^64`.
- The quotient is `q_k = f / Z_k = sum_{d >= 1} c_k^(d - 1) * (f >> 64 d)`.
- Here `(f >> m)_i = f_(i + m)`.
- The proof is `[q_k(s)] = sum_{d = 1}^{63} c_k^(d - 1) * H_d`.
- The point `H_d` is `sum_i f_(i + 64 d) * [s^i]`.

The points `H_d` do not depend on the cell.

So 63 multi-scalar multiplications serve all 128 proofs.

Each `c_k` is a 128-th root of unity, taken in bit-reversed order.

So the proofs are the values of `sum_d H_d * Y^(d - 1)` at those roots.

One FFT in G1 computes them all.

This is the Toeplitz structure of FK20.

See Feist and Khovratovich, "Fast amortized KZG proofs", <https://eprint.iacr.org/2023/033>.

The polynomial has at most 4096 coefficients, the size of the monomial setup. -/
def computeCellsAndKzgProofsPolynomialcoeff (setup : TrustedSetup)
    (polynomialCoeff : PolynomialCoeff) : Except KzgError (Array Cell × Array KZGProof) := do
  let n := FIELD_ELEMENTS_PER_CELL
  let size := polynomialCoeff.size
  let cells := cellsOfExtendedEvaluations (extendedEvaluations polynomialCoeff)

  -- Phase 1: `H_d` for each shift `d` that leaves a coefficient.
  --
  -- With 4096 coefficients, `d` runs from 1 to 63, and `H_d` sums `4096 - 64 d` points.
  --
  -- The sums are independent, so each runs as its own task.
  --
  -- Both slices have `size - n * d` entries, so the lengths of the sum agree.
  --
  -- Both phases run inside one task.
  -- Lean's pool starts a new worker only when no worker is idle.
  -- Spawned from a busy worker, the inner tasks then grow the pool.
  let shifts := (size + n - 1) / n - 1
  let proofs := (Task.spawn fun _ =>
    let tasks := (Array.range shifts).map fun e => Task.spawn fun _ =>
      let d := e + 1
      Bls.G1.msm (setup.g1Monomial.toArray.extract 0 (size - n * d))
        (polynomialCoeff.extract (n * d) size)
    let hs := tasks.map Task.get

    -- Phase 2: evaluate sum_d H_d * Y^(d - 1) at the 128-th roots of unity.
    -- The bit reversal puts the proofs in cell order.
    let padded := hs ++ Array.replicate (CELLS_PER_EXT_BLOB - hs.size) Bls.G1.zero
    bitReversalPermutation (fftG1 padded (computeRootsOfUnity CELLS_PER_EXT_BLOB))).get
  return (cells, proofs.map compressG1)

/-- Compute the cells of a blob and their proofs.

The proofs come together, by the FK20 method. -/
def computeCellsAndKzgProofs (setup : TrustedSetup)
    (blob : Blob) : Except KzgError (Array Cell × Array KZGProof) := do
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  computeCellsAndKzgProofsPolynomialcoeff setup polynomialCoeff

/-- Random challenge `r` used in the universal verification equation. -/
def computeVerifyCellKzgProofBatchChallenge
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : Fr :=
  let h := RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN
    ++ intToBytesBE FIELD_ELEMENTS_PER_BLOB 8
    ++ intToBytesBE FIELD_ELEMENTS_PER_CELL 8
    ++ intToBytesBE commitments.size 8
    ++ intToBytesBE cellIndices.size 8
  let h := commitments.foldl (init := h) fun h c => h ++ ⟨c.toArray⟩
  -- One entry per cell, from four arrays of one length, which the callers check.
  let cells := (commitmentIndices.zip cellIndices).zip (cosetsEvals.zip proofs)
  let h := cells.foldl (init := h) fun h ((commitmentIndex, cellIndex), (evals, proof)) =>
    let h := h ++ intToBytesBE commitmentIndex 8
    let h := h ++ intToBytesBE cellIndex 8
    let h := evals.foldl (init := h) fun h ce =>
      h ++ ⟨(blsFieldToBytes ce).toArray⟩
    h ++ ⟨proof.toArray⟩
  Fr.hashToBlsField h

/-- Verify that a set of cells belong to their commitments, given distinct commitments.

Each cell comes with a commitment index, a cell index, its values and a proof.

The proof shows that the values are those of the polynomial of the indexed commitment.

The values are taken over the coset of the cell index.

It is the core of the batch check of cell proofs. -/
def verifyCellKzgProofBatchImpl (setup : TrustedSetup)
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : Except KzgError Bool := do
  -- Length and bounds checks.
  if cellIndices.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "cellIndices" commitmentIndices.size cellIndices.size)
  if cosetsEvals.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size cosetsEvals.size)
  if proofs.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "proofs" commitmentIndices.size proofs.size)
  if commitmentIndices.any (· ≥ commitments.size) then
    throw .commitmentIndexOutOfBounds
  -- The commitments list must contain no duplicates
  if commitments.zipIdx.any (fun (c, i) => commitments.idxOf? c ≠ some i) then
    throw .duplicateCommitments

  -- The verification equation that we will check is pairing (LL, LR) = pairing (RL, [1]), where
  -- LL = sum_k r^k proofs[k],
  -- LR = [s^n]
  -- RL = RLC - RLI + RLP, where
  --   RLC = sum_i weights[i] commitments[i]
  --   RLI = [sum_k r^k interpolation_poly_k(s)]
  --   RLP = sum_k (r^k * h_k^n) proofs[k]
  --
  -- Here, the variables have the following meaning:
  -- - k < cellIndices.size is an index iterating over all cells in the input
  -- - r is a random coefficient, derived from hashing all data provided by the prover
  -- - s is the secret embedded in the KZG setup
  -- - n = FIELD_ELEMENTS_PER_CELL is the size of the evaluation domain
  -- - i ranges over all provided commitments
  -- - weights[i] is a weight computed for commitment i
  --   - It depends on r and on which cells are associated with commitment i
  -- - interpolation_poly_k is the interpolation polynomial for the kth cell
  -- - h_k is the coset shift specifying the evaluation domain of the kth cell

  let numCells := cellIndices.size
  let n := FIELD_ELEMENTS_PER_CELL
  let numCommitments := commitments.size

  -- Step 1: r and r^0..r^(num_cells-1).
  let r := computeVerifyCellKzgProofBatchChallenge
            commitments commitmentIndices cellIndices cosetsEvals proofs
  let rPowers := computePowers r numCells

  -- Step 2: LL = Σ_k r^k proofs[k].
  -- The proofs are decoded once, for this sum and for RLP.
  let proofsG1 ← proofs.mapM uncompressG1
  let ll : G1 ← g1LincombPoints proofsG1 rPowers

  -- Step 3: LR = [s^n].
  let lr : G2 := setup.g2Monomial[FIELD_ELEMENTS_PER_CELL]'(by decide)

  -- Step 4.1: weights[i] = Σ_{k : commitmentIndices[k] = i} r^k, each index checked above.
  let weights : Array Fr := (commitmentIndices.zip rPowers).foldl
    (init := Array.replicate numCommitments Fr.zero)
    fun weights (i, rPower) => weights.modify i (· + rPower)

  -- Step 4.1b: RLC = Σ_i weights[i] commitments[i].
  let rlc : G1 ← g1LincombPoints (← commitments.mapM uncompressG1) weights

  -- The coset shift h_k of every cell.
  -- The domain is computed once, not once per cell.
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  -- The shift of cell `i` is entry `64 i` of the domain, which exists exactly when `i < 128`.
  let shifts : Array Fr ← cellIndices.mapM fun cellIndex =>
    if h : n * cellIndex < domain.size then pure domain[n * cellIndex]
    else throw .cellIndexOutOfBounds

  -- Step 4.2: RLI = [Σ_k r^k I_k(s)], each I_k from one inverse FFT over its coset.
  --
  -- That is the inverse DFT method of the post on the universal verification equation.
  let sumInterp : PolynomialCoeff ← (shifts.zip (cosetsEvals.zip rPowers)).foldlM
    (init := Array.replicate n Fr.zero)
    fun sumInterp (shift, evals, rPower) => do
      let interp ← interpolateCosetEvals shift evals
      let scaled ← multiplyPolynomialcoeff #[rPower] interp
      pure (addPolynomialcoeff sumInterp scaled)
  let rli : G1 ← g1LincombPoints (setup.g1Monomial.toArray.extract 0 n) sumInterp

  -- Step 4.3: RLP = Σ_k (r^k * h_k^n) proofs[k].
  let weightedRPowers : Array Fr :=
    Array.zipWith (fun rPower shift => rPower * shift ^ (Fr.ofNat n)) rPowers shifts
  let rlp : G1 ← g1LincombPoints proofsG1 weightedRPowers

  -- Step 4.4: RL = RLC - RLI + RLP.
  let rl : G1 := Bls.G1.add (Bls.G1.add rlc (Bls.G1.neg rli)) rlp

  -- Step 5: pairing(LL, LR) = pairing(RL, [1]).
  return Bls.pairingCheck #[
    (ll, lr),
    (rl, Bls.G2.neg (setup.g2Monomial[0]'(by decide)))
  ]

/-- Verify that a set of cells belong to their commitments.

Each cell comes with a commitment, a cell index and a proof.

The proof shows that the cell holds the values of the committed polynomial on its coset.

The check is the universal verification equation of
<https://ethresear.ch/t/a-universal-verification-equation-for-data-availability-sampling/13240>.

It removes repeated commitments, then runs the core check. -/
def verifyCellKzgProofBatch (setup : TrustedSetup)
    (commitmentsBytes : Array Bytes48)
    (cellIndices : Array CellIndex)
    (cells : Array Cell)
    (proofsBytes : Array Bytes48) : Except KzgError Bool := do

  if cells.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cells" commitmentsBytes.size cells.size)
  if proofsBytes.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "proofsBytes" commitmentsBytes.size proofsBytes.size)
  if cellIndices.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cellIndices" commitmentsBytes.size cellIndices.size)

  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw .cellIndexOutOfBounds

  -- Remove repeated commitments, keeping the first index, by a scan over the short list.
  let (deduped, commitmentIndices) ←
    commitmentsBytes.zipIdx.foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array CommitmentIndex)))
      fun (deduped, commitmentIndices) (cb, i) => do
        -- Validate the commitment, which also decodes it.
        let _ ← match bytesToKzgCommitment cb with
                | .ok c    => pure c
                | .error _ => throw (.invalidCommitment (some i))
        -- Find or append.
        match deduped.idxOf? cb with
        | some j => pure (deduped, commitmentIndices.push j)
        | none   => pure (deduped.push cb, commitmentIndices.push deduped.size)

  -- Convert cells to coset evaluations.
  let cosetsEvals : Array CosetEvals ← cells.mapM fun c =>
    cellToCosetEvals c

  -- Validate proofs.
  let proofs : Array KZGProof ← proofsBytes.zipIdx.mapM fun (pb, i) =>
    match bytesToKzgProof pb with
    | .ok p    => pure p
    | .error _ => throw (.invalidProof (some i))

  verifyCellKzgProofBatchImpl setup deduped commitmentIndices cellIndices cosetsEvals proofs

/-- Decode a buffer of packed indices.

The buffer holds the indices one after another, each as 8 big-endian bytes.

The Python binding packs index arrays this way, so the C exports take only byte arrays.

It is pure parsing, so it lives in the specification, where the proofs can reach it.

A length that is not a multiple of 8 is rejected, never truncated.
-/
def unpackIndicesBE (b : ByteArray) : Except KzgError (Array Nat) := do
  -- A partial last index means a malformed buffer.
  if b.size % 8 != 0 then
    throw (.badIndicesBytesSize b.size)
  let n := b.size / 8
  let mut out : Array Nat := Array.mkEmpty n
  for i in [:n] do
    out := out.push (bytesBEToNat (b.extract (i*8) ((i+1)*8)))
  return out

end EthLib.Cryptography.Kzg
