module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.BitReversal
public import EthLib.Cryptography.Kzg.Polynomials
public import EthLib.Cryptography.Kzg.Fft
public import EthLib.Cryptography.Kzg.Core
public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Kzg.Errors
public import EthLib.Base.BigEndian

/-!
# `Cells`

Cell proofs over a blob extended by a Reed-Solomon code.

EIP-7594 adds these operations at the Fusaka fork.

The values of the extended polynomial split into 128 cosets of 64 values each.

Each cell carries its own KZG multi-evaluation proof.

So a verifier can sample any set of cells without downloading the whole blob.

The step comments quote the functions of the same names in consensus-specs at `8a3df1d7`:
<https://github.com/ethereum/consensus-specs/blob/8a3df1d79d70000801407e33d660171be9cd06d1/specs/fulu/polynomial-commitments-sampling.md>

EIP-7594 links that file at `9d377fd5`; the later text has the interface used here.
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
  -- cell_to_coset_evals: `evals[i] = bytes_to_bls_field(cell[start:end])`, for 64 values.
  bytesToBlsFields (k := FIELD_ELEMENTS_PER_CELL) cell

/-- Convert a trusted `CosetEvals` back into an untrusted `Cell`.

Every caller passes 64 values; a value past the end of a shorter array encodes as zero. -/
def cosetEvalsToCell (cosetEvals : CosetEvals) : Cell :=
  -- coset_evals_to_cell: `cell += bls_field_to_bytes(coset_evals[i])`, for 64 values.
  (Vector.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i =>
    blsFieldToBytes (if h : i.val < cosetEvals.size then cosetEvals[i.val] else Fr.zero)).flatten

/-! ## Cell cosets -/

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


/-- The coset of a cell.

Let `G = {1, g, g^2, ...}` be the subgroup of order 64 of the 8192-th roots of unity.

The coset is `h * G = {h, hg, hg^2, ...}` for a shift `h`.

It is block `i` of 64 points of the bit-reversed domain, for the cell index `i`. -/
def cosetForCell (cellIndex : CellIndex) : Except KzgError Coset := do
  -- coset_for_cell: `assert cell_index < CELLS_PER_EXT_BLOB`.
  if hci : cellIndex ≥ CELLS_PER_EXT_BLOB then
    throw (.cellIndexOutOfBounds cellIndex)
  else
    -- `roots_of_unity_brp = bit_reversal_permutation(compute_roots_of_unity(...))`.
    let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
    -- `roots_of_unity_brp[FIELD_ELEMENTS_PER_CELL * cell_index : ... * (cell_index + 1)]`.
    return Array.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i =>
      domain[FIELD_ELEMENTS_PER_CELL * cellIndex + i.val]'(by
        rw [size_rootsOfUnityBrp, Nat.mul_comm]
        exact cell_slot_lt (Nat.lt_of_not_le hci) i.isLt)

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
  -- In place of `interpolate_polynomialcoeff(coset_for_cell(...), cosets_evals[k])`.
  --
  -- `assert len(xs) == len(ys)`, with the 64 points of a coset.
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
  -- compute_cells: `polynomial = blob_to_polynomial(blob)`.
  --
  -- `assert len(blob) == BYTES_PER_BLOB` holds by the type.
  let polynomial ← blobToPolynomial blob
  -- `polynomial_coeff = polynomial_eval_to_coeff(polynomial)`.
  --
  -- The loop of `evaluate_polynomialcoeff` over each `coset_for_cell(i)` is one FFT here.
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
  -- compute_cells_and_kzg_proofs_polynomialcoeff proves each `coset_for_cell(i)` on its own.
  --
  -- Here one FFT gives all the cells, and the FK20 method below gives all the proofs.
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
  --
  -- Lean's pool starts a new worker only when no worker is idle.
  --
  -- Spawned from a busy worker, the inner tasks then grow the pool.
  let shifts := (size + n - 1) / n - 1
  let proofs := (Task.spawn fun _ =>
    let tasks := (Array.range shifts).map fun e => Task.spawn fun _ =>
      let d := e + 1
      Bls.G1.msm (setup.g1Monomial.toArray.extract 0 (size - n * d))
        (polynomialCoeff.extract (n * d) size)
    let hs := tasks.map Task.get

    -- Phase 2: evaluate sum_d H_d * Y^(d - 1) at the 128-th roots of unity.
    --
    -- The bit reversal puts the proofs in cell order.
    let padded := hs ++ Array.replicate (CELLS_PER_EXT_BLOB - hs.size) Bls.G1.zero
    bitReversalPermutation (fftG1 padded (computeRootsOfUnity CELLS_PER_EXT_BLOB))).get
  return (cells, proofs.map compressG1)

/-- Compute the cells of a blob and their proofs.

The proofs come together, by the FK20 method. -/
def computeCellsAndKzgProofs (setup : TrustedSetup)
    (blob : Blob) : Except KzgError (Array Cell × Array KZGProof) := do
  -- compute_cells_and_kzg_proofs: `polynomial = blob_to_polynomial(blob)`.
  let polynomial ← blobToPolynomial blob
  -- `polynomial_coeff = polynomial_eval_to_coeff(polynomial)`.
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  -- `return compute_cells_and_kzg_proofs_polynomialcoeff(polynomial_coeff)`.
  computeCellsAndKzgProofsPolynomialcoeff setup polynomialCoeff

/-- Random challenge `r` used in the universal verification equation. -/
def computeVerifyCellKzgProofBatchChallenge
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : Fr :=
  -- compute_verify_cell_kzg_proof_batch_challenge starts from the domain tag.
  --
  -- `hashinput = RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN`.
  --
  -- Then 8 bytes each of the blob and cell sizes, `len(commitments)` and `len(cell_indices)`.
  let h := RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN
    ++ ⟨(Base.natToBytes 8 FIELD_ELEMENTS_PER_BLOB).toArray⟩
    ++ ⟨(Base.natToBytes 8 FIELD_ELEMENTS_PER_CELL).toArray⟩
    ++ ⟨(Base.natToBytes 8 commitments.size).toArray⟩
    ++ ⟨(Base.natToBytes 8 cellIndices.size).toArray⟩
  -- `for commitment in commitments: hashinput += commitment`.
  let h := commitments.foldl (init := h) fun h c => h ++ ⟨c.toArray⟩
  -- One entry per cell, from four arrays of one length, which the callers check.
  let cells := (commitmentIndices.zip cellIndices).zip (cosetsEvals.zip proofs)
  -- For each cell `k`: its commitment index and cell index as 8 bytes, its values, its proof.
  let h := cells.foldl (init := h) fun h ((commitmentIndex, cellIndex), (evals, proof)) =>
    let h := h ++ ⟨(Base.natToBytes 8 commitmentIndex).toArray⟩
    let h := h ++ ⟨(Base.natToBytes 8 cellIndex).toArray⟩
    let h := evals.foldl (init := h) fun h ce =>
      h ++ ⟨(blsFieldToBytes ce).toArray⟩
    h ++ ⟨proof.toArray⟩
  -- `return hash_to_bls_field(hashinput)`.
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
  -- verify_cell_kzg_proof_batch_impl: `assert len(commitment_indices) == len(cell_indices) == ...`.
  --
  -- The other two lengths in that assert are those of `cosets_evals` and `proofs`.
  if cellIndices.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "cellIndices" commitmentIndices.size cellIndices.size)
  if cosetsEvals.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size cosetsEvals.size)
  if proofs.size ≠ commitmentIndices.size then
    throw (.inputLengthMismatch "proofs" commitmentIndices.size proofs.size)
  -- `assert commitment_index < len(commitments)`, for each index.
  if commitmentIndices.any (· ≥ commitments.size) then
    let index := (commitmentIndices.find? (· ≥ commitments.size)).getD 0
    throw (.commitmentIndexOutOfBounds index commitments.size)
  -- `assert len(commitments) == len(set(commitments))`, checked here after the indices.
  if commitments.zipIdx.any (fun (c, i) => commitments.idxOf? c ≠ some i) then
    let repeated := commitments.zipIdx.find? (fun (c, i) => commitments.idxOf? c ≠ some i)
    throw (.duplicateCommitments ((repeated.map (·.2)).getD 0))

  -- The check is `pairing(LL, LR) = pairing(RL, [1])`, with `LL = sum_k r^k proofs[k]`.
  --
  -- `LR = [s^n]`, and `RL = RLC - RLI + RLP`, the three sums of steps 4.1 to 4.3.
  --
  -- Cell `k` has the shift `h_k` and the interpolation polynomial `I_k` of its values.
  --
  -- Commitment `i` has the weight `weights[i]`, the sum of `r^k` over its cells.
  --
  -- `r` hashes all the inputs, `s` is the secret of the setup, and `n` is 64, the size of a cell.

  let numCells := cellIndices.size
  let n := FIELD_ELEMENTS_PER_CELL
  let numCommitments := commitments.size

  -- Step 1: a challenge `r` and its powers `r^0, ..., r^(num_cells - 1)`.
  let r := computeVerifyCellKzgProofBatchChallenge
            commitments commitmentIndices cellIndices cosetsEvals proofs
  let rPowers := computePowers r numCells

  -- Step 2: `LL = sum_k r^k proofs[k]`.
  --
  -- The proofs are decoded once, for this sum and for RLP.
  let proofsG1 ← proofs.mapM uncompressG1
  let ll : G1 ← g1LincombPoints proofsG1 rPowers

  -- Step 3: `LR = [s^n]`.
  let lr : G2 := setup.g2Monomial[FIELD_ELEMENTS_PER_CELL]'(by decide)

  -- Step 4.1a: `weights[i]`, the sum of all `r^k` for which cell `k` has commitment `i`.
  --
  -- Each commitment index is checked above, so no `r^k` is lost.
  let weights : Array Fr := (commitmentIndices.zip rPowers).foldl
    (init := Array.replicate numCommitments Fr.zero)
    fun weights (i, rPower) => weights.modify i (· + rPower)

  -- Step 4.1b: `RLC = sum_i weights[i] commitments[i]`.
  let rlc : G1 ← g1LincombPoints (← commitments.mapM uncompressG1) weights

  -- `h_k = coset_shift_for_cell(cell_indices[k])`, for every cell.
  --
  -- The domain is computed once, not once per cell.
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  -- The shift of cell `i` is entry `64 i` of the domain, which exists exactly when `i < 128`.
  let shifts : Array Fr ← cellIndices.mapM fun cellIndex =>
    if h : n * cellIndex < domain.size then pure domain[n * cellIndex]
    else throw (.cellIndexOutOfBounds cellIndex)

  -- Step 4.2: `RLI = [sum_k r^k interpolation_poly_k(s)]`.
  --
  -- Each `I_k` comes from one inverse FFT over its coset, not from Lagrange interpolation.
  --
  -- That is the inverse DFT method the source recommends.
  --
  -- It comes from the post on the universal verification equation.
  let sumInterp : PolynomialCoeff ← (shifts.zip (cosetsEvals.zip rPowers)).foldlM
    (init := Array.replicate n Fr.zero)
    fun sumInterp (shift, evals, rPower) => do
      let interp ← interpolateCosetEvals shift evals
      let scaled ← multiplyPolynomialcoeff #[rPower] interp
      pure (addPolynomialcoeff sumInterp scaled)
  let rli : G1 ← g1LincombPoints (setup.g1Monomial.toArray.extract 0 n) sumInterp

  -- Step 4.3: `RLP = sum_k (r^k * h_k^n) proofs[k]`.
  let weightedRPowers : Array Fr :=
    Array.zipWith (fun rPower shift => rPower * shift ^ (Fr.ofNat n)) rPowers shifts
  let rlp : G1 ← g1LincombPoints proofsG1 weightedRPowers

  -- Step 4.4: `RL = RLC - RLI + RLP`.
  let rl : G1 := Bls.G1.add (Bls.G1.add rlc (Bls.G1.neg rli)) rlp

  -- Step 5: `pairing(LL, LR) = pairing(RL, [1])`, as `e(LL, LR) * e(RL, -[1]) = 1`.
  return Bls.pairingCheck #[
    (ll, lr),
    (rl, Bls.G2.neg (setup.g2Monomial[0]'(by decide)))
  ]

/-- Verify that a set of cells belong to their commitments.

Each cell comes with a commitment, a cell index and a proof.

The proof shows that the cell holds the values of the committed polynomial on its coset.

The check is the [universal verification equation][uve] of data availability sampling.

It removes repeated commitments, then runs the core check.

[uve]: https://ethresear.ch/t/a-universal-verification-equation-for-data-availability-sampling/13240
-/
def verifyCellKzgProofBatch (setup : TrustedSetup)
    (commitmentsBytes : Array Bytes48)
    (cellIndices : Array CellIndex)
    (cells : Array Cell)
    (proofsBytes : Array Bytes48) : Except KzgError Bool := do
  -- verify_cell_kzg_proof_batch: `assert len(commitments_bytes) == len(cells) == ...`.
  --
  -- The other two lengths in that assert are those of `proofs_bytes` and `cell_indices`.
  --
  -- The byte lengths of commitments, cells and proofs hold by their types.
  if cells.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cells" commitmentsBytes.size cells.size)
  if proofsBytes.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "proofsBytes" commitmentsBytes.size proofsBytes.size)
  if cellIndices.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cellIndices" commitmentsBytes.size cellIndices.size)

  -- `assert cell_index < CELLS_PER_EXT_BLOB`, for each index.
  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw (.cellIndexOutOfBounds ((cellIndices.find? (· ≥ CELLS_PER_EXT_BLOB)).getD 0))

  -- `deduplicated_commitments` and `commitment_indices`, in one scan over the short list.
  --
  -- Remove repeated commitments, keeping the first index.
  let (deduped, commitmentIndices) ←
    commitmentsBytes.zipIdx.foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array CommitmentIndex)))
      fun (deduped, commitmentIndices) (cb, i) => do
        -- `bytes_to_kzg_commitment(commitment_bytes)`, on every entry, repeated or not.
        --
        -- A repeated entry has the same bytes, so it gives the same result.
        let _ ← match bytesToKzgCommitment cb with
                | .ok c    => pure c
                | .error _ => throw (.invalidCommitment (some i))
        -- Find or append.
        match deduped.idxOf? cb with
        | some j => pure (deduped, commitmentIndices.push j)
        | none   => pure (deduped.push cb, commitmentIndices.push deduped.size)

  -- `cosets_evals = [cell_to_coset_evals(cell) for cell in cells]`.
  let cosetsEvals : Array CosetEvals ← cells.mapM fun c =>
    cellToCosetEvals c

  -- `proofs = [bytes_to_kzg_proof(proof_bytes) for proof_bytes in proofs_bytes]`.
  let proofs : Array KZGProof ← proofsBytes.zipIdx.mapM fun (pb, i) =>
    match bytesToKzgProof pb with
    | .ok p    => pure p
    | .error _ => throw (.invalidProof (some i))

  -- `return verify_cell_kzg_proof_batch_impl(...)`.
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
    out := out.push (Base.bytesToNat (b.extract (i*8) ((i+1)*8)).data.toList)
  return out

end EthLib.Cryptography.Kzg
