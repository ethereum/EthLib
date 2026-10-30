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

Cell proofs over a Reed-Solomon-extended blob. The extended
polynomial is split into `CELLS_PER_EXT_BLOB` cosets of
`FIELD_ELEMENTS_PER_CELL` evaluations each; each cell carries an
independent KZG multi-evaluation proof, so verifiers can sample any
subset of cells without downloading the full blob.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open EthLib.Cryptography.Bls (G1 G2 Fr)

/-! ## Type aliases -/

abbrev Cell             := ByteArray
abbrev CellIndex        := Nat
abbrev CommitmentIndex  := Nat
abbrev Coset            := Array Fr
abbrev CosetEvals       := Array Fr

/-- Convert an untrusted `Cell` into a trusted `CosetEvals`. -/
def cellToCosetEvals (cell : Cell) : Except KzgError CosetEvals := do
  if cell.size ≠ BYTES_PER_CELL then
    throw (.badCellSize cell.size)
  (Array.range FIELD_ELEMENTS_PER_CELL).mapM fun i =>
    let s := i * BYTES_PER_FIELD_ELEMENT
    let e := (i + 1) * BYTES_PER_FIELD_ELEMENT
    match bytesToBlsField (cell.extract s e) with
    | .ok f    => pure f
    | .error _ => throw (.invalidFieldElement (some i))

/-- Convert a trusted `CosetEvals` back into an untrusted `Cell`. -/
def cosetEvalsToCell (cosetEvals : CosetEvals) : Cell :=
  (Array.range FIELD_ELEMENTS_PER_CELL).foldl
    (init := ByteArray.empty)
    fun bytes i => bytes ++ blsFieldToBytes cosetEvals[i]!

/-! ## Cell cosets -/

/-- Get the coset for a given `cellIndex`.
Precisely, consider the group of roots of unity of order
`FIELD_ELEMENTS_PER_CELL * CELLS_PER_EXT_BLOB`.
Let `G = {1, g, g^2, ...}` denote its subgroup of order `FIELD_ELEMENTS_PER_CELL`.
Then, the coset is defined as `h * G = {h, hg, hg^2, ...}`.
This function, returns the coset. -/
def cosetForCell (cellIndex : CellIndex) : Except KzgError Coset := do
  if cellIndex ≥ CELLS_PER_EXT_BLOB then
    throw .cellIndexOutOfBounds
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  let start := FIELD_ELEMENTS_PER_CELL * cellIndex
  return Array.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i => domain[start + i.val]!

/-- Interpolate one cell: the polynomial of degree below 64 with the values `evals` on the coset of shift `h`.

The coset is a shifted FFT domain, in bit-reversed order.

```text
    point j    : h * v^(rev(j))          v a 64-th root of unity, rev the 6-bit reversal
    J(Y)       : I(h * Y)                so J takes the values evals on the 64-th roots
    J          : IFFT(brp(evals))
    I_i        : J_i * h^(-i)
```

It returns the same polynomial as Lagrange interpolation.

Lagrange needs `64 * 63` field inversions.

This needs one inverse FFT and one inversion. -/
def interpolateCosetEvals (h : Fr) (evals : CosetEvals) : Except KzgError PolynomialCoeff := do
  if evals.size ≠ FIELD_ELEMENTS_PER_CELL then
    throw (.inputLengthMismatch "ys" FIELD_ELEMENTS_PER_CELL evals.size)
  let j := fftField (bitReversalPermutation evals) (computeRootsOfUnity FIELD_ELEMENTS_PER_CELL) (inv := true)
  return shiftVals j h.inverse

/-- The values of a polynomial on the extended domain, in bit-reversed order.

Cell `i` holds the values at `cosetForCell i`.

That coset is the `i`-th block of 64 points of the bit-reversed domain.

```text
    values : [ cell 0: 64 | cell 1: 64 | ... | cell 127: 64 ]
```

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
def computeCells (blob : Blob) : KzgM (Array Cell) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let polynomial ← blobToPolynomial blob
  return cellsOfExtendedEvaluations (extendedEvaluations (polynomialEvalToCoeff polynomial))

/-- Compute cells and proofs for a polynomial in coefficient form.

The specification proves each cell on its own.

It divides `f` by the cell's vanishing polynomial, then commits to the quotient.

That costs one multi-scalar multiplication of 4032 points per cell.

The 128 quotients share their structure, so this computes them together.

```text
    cell k   : the coset h_k * mu_64
    Z_k      : X^64 - c_k,   with c_k = h_k^64
    q_k      : f / Z_k = sum_{d >= 1} c_k^(d - 1) * (f >> 64 d)
    proof_k  : [q_k(s)] = sum_{d = 1}^{63} c_k^(d - 1) * H_d
    H_d      : sum_i f_(i + 64 d) * [s^i]

    (f >> m)_i = f_(i + m)
```

The points `H_d` do not depend on the cell.

So 63 multi-scalar multiplications serve all 128 proofs.

Each `c_k` is a 128-th root of unity, taken in bit-reversed order.

So the proofs are the values of `sum_d H_d * Y^(d - 1)` at those roots.

One FFT in G1 computes them all.

This is the Toeplitz structure of FK20.

See Feist and Khovratovich, "Fast amortized KZG proofs", ePrint 2023/033.

The polynomial has at most 4096 coefficients, the size of the monomial setup. -/
def computeCellsAndKzgProofsPolynomialcoeff
    (polynomialCoeff : PolynomialCoeff) : KzgM (Array Cell × Array KZGProof) := do
  let setup ← TrustedSetup.get!
  let n := FIELD_ELEMENTS_PER_CELL
  let size := polynomialCoeff.size
  let cells := cellsOfExtendedEvaluations (extendedEvaluations polynomialCoeff)

  -- Phase 1: H_d for each shift d that leaves a coefficient.
  --
  --     4096 coefficients → d = 1, ..., 63 → H_d sums 4096 - 64 d points
  --
  -- The sums are independent, so each runs as its own task.
  -- Both slices have `size - n * d` entries, so the multi-scalar multiplication sees no length mismatch.
  --
  -- Both phases run inside one task.
  -- Lean's pool starts a new worker only when no worker is idle.
  -- Spawned from a busy worker, the inner tasks then grow the pool.
  let shifts := (size + n - 1) / n - 1
  let proofs := (Task.spawn fun _ =>
    let tasks := (Array.range shifts).map fun e => Task.spawn fun _ =>
      let d := e + 1
      Bls.G1.msm (setup.g1Monomial.extract 0 (size - n * d)) (polynomialCoeff.extract (n * d) size)
    let hs := tasks.map Task.get

    -- Phase 2: evaluate sum_d H_d * Y^(d - 1) at the 128-th roots of unity.
    -- The bit reversal puts the proofs in cell order.
    let padded := hs ++ Array.replicate (CELLS_PER_EXT_BLOB - hs.size) Bls.G1.zero
    bitReversalPermutation (fftG1 padded (computeRootsOfUnity CELLS_PER_EXT_BLOB))).get
  return (cells, proofs.map Bls.G1.compress)

/-- Compute all cell proofs for an extended blob. Naive O(n²);
optimal implementations use FK20. -/
def computeCellsAndKzgProofs
    (blob : Blob) : KzgM (Array Cell × Array KZGProof) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let polynomial ← blobToPolynomial blob
  let polynomialCoeff := polynomialEvalToCoeff polynomial
  computeCellsAndKzgProofsPolynomialcoeff polynomialCoeff

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
  let h := commitments.foldl (init := h) fun h c => h ++ c
  let h := (Array.range cosetsEvals.size).foldl (init := h) fun h k =>
    let h := h ++ intToBytesBE commitmentIndices[k]! 8
    let h := h ++ intToBytesBE cellIndices[k]! 8
    let h := cosetsEvals[k]!.foldl (init := h) fun h ce =>
      h ++ blsFieldToBytes ce
    h ++ proofs[k]!
  Fr.hashToBlsField h

/-- Helper: Verify that a set of cells belong to their corresponding commitment.

Given a list of `commitments` (which contains no duplicates) and four lists
representing tuples of (`commitmentIndex`, `cellIndex`, `evals`, `proof`), the
function verifies `proof` which shows that `evals` are the evaluations of the
polynomial associated with `commitments[commitmentIndex]`, evaluated over the
domain specified by `cellIndex`.

This function is the internal implementation of `verifyCellKzgProofBatch`. -/
def verifyCellKzgProofBatchImpl
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) : KzgM Bool := do
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
  if (Array.range commitments.size).any
      (fun i => commitments.idxOf? commitments[i]! ≠ some i) then
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

  let setup ← TrustedSetup.get!
  let numCells := cellIndices.size
  let n := FIELD_ELEMENTS_PER_CELL
  let numCommitments := commitments.size

  -- Step 1: r and r^0..r^(num_cells-1).
  let r := computeVerifyCellKzgProofBatchChallenge
            commitments commitmentIndices cellIndices cosetsEvals proofs
  let rPowers := computePowers r numCells

  -- Step 2: LL = Σ_k r^k proofs[k].
  let ll : G1 ← uncompressG1 (← g1Lincomb proofs rPowers)

  -- Step 3: LR = [s^n].
  let lr : G2 := setup.g2Monomial[n]!

  -- Step 4.1: weights[i] = Σ_{k : commitmentIndices[k] = i} r^k.
  -- Note: we do that by iterating over all k and updating the correct
  -- weights[i] accordingly.
  let weights : Array Fr := (Array.range numCells).foldl
    (init := Array.replicate numCommitments Fr.zero)
    fun weights k =>
      let i := commitmentIndices[k]!
      weights.set! i (weights[i]! + rPowers[k]!)

  -- Step 4.1b: RLC = Σ_i weights[i] commitments[i].
  let rlc : G1 ← uncompressG1 (← g1Lincomb commitments weights)

  -- The coset shift h_k of every cell.
  -- The domain is computed once, not once per cell.
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  let shifts : Array Fr ← cellIndices.mapM fun cellIndex => do
    if cellIndex ≥ CELLS_PER_EXT_BLOB then
      throw .cellIndexOutOfBounds
    pure domain[n * cellIndex]!

  -- Step 4.2: RLI = [Σ_k r^k I_k(s)].
  -- Each I_k comes from one inverse FFT over its coset.
  -- It is the IDFT method of the blog post linked in `verifyCellKzgProofBatch`.
  let sumInterp : PolynomialCoeff ← (Array.range numCells).foldlM
    (init := Array.replicate n Fr.zero)
    fun sumInterp k => do
      let interp ← interpolateCosetEvals shifts[k]! cosetsEvals[k]!
      let scaled ← multiplyPolynomialcoeff #[rPowers[k]!] interp
      pure (addPolynomialcoeff sumInterp scaled)
  let rli : G1 ← g1LincombPoints (setup.g1Monomial.extract 0 n) sumInterp

  -- Step 4.3: RLP = Σ_k (r^k * h_k^n) proofs[k].
  let weightedRPowers : Array Fr := (Array.range numCells).map fun k =>
    rPowers[k]! * (shifts[k]! ^ (Fr.ofNat n))
  let rlp : G1 ← uncompressG1 (← g1Lincomb proofs weightedRPowers)

  -- Step 4.4: RL = RLC - RLI + RLP.
  let rl : G1 := Bls.G1.add (Bls.G1.add rlc (Bls.G1.neg rli)) rlp

  -- Step 5: pairing(LL, LR) = pairing(RL, [1]).
  return Bls.pairingCheck #[
    (ll, lr),
    (rl, Bls.G2.neg setup.g2Monomial[0]!)
  ]

/-- Verify that a set of cells belong to their corresponding commitments.

Given four lists representing tuples of (`commitment`, `cellIndex`, `cell`,
`proof`), the function verifies `proof` which shows that `cell` are the
evaluations of the polynomial associated with `commitment`, evaluated over the
domain specified by `cellIndex`.

This function implements the universal verification equation that has been
introduced here:
https://ethresear.ch/t/a-universal-verification-equation-for-data-availability-sampling/13240

Deduplicates `commitmentsBytes` and forwards into
`verifyCellKzgProofBatchImpl`. -/
def verifyCellKzgProofBatch
    (commitmentsBytes : Array Bytes48)
    (cellIndices : Array CellIndex)
    (cells : Array Cell)
    (proofsBytes : Array Bytes48) : KzgM Bool := do

  if cells.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cells" commitmentsBytes.size cells.size)
  if proofsBytes.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "proofsBytes" commitmentsBytes.size proofsBytes.size)
  if cellIndices.size ≠ commitmentsBytes.size then
    throw (.inputLengthMismatch "cellIndices" commitmentsBytes.size cellIndices.size)

  if let some cb := commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT) then
    throw (.badCommitmentSize cb.size)
  if cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) then
    throw .cellIndexOutOfBounds
  if let some c := cells.find? (fun c => c.size != BYTES_PER_CELL) then
    throw (.badCellSize c.size)
  if let some pb := proofsBytes.find? (fun pb => pb.size != BYTES_PER_PROOF) then
    throw (.badProofSize pb.size)

  -- Deduplicate commitments while preserving the index of first occurrence.
  -- We use a simple linear scan (`idxOf?`); the input list of commitments
  -- tends to be short relative to the cell list.
  let (deduped, commitmentIndices) ←
    (Array.range commitmentsBytes.size).foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array CommitmentIndex)))
      fun (deduped, commitmentIndices) i => do
        let cb := commitmentsBytes[i]!
        -- Validate (also acts as `bytes_to_kzg_commitment`).
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
  let proofs : Array KZGProof ← (Array.range proofsBytes.size).mapM fun i =>
    match bytesToKzgProof proofsBytes[i]! with
    | .ok p    => pure p
    | .error _ => throw (.invalidProof (some i))

  verifyCellKzgProofBatchImpl deduped commitmentIndices cellIndices cosetsEvals proofs

/-- Decode a buffer of packed indices.

Each index is 8 bytes, big-endian:

```text
    [ index_0: 8 | index_1: 8 | ... | index_(n-1): 8 ]
```

The Python wrapper packs index arrays this way, so the C exports take only byte arrays.
It is pure parsing, so it lives in the specification, where the proofs can reach it, and the exports call it.

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
