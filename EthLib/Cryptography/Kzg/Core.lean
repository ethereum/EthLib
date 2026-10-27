import EthLib.Cryptography.Bls
import EthLib.Cryptography.Kzg.Constants
import EthLib.Cryptography.Kzg.BitReversal
import EthLib.Cryptography.Kzg.Polynomials
import EthLib.Cryptography.Kzg.TrustedSetup
import EthLib.Cryptography.Kzg.Errors

/-!
# `Kzg.Core`

The blob-commitment surface of KZG. Public methods live in `KzgM`
(`ExceptT KzgError IO`) because they read the loaded trusted setup and
report typed domain errors; internal helpers that only manipulate field
elements remain pure.
-/

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open EthLib.Cryptography.Bls (G1 G2 Fr)

/-! ## Type aliases

`KZGCommitment` and `KZGProof` are `Bytes48` aliases, kept as
`ByteArray` for direct interop with public method signatures. -/

abbrev G1Point       := ByteArray
abbrev G2Point       := ByteArray
abbrev KZGCommitment := ByteArray
abbrev KZGProof      := ByteArray

/-! ## Validation -/

/-- Validate a commitment or a proof and return its point.

This is `validate_kzg_g1` from the Deneb polynomial commitments specification.

It is BLS public-key validation, except that the point at infinity is allowed.

The commitment to the zero polynomial is the point at infinity, so KZG must accept it.
-/
def validateKzgG1Point (b : Bytes48) : Except KzgError G1 :=
  -- The canonical infinity encoding is accepted as the identity.
  if b == G1_POINT_AT_INFINITY then .ok Bls.G1.zero
  -- Any other input must pass full public-key validation.
  else match Bls.G1.keyValidatePoint b with
  | .ok p    => .ok p
  | .error _ => .error .invalidG1Point

/-- BLS validation, allowing the point at infinity. -/
def validateKzgG1 (b : Bytes48) : Bool :=
  if b == G1_POINT_AT_INFINITY then true
  else (Bls.G1.keyValidate b).isOk

/-- Decompress 48 bytes into a point, or fail with an invalid-point error.

A failed decompression must stop the computation.

Falling back to a default point would silently replace the input with the point at infinity.
-/
def uncompressG1 (b : Bytes48) : KzgM G1 :=
  match Bls.G1.uncompress b with
  | .ok g    => pure g
  | .error _ => throw .invalidG1Point

/-- Validate untrusted bytes as a `KZGCommitment`. -/
def bytesToKzgCommitment (b : Bytes48) : Except KzgError KZGCommitment :=
  if validateKzgG1 b then .ok b else .error (.invalidCommitment none)

/-- Validate untrusted bytes as a `KZGProof`. -/
def bytesToKzgProof (b : Bytes48) : Except KzgError KZGProof :=
  if validateKzgG1 b then .ok b else .error (.invalidProof none)

/-- Fiat-Shamir challenge for a (blob, commitment) pair. -/
def computeChallenge (blob : Blob) (commitment : KZGCommitment) : Fr :=
  let degreePoly := intToBytesBE FIELD_ELEMENTS_PER_BLOB 16
  let data := FIAT_SHAMIR_PROTOCOL_DOMAIN ++ degreePoly ++ blob ++ commitment
  Fr.hashToBlsField data

/-- The linear combination `sum_i scalars_i * points_i` of decoded points.

This is `g1_lincomb` from the Deneb polynomial commitments specification, without the decoding step.

Callers that already hold points skip a compress and decompress round trip.
-/
def g1LincombPoints
    (points : Array G1) (scalars : Array Fr) : KzgM G1 := do
  if points.size ≠ scalars.size then
    throw (.lincombLengthMismatch points.size scalars.size)
  if points.size = 0 then
    return Bls.G1.zero
  return Bls.G1.msm points scalars

/-- BLS multi-scalar multiplication in G1, on compressed-point inputs. -/
def g1Lincomb
    (points : Array KZGCommitment) (scalars : Array Fr) : KzgM KZGCommitment := do
  if points.size ≠ scalars.size then
    throw (.lincombLengthMismatch points.size scalars.size)
  if points.size = 0 then
    return Bls.G1.compress Bls.G1.zero
  -- An undecodable 48-byte input must fail: the `Inhabited` default of
  -- `G1` is the point at infinity, so it would silently drop out of the
  -- multi-scalar multiplication.
  let pointsG1 ← points.mapM uncompressG1
  return Bls.G1.compress (Bls.G1.msm pointsG1 scalars)

/-- Given `y == p(z)` for a polynomial `p(x)`, compute `q(z)`: the KZG
quotient polynomial evaluated at `z` for the special case where `z` is in
roots of unity.

For more details, read
https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html section
"Dividing when one of the points is zero". The code below computes q(x_m)
for the roots of unity special case. -/
private def computeQuotientEvalWithinDomain
    (z : Fr) (polynomial : Polynomial) (y : Fr)
    : Fr :=
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  -- One batch inversion gives every `1 / (z * (z - omega_i))`.
  -- The skipped term has denominator zero, which inverts to zero and is never read.
  let inverses := Fr.batchInverse (domain.map fun omega_i => z * (z - omega_i))
  (Array.range domain.size).foldl (init := Fr.zero) fun result i =>
    let omega_i := domain[i]!
    if omega_i == z then
      result
    else
      let f_i := polynomial[i]! - y
      let numerator := f_i * omega_i
      -- `z` is a root of unity here (the caller only reaches this function
      -- when `z` is in the domain), so `z ≠ 0`; and `omega_i ≠ z` by the
      -- skip above — the denominator is nonzero.
      result + numerator * inverses[i]!

/-- Returns the KZG proof at `z` and the evaluation `y = p(z)`. -/
private def computeKzgProofImpl
    (polynomial : Polynomial) (z : Fr) : KzgM (KZGProof × Fr) := do
  let setup ← TrustedSetup.get!
  let g1LagrangeBrp := bitReversalPermutation setup.g1Lagrange
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB

  -- For all x_i, compute p(x_i) - p(z).
  let y ← evaluatePolynomialInEvaluationForm polynomial z
  let polynomialShifted := polynomial.map (· - y)

  -- For all x_i, compute (x_i - z), and all their inverses with one inversion.
  let denominatorPoly := domain.map (· - z)
  let inverses := Fr.batchInverse denominatorPoly

  -- Quotient polynomial directly in evaluation form.
  let quotient : Array Fr := Array.ofFn (n := FIELD_ELEMENTS_PER_BLOB) fun i =>
    let a := polynomialShifted[i.val]!
    let b := denominatorPoly[i.val]!
    if b.isZero then
      -- z lands on a root of unity; use the special-case formula.
      computeQuotientEvalWithinDomain domain[i.val]! polynomial y
    else
      a * inverses[i.val]!

  let proofG1 ← g1LincombPoints g1LagrangeBrp quotient
  return (Bls.G1.compress proofG1, y)

/-- Compute a KZG proof at `z` for the polynomial represented by `blob`.
Returns `(proof, y_bytes)`, where `y_bytes` is the 32-byte big-endian
encoding of `p(z)`. -/
def computeKzgProof (blob : Blob) (zBytes : Bytes32) : KzgM (KZGProof × Bytes32) := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  if zBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw (.badFieldElementSize zBytes.size)
  let polynomial ← blobToPolynomial blob
  let z ← bytesToBlsField zBytes
  let (proof, y) ← computeKzgProofImpl polynomial z
  return (proof, blsFieldToBytes y)

/-- Verify a KZG proof that `p(z) == y`, where `p(x)` is the polynomial
committed to in `commitmentG1`. Checks the pairing equation
`e(P - [y], -[1]) * e(proof, [s] - [z]) == 1`. -/
private def verifyKzgProofImpl
    (commitmentG1 : G1) (z y : Fr) (proofG1 : G1)
    : KzgM Bool := do
  let setup ← TrustedSetup.get!
  let s := setup.g2Monomial[1]!
  let X_minus_z : G2 := Bls.G2.add s (Bls.G2.mul Bls.G2.generator (-z))
  let P_minus_y : G1 := Bls.G1.add commitmentG1 (Bls.G1.mul Bls.G1.generator (-y))
  let pairs : Array (G1 × G2) := #[
    (P_minus_y, Bls.G2.neg Bls.G2.generator),
    (proofG1, X_minus_z)
  ]
  return Bls.pairingCheck pairs

/-- Verify a KZG proof, taking inputs as raw bytes. -/
def verifyKzgProof
    (commitmentBytes : Bytes48) (zBytes yBytes : Bytes32) (proofBytes : Bytes48)
    : KzgM Bool := do
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw (.badCommitmentSize commitmentBytes.size)
  if zBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw (.badFieldElementSize zBytes.size)
  if yBytes.size ≠ BYTES_PER_FIELD_ELEMENT then
    throw (.badFieldElementSize yBytes.size)
  if proofBytes.size ≠ BYTES_PER_PROOF then
    throw (.badProofSize proofBytes.size)
  let commitmentG1 ← match validateKzgG1Point commitmentBytes with
                     | .ok c    => pure c
                     | .error _ => throw (.invalidCommitment none)
  let proofG1 ← match validateKzgG1Point proofBytes with
                | .ok p    => pure p
                | .error _ => throw (.invalidProof none)
  let z ← bytesToBlsField zBytes
  let y ← bytesToBlsField yBytes
  verifyKzgProofImpl commitmentG1 z y proofG1

/-- Verify multiple KZG proofs efficiently using a random linear combination. -/
private def verifyKzgProofBatch
    (commitments : Array KZGCommitment)
    (commitmentsG1 : Array G1)
    (zs ys : Array Fr)
    (proofs : Array KZGProof)
    (proofsG1 : Array G1) : KzgM Bool := do
  if zs.size ≠ commitments.size then
    throw (.inputLengthMismatch "zs" commitments.size zs.size)
  if ys.size ≠ commitments.size then
    throw (.inputLengthMismatch "ys" commitments.size ys.size)
  if proofs.size ≠ commitments.size then
    throw (.inputLengthMismatch "proofs" commitments.size proofs.size)
  let setup ← TrustedSetup.get!

  -- Random challenge: deterministic via Fiat-Shamir.
  let degreePoly := intToBytesBE FIELD_ELEMENTS_PER_BLOB 8
  let numCommitments := intToBytesBE commitments.size 8
  let data := (Array.range commitments.size).foldl
    (init := RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ++ degreePoly ++ numCommitments)
    fun data i => data
        ++ commitments[i]!
        ++ blsFieldToBytes zs[i]!
        ++ blsFieldToBytes ys[i]!
        ++ proofs[i]!
  let r := Fr.hashToBlsField data
  let rPowers := computePowers r commitments.size

  -- proof_lincomb = Σ_i r^i · proof_i
  let proofLincombG1 ← g1LincombPoints proofsG1 rPowers
  -- proof_z_lincomb = Σ_i (z_i · r^i) · proof_i
  let zRPowers := Array.ofFn (n := zs.size) fun i => zs[i.val]! * rPowers[i.val]!
  let proofZLincombG1 ← g1LincombPoints proofsG1 zRPowers

  -- C_minus_ys[i] = commitment_i - [y_i]
  let cMinusYs : Array G1 := Array.ofFn (n := commitments.size) fun i =>
    Bls.G1.add commitmentsG1[i.val]!
               (Bls.G1.mul Bls.G1.generator (-ys[i.val]!))
  let cMinusYLincombG1 ← g1LincombPoints cMinusYs rPowers

  let s := setup.g2Monomial[1]!
  let pairs : Array (G1 × G2) := #[
    ( proofLincombG1, Bls.G2.neg s ),
    ( Bls.G1.add cMinusYLincombG1 proofZLincombG1
    , Bls.G2.generator )
  ]
  return Bls.pairingCheck pairs

/-- Compute a KZG commitment from a blob. -/
def blobToKzgCommitment (blob : Blob) : KzgM KZGCommitment := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  let setup ← TrustedSetup.get!
  let polynomial ← blobToPolynomial blob
  let lagrangeBrp := bitReversalPermutation setup.g1Lagrange
  let commitmentG1 ← g1LincombPoints lagrangeBrp polynomial
  return Bls.G1.compress commitmentG1

/-- Compute the KZG proof verifying `blob` against `commitment`. Does
not check that `commitment` is correct for `blob`. -/
def computeBlobKzgProof (blob : Blob) (commitmentBytes : Bytes48) : KzgM KZGProof := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw (.badCommitmentSize commitmentBytes.size)
  let commitment ← bytesToKzgCommitment commitmentBytes
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitment
  let (proof, _) ← computeKzgProofImpl polynomial evaluationChallenge
  return proof

/-- Verify that `blob` corresponds to `commitment` via `proof`. -/
def verifyBlobKzgProof
    (blob : Blob) (commitmentBytes : Bytes48) (proofBytes : Bytes48)
    : KzgM Bool := do
  if blob.size ≠ BYTES_PER_BLOB then
    throw (.badBlobSize blob.size)
  if commitmentBytes.size ≠ BYTES_PER_COMMITMENT then
    throw (.badCommitmentSize commitmentBytes.size)
  if proofBytes.size ≠ BYTES_PER_PROOF then
    throw (.badProofSize proofBytes.size)
  let commitmentG1 ← match validateKzgG1Point commitmentBytes with
                     | .ok c    => pure c
                     | .error _ => throw (.invalidCommitment none)
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitmentBytes
  let y ← evaluatePolynomialInEvaluationForm polynomial evaluationChallenge
  let proofG1 ← match validateKzgG1Point proofBytes with
                | .ok p    => pure p
                | .error _ => throw (.invalidProof none)
  verifyKzgProofImpl commitmentG1 evaluationChallenge y proofG1

/-- Verify a batch of (blob, commitment, proof) triples. Returns `true`
for the empty input. -/
def verifyBlobKzgProofBatch
    (blobs : Array Blob)
    (commitmentsBytes : Array Bytes48)
    (proofsBytes : Array Bytes48) : KzgM Bool := do
  if commitmentsBytes.size ≠ blobs.size then
    throw (.inputLengthMismatch "commitmentsBytes" blobs.size commitmentsBytes.size)
  if proofsBytes.size ≠ blobs.size then
    throw (.inputLengthMismatch "proofsBytes" blobs.size proofsBytes.size)

  let (commitments, commitmentsG1, challenges, ys, proofs, proofsG1) ←
    (Array.range blobs.size).foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array G1), (#[] : Array Fr),
                (#[] : Array Fr), (#[] : Array KZGProof), (#[] : Array G1)))
      fun (commitments, commitmentsG1, challenges, ys, proofs, proofsG1) i => do
        let blob := blobs[i]!
        let cb := commitmentsBytes[i]!
        let pb := proofsBytes[i]!
        if blob.size ≠ BYTES_PER_BLOB then
          throw (.badBlobSize blob.size)
        if cb.size ≠ BYTES_PER_COMMITMENT then
          throw (.badCommitmentSize cb.size)
        if pb.size ≠ BYTES_PER_PROOF then
          throw (.badProofSize pb.size)

        let commitmentG1 ← match validateKzgG1Point cb with
                           | .ok c    => pure c
                           | .error _ => throw (.invalidCommitment (some i))
        let proofG1 ← match validateKzgG1Point pb with
                      | .ok p    => pure p
                      | .error _ => throw (.invalidProof (some i))

        let polynomial ← blobToPolynomial blob
        let challenge := computeChallenge blob cb
        let y ← evaluatePolynomialInEvaluationForm polynomial challenge

        pure (commitments.push cb, commitmentsG1.push commitmentG1,
              challenges.push challenge, ys.push y, proofs.push pb, proofsG1.push proofG1)

  verifyKzgProofBatch commitments commitmentsG1 challenges ys proofs proofsG1

end EthLib.Cryptography.Kzg
