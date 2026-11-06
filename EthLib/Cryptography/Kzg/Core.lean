module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.BitReversal
public import EthLib.Cryptography.Kzg.Polynomials
public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Kzg.Errors

/-!
# `Kzg.Core`

The blob-commitment surface of KZG.

EIP-4844 adds these operations at the Dencun fork.

Each operation that reads the trusted setup takes it as its first argument.

Each operation that can reject its input returns `Except KzgError`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open EthLib.Base (Bytes32)
open EthLib.Cryptography.Bls (G1 G2 Fr)

/-! ## Type aliases -/

/-- A commitment: a compressed `G1` point. -/
abbrev KZGCommitment := Bytes48

/-- A proof: a compressed `G1` point. -/
abbrev KZGProof := Bytes48

/-- The 48-byte compressed encoding of a point. -/
def compressG1 (p : G1) : Bytes48 := ⟨(Bls.G1.compress p).data, Bls.G1.size_compress p⟩

/-! ## Validation -/

/-- Validate a commitment or a proof and return its point.

It is BLS public-key validation, except that the point at infinity is allowed.

The commitment to the zero polynomial is the point at infinity, so KZG must accept it.
-/
def validateKzgG1Point (b : Bytes48) : Except KzgError G1 :=
  -- The canonical infinity encoding is accepted as the identity.
  if b == G1_POINT_AT_INFINITY then .ok Bls.G1.zero
  -- Any other input must pass full public-key validation.
  else match Bls.G1.keyValidatePoint ⟨b.toArray⟩ with
  | .ok p    => .ok p
  | .error _ => .error .invalidG1Point

/-- BLS validation, allowing the point at infinity. -/
def validateKzgG1 (b : Bytes48) : Bool :=
  if b == G1_POINT_AT_INFINITY then true
  else (Bls.G1.keyValidate ⟨b.toArray⟩).isOk

/-- Decompress 48 bytes into a point, or fail with an invalid-point error.

A failed decompression must stop the computation.

Falling back to a default point would silently replace the input with the point at infinity.
-/
def uncompressG1 (b : Bytes48) : Except KzgError G1 :=
  match Bls.G1.uncompress ⟨b.toArray⟩ with
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
  let data := FIAT_SHAMIR_PROTOCOL_DOMAIN ++ degreePoly ++ ⟨blob.toArray⟩ ++ ⟨commitment.toArray⟩
  Fr.hashToBlsField data

/-- The linear combination `sum_i scalars_i * points_i` of decoded points.

The setup and the inputs are decoded once, so no point goes through bytes in between.
-/
def g1LincombPoints
    (points : Array G1) (scalars : Array Fr) : Except KzgError G1 := do
  if points.size ≠ scalars.size then
    throw (.lincombLengthMismatch points.size scalars.size)
  if points.size = 0 then
    return Bls.G1.zero
  return Bls.G1.msm points scalars

/-- The quotient `q(z)` of the KZG proof, given `y = p(z)`, when `z` is a root of unity.

The general quotient divides by zero at such a `z`, so this case has its own formula.

It is the section "Dividing when one of the points is zero" of
<https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html>. -/
def computeQuotientEvalWithinDomain
    (z : Fr) (polynomial : Polynomial) (y : Fr)
    : Fr :=
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  -- One batch inversion gives every `1 / (z * (z - omega_i))`.
  -- The skipped term has denominator zero, which inverts to zero and is never read.
  let inverses := Fr.batchInverse (domain.map fun omega_i => z * (z - omega_i))
  -- The caller passes 4096 values, so the zip drops no entry.
  ((domain.zip polynomial).zip inverses).foldl (init := Fr.zero)
    fun result ((omega_i, p_i), inverse_i) =>
      if omega_i == z then
        result
      else
        let f_i := p_i - y
        let numerator := f_i * omega_i
        -- Here `z` is in the domain, so `z ≠ 0`, and the skip gives `omega_i ≠ z`.
        result + numerator * inverse_i

/-- Returns the KZG proof at `z` and the evaluation `y = p(z)`. -/
def computeKzgProofImpl (setup : TrustedSetup)
    (polynomial : Polynomial) (z : Fr) : Except KzgError (KZGProof × Fr) := do
  let g1LagrangeBrp := setup.g1LagrangeBrp.toArray
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB

  -- For all x_i, compute p(x_i) - p(z).
  let y ← evaluatePolynomialInEvaluationForm polynomial z
  let polynomialShifted := polynomial.map (· - y)

  -- For all x_i, compute (x_i - z), and all their inverses with one inversion.
  let denominatorPoly := domain.map (· - z)
  let inverses := Fr.batchInverse denominatorPoly

  -- The quotient in evaluation form, over the 4096 values that the evaluation above checked.
  let quotient : Array Fr :=
    (domain.zip (polynomialShifted.zip inverses)).map fun (omega_i, a, inverse_i) =>
      if (omega_i - z).isZero then
        -- `z` is the root of unity `omega_i`, so the special formula applies.
        computeQuotientEvalWithinDomain omega_i polynomial y
      else
        a * inverse_i

  let proofG1 ← g1LincombPoints g1LagrangeBrp quotient
  return (compressG1 proofG1, y)

/-- The KZG proof at `z` for the polynomial of a blob, with the value `p(z)`.

The value comes as 32 big-endian bytes. -/
def computeKzgProof (setup : TrustedSetup) (blob : Blob) (zBytes : Bytes32) :
    Except KzgError (KZGProof × Bytes32) := do
  let polynomial ← blobToPolynomial blob
  let z ← bytesToBlsField zBytes
  let (proof, y) ← computeKzgProofImpl setup polynomial z
  return (proof, blsFieldToBytes y)

/-- Verify a KZG proof that `p(z) == y`, given only the setup point `[s]_2`.

It checks `e(P - [y], -[1]) * e(proof, [s] - [z]) == 1`, where `P` commits to `p`.

A caller that holds only `[s]_2`, such as the point evaluation precompile, can use it. -/
def verifyKzgProofWith (s : G2)
    (commitmentG1 : G1) (z y : Fr) (proofG1 : G1) : Bool :=
  let X_minus_z : G2 := Bls.G2.add s (Bls.G2.mul Bls.G2.generator (-z))
  let P_minus_y : G1 := Bls.G1.add commitmentG1 (Bls.G1.mul Bls.G1.generator (-y))
  let pairs : Array (G1 × G2) := #[
    (P_minus_y, Bls.G2.neg Bls.G2.generator),
    (proofG1, X_minus_z)
  ]
  Bls.pairingCheck pairs

/-- Verify a KZG proof that `p(z) == y` for the committed polynomial `p`. -/
def verifyKzgProofImpl (setup : TrustedSetup)
    (commitmentG1 : G1) (z y : Fr) (proofG1 : G1) : Bool :=
  verifyKzgProofWith (setup.g2Monomial[1]'(by decide)) commitmentG1 z y proofG1

/-- Verify a KZG proof, taking inputs as raw bytes. -/
def verifyKzgProof (setup : TrustedSetup)
    (commitmentBytes : Bytes48) (zBytes yBytes : Bytes32) (proofBytes : Bytes48)
    : Except KzgError Bool := do
  let commitmentG1 ← match validateKzgG1Point commitmentBytes with
                     | .ok c    => pure c
                     | .error _ => throw (.invalidCommitment none)
  let proofG1 ← match validateKzgG1Point proofBytes with
                | .ok p    => pure p
                | .error _ => throw (.invalidProof none)
  let z ← bytesToBlsField zBytes
  let y ← bytesToBlsField yBytes
  return verifyKzgProofImpl setup commitmentG1 z y proofG1

/-- The Fiat-Shamir challenge of a batch of openings.

It hashes the domain, the degree bound, the number of openings, and each opening in order. -/
def computeVerifyKzgProofBatchChallenge (commitments : Array KZGCommitment) (zs ys : Array Fr)
    (proofs : Array KZGProof) : Fr :=
  let degreePoly := intToBytesBE FIELD_ELEMENTS_PER_BLOB 8
  let numCommitments := intToBytesBE commitments.size 8
  let data := ((commitments.zip zs).zip (ys.zip proofs)).foldl
    (init := RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ++ degreePoly ++ numCommitments)
    fun data ((commitment, z), (y, proof)) => data
        ++ ⟨commitment.toArray⟩
        ++ ⟨(blsFieldToBytes z).toArray⟩
        ++ ⟨(blsFieldToBytes y).toArray⟩
        ++ ⟨proof.toArray⟩
  Fr.hashToBlsField data

/-- Verify multiple KZG proofs efficiently using a random linear combination. -/
def verifyKzgProofBatch (setup : TrustedSetup)
    (commitments : Array KZGCommitment)
    (commitmentsG1 : Array G1)
    (zs ys : Array Fr)
    (proofs : Array KZGProof)
    (proofsG1 : Array G1) : Except KzgError Bool := do
  if zs.size ≠ commitments.size then
    throw (.inputLengthMismatch "zs" commitments.size zs.size)
  if ys.size ≠ commitments.size then
    throw (.inputLengthMismatch "ys" commitments.size ys.size)
  if proofs.size ≠ commitments.size then
    throw (.inputLengthMismatch "proofs" commitments.size proofs.size)
  if commitmentsG1.size ≠ commitments.size then
    throw (.inputLengthMismatch "commitmentsG1" commitments.size commitmentsG1.size)
  if proofsG1.size ≠ commitments.size then
    throw (.inputLengthMismatch "proofsG1" commitments.size proofsG1.size)

  -- The Fiat-Shamir challenge, over arrays of one length, so no zip drops an entry.
  let r := computeVerifyKzgProofBatchChallenge commitments zs ys proofs
  let rPowers := computePowers r commitments.size

  -- proof_lincomb = Σ_i r^i · proof_i
  let proofLincombG1 ← g1LincombPoints proofsG1 rPowers
  -- proof_z_lincomb = Σ_i (z_i · r^i) · proof_i
  let zRPowers := Array.zipWith (· * ·) zs rPowers
  let proofZLincombG1 ← g1LincombPoints proofsG1 zRPowers

  -- C_minus_ys[i] = commitment_i - [y_i]
  let cMinusYs : Array G1 := Array.zipWith
    (fun commitmentG1 y => Bls.G1.add commitmentG1 (Bls.G1.mul Bls.G1.generator (-y)))
    commitmentsG1 ys
  let cMinusYLincombG1 ← g1LincombPoints cMinusYs rPowers

  let s := setup.g2Monomial[1]'(by decide)
  let pairs : Array (G1 × G2) := #[
    ( proofLincombG1, Bls.G2.neg s ),
    ( Bls.G1.add cMinusYLincombG1 proofZLincombG1
    , Bls.G2.generator )
  ]
  return Bls.pairingCheck pairs

/-- Compute a KZG commitment from a blob. -/
def blobToKzgCommitment (setup : TrustedSetup) (blob : Blob) :
    Except KzgError KZGCommitment := do
  let polynomial ← blobToPolynomial blob
  let commitmentG1 ← g1LincombPoints setup.g1LagrangeBrp.toArray polynomial
  return compressG1 commitmentG1

/-- Compute the KZG proof of a blob against a commitment.

It does not check that the commitment belongs to the blob. -/
def computeBlobKzgProof (setup : TrustedSetup) (blob : Blob) (commitmentBytes : Bytes48) :
    Except KzgError KZGProof := do
  let commitment ← bytesToKzgCommitment commitmentBytes
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitment
  let (proof, _) ← computeKzgProofImpl setup polynomial evaluationChallenge
  return proof

/-- Verify that `blob` corresponds to `commitment` via `proof`. -/
def verifyBlobKzgProof (setup : TrustedSetup)
    (blob : Blob) (commitmentBytes : Bytes48) (proofBytes : Bytes48)
    : Except KzgError Bool := do
  let commitmentG1 ← match validateKzgG1Point commitmentBytes with
                     | .ok c    => pure c
                     | .error _ => throw (.invalidCommitment none)
  let polynomial ← blobToPolynomial blob
  let evaluationChallenge := computeChallenge blob commitmentBytes
  let y ← evaluatePolynomialInEvaluationForm polynomial evaluationChallenge
  let proofG1 ← match validateKzgG1Point proofBytes with
                | .ok p    => pure p
                | .error _ => throw (.invalidProof none)
  return verifyKzgProofImpl setup commitmentG1 evaluationChallenge y proofG1

/-- Verify a batch of triples of a blob, a commitment and a proof.

Each triple checks its commitment, then decodes its blob, then checks its proof.

The first failure gives the error.

The empty batch verifies. -/
def verifyBlobKzgProofBatch (setup : TrustedSetup)
    (blobs : Array Blob)
    (commitmentsBytes : Array Bytes48)
    (proofsBytes : Array Bytes48) : Except KzgError Bool := do
  if commitmentsBytes.size ≠ blobs.size then
    throw (.inputLengthMismatch "commitmentsBytes" blobs.size commitmentsBytes.size)
  if proofsBytes.size ≠ blobs.size then
    throw (.inputLengthMismatch "proofsBytes" blobs.size proofsBytes.size)

  -- The three arrays have one length here, so the zip drops no entry.
  let (commitments, commitmentsG1, challenges, ys, proofs, proofsG1) ←
    (blobs.zip (commitmentsBytes.zip proofsBytes)).zipIdx.foldlM
      (init := ((#[] : Array KZGCommitment), (#[] : Array G1), (#[] : Array Fr),
                (#[] : Array Fr), (#[] : Array KZGProof), (#[] : Array G1)))
      fun (commitments, commitmentsG1, challenges, ys, proofs, proofsG1)
          ((blob, cb, pb), i) => do
        let commitmentG1 ← match validateKzgG1Point cb with
                           | .ok c    => pure c
                           | .error _ => throw (.invalidCommitment (some i))
        let polynomial ← blobToPolynomial blob
        let challenge := computeChallenge blob cb
        let y ← evaluatePolynomialInEvaluationForm polynomial challenge
        let proofG1 ← match validateKzgG1Point pb with
                      | .ok p    => pure p
                      | .error _ => throw (.invalidProof (some i))

        pure (commitments.push cb, commitmentsG1.push commitmentG1,
              challenges.push challenge, ys.push y, proofs.push pb, proofsG1.push proofG1)

  verifyKzgProofBatch setup commitments commitmentsG1 challenges ys proofs proofsG1

end EthLib.Cryptography.Kzg
