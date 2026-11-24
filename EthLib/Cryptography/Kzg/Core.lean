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

The scheme is PolyCommit_DL, §3.2 of Kate, Zaverucha and Goldberg, ASIACRYPT 2010:
<https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf>

[EIP-4844, Cryptographic helpers][eip-4844] uses two operations of this module.

They are the check of one opening and the batch check of blob proofs.

The proof function of the text that EIP-4844 points to returns no `y`.

Here the proof function also returns `y = p(z)`.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#cryptographic-helpers
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
def compressG1 (p : G1) : Bytes48 := Bls.G1.compress p

/-! ## Validation -/

/-- Validate a commitment or a proof and return its point.

It is BLS public-key validation, except that the point at infinity is allowed.

The commitment to the zero polynomial is the point at infinity, so KZG must accept it.
-/
def validateKzgG1Point (b : Bytes48) : Except KzgError G1 :=
  -- The encoding of the point at infinity is valid.
  if b == G1_POINT_AT_INFINITY then .ok Bls.G1.zero
  -- Any other encoding must pass the BLS public-key validation.
  else match Bls.G1.keyValidatePoint b with
  | .ok p    => .ok p
  | .error _ => .error .invalidG1Point

/-- BLS validation, allowing the point at infinity. -/
def validateKzgG1 (b : Bytes48) : Bool :=
  -- The encoding of the point at infinity is valid.
  if b == G1_POINT_AT_INFINITY then true
  -- Any other encoding must pass the BLS public-key validation.
  else (Bls.G1.keyValidate b).isOk

/-- Decompress 48 bytes into a point, or fail with an invalid-point error.

A failed decompression must stop the computation.

Falling back to a default point would silently replace the input with the point at infinity.
-/
def uncompressG1 (b : Bytes48) : Except KzgError G1 :=
  match Bls.G1.uncompress b with
  | .ok g    => pure g
  | .error _ => throw .invalidG1Point

/-- Validate untrusted bytes as a `KZGCommitment`. -/
def bytesToKzgCommitment (b : Bytes48) : Except KzgError KZGCommitment :=
  -- The bytes are a commitment when they are a valid `G1` point, at infinity or not.
  if validateKzgG1 b then .ok b else .error (.invalidCommitment none)

/-- Validate untrusted bytes as a `KZGProof`. -/
def bytesToKzgProof (b : Bytes48) : Except KzgError KZGProof :=
  -- The bytes are a proof when they are a valid `G1` point, at infinity or not.
  if validateKzgG1 b then .ok b else .error (.invalidProof none)

/-- Fiat-Shamir challenge for a (blob, commitment) pair. -/
def computeChallenge (blob : Blob) (commitment : KZGCommitment) : Fr :=
  -- The degree bound 4096, as 16 big-endian bytes.
  let degreePoly : ByteArray := ⟨(Base.ByteOrder.toBE 16 FIELD_ELEMENTS_PER_BLOB).toArray⟩
  -- The hash input is the 16 ASCII bytes `FSBLOBVERIFY_V1_`, then the degree bound.
  --
  -- Then come the blob and the commitment.
  let data := FIAT_SHAMIR_PROTOCOL_DOMAIN ++ degreePoly ++ ⟨blob.toArray⟩ ++ ⟨commitment.toArray⟩
  -- The challenge is the SHA-256 of that input, read as a big-endian integer.
  --
  -- It is reduced modulo the modulus of `Fr`.
  Fr.hashToBlsField data

/-- The linear combination `sum_i scalars_i * points_i` of decoded points.

The setup and the inputs are decoded once, so no point goes through bytes in between.
-/
def g1LincombPoints
    (points : Array G1) (scalars : Array Fr) : Except KzgError G1 := do
  -- There must be as many scalars as points.
  if points.size ≠ scalars.size then
    throw (.lincombLengthMismatch points.size scalars.size)
  -- With no points, the sum is the point at infinity.
  if points.size = 0 then
    return Bls.G1.zero
  -- Otherwise one multi-scalar multiplication, on points that are already decoded.
  return Bls.G1.msm points scalars

/-- The quotient `q(z)` of the KZG proof, given `y = p(z)`, when `z` is a root of unity.

The general quotient divides by zero at such a `z`, so this case has its own formula.

It is the section "Dividing when one of the points is zero" of [the multiproofs note][feist].

[feist]: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html
-/
def computeQuotientEvalWithinDomain
    (z : Fr) (polynomial : Polynomial) (y : Fr)
    : Fr :=
  -- The domain is the 4096-th roots of unity in bit-reversed order.
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  -- The denominators `z (z - omega_i)`, for every `i` at once.
  --
  -- One batch inversion gives every `1 / (z (z - omega_i))`.
  --
  -- The skipped term has denominator zero, which inverts to zero and is never read.
  let inverses := Fr.batchInverse (domain.map fun omega_i => z * (z - omega_i))
  -- The quotient starts at 0 and gains one term per point `omega_i` of the domain.
  --
  -- The caller passes 4096 values, so the zip drops no entry.
  ((domain.zip polynomial).zip inverses).foldl (init := Fr.zero)
    fun result ((omega_i, p_i), inverse_i) =>
      -- The term of `omega_i = z` is skipped.
      if omega_i == z then
        result
      else
        -- `f_i = p_i - y`, for the value `p_i` at `omega_i`, and the numerator is `f_i omega_i`.
        let f_i := p_i - y
        let numerator := f_i * omega_i
        -- The term `f_i omega_i / (z (z - omega_i))` is added to the quotient.
        --
        -- Here `z` is in the domain, so `z ≠ 0`, and the skip gives `omega_i ≠ z`.
        result + numerator * inverse_i

/-- Returns the KZG proof at `z` and the evaluation `y = p(z)`. -/
def computeKzgProofImpl (setup : TrustedSetup)
    (polynomial : Polynomial) (z : Fr) : Except KzgError (KZGProof × Fr) := do
  -- The proof reads the Lagrange form of the `G1` setup in bit-reversed order.
  --
  -- The setup keeps it, decoded once.
  let g1LagrangeBrp := setup.g1LagrangeBrp.toArray
  -- The domain is the 4096-th roots of unity in bit-reversed order.
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB

  -- `y = p(z)`, which also checks that there are 4096 values.
  let y ← evaluatePolynomialInEvaluationForm polynomial z
  -- The values of `p(x) - y`: `p_i - y` for each value `p_i`.
  let polynomialShifted := polynomial.map (· - y)

  -- The values of `x - z`: `omega_i - z` for each point `omega_i` of the domain.
  let denominatorPoly := domain.map (· - z)
  -- All the inverses of the denominators with one inversion, for the divisions below.
  let inverses := Fr.batchInverse denominatorPoly

  -- One quotient value `q_i` per point `omega_i`, for the 4096 values that `y = p(z)` checked.
  let quotient : Array Fr :=
    (domain.zip (polynomialShifted.zip inverses)).map fun (omega_i, a, inverse_i) =>
      -- When `omega_i = z`, `q_i` is `q(z)`, by the sum over the domain above.
      if (omega_i - z).isZero then
        computeQuotientEvalWithinDomain omega_i polynomial y
      -- Otherwise `q_i = (p_i - y) / (omega_i - z)`.
      else
        a * inverse_i

  -- The proof is `sum_i q_i L_i`, for the Lagrange setup `L_i` of `G1` in bit-reversed order.
  let proofG1 ← g1LincombPoints g1LagrangeBrp quotient
  -- The proof, compressed, and the value `y`.
  return (compressG1 proofG1, y)

/-- The KZG proof at `z` for the polynomial of a blob, with the value `p(z)`.

The value comes as 32 big-endian bytes. -/
def computeKzgProof (setup : TrustedSetup) (blob : Blob) (zBytes : Bytes32) :
    Except KzgError (KZGProof × Bytes32) := do
  -- The byte lengths of the inputs hold by their types.
  --
  -- The blob is decoded into its 4096 values in `Fr`.
  let polynomial ← blobToPolynomial blob
  -- The point `z` is decoded into `Fr`, then the proof and `y = p(z)` are computed.
  let z ← bytesToBlsField zBytes
  let (proof, y) ← computeKzgProofImpl setup polynomial z
  -- The proof and `y` as 32 big-endian bytes.
  return (proof, blsFieldToBytes y)

/-- Verify a KZG proof that `p(z) = y`, given only the setup point `[s]_2`.

It checks `e(P - [y], -[1]) * e(proof, [s] - [z]) = 1`, where `P` commits to `p`.

A caller that holds only `[s]_2`, such as the point evaluation precompile, can use it. -/
def verifyKzgProofWith (s : G2)
    (commitmentG1 : G1) (z y : Fr) (proofG1 : G1) : Bool :=
  -- `[s - z]_2 = [s]_2 + (-z) [1]_2`.
  --
  -- Here `[s]_2` is entry 1 of the monomial form of the `G2` setup, which the caller passes.
  let X_minus_z : G2 := Bls.G2.add s (Bls.G2.mul Bls.G2.generator (-z))
  -- `P - [y]_1 = P + (-y) [1]_1`, on decoded points.
  let P_minus_y : G1 := Bls.G1.add commitmentG1 (Bls.G1.mul Bls.G1.generator (-y))
  -- The proof is valid when `e(P - [y]_1, -[1]_2) * e(proof, [s - z]_2) = 1`.
  let pairs : Array (G1 × G2) := #[
    (P_minus_y, Bls.G2.neg Bls.G2.generator),
    (proofG1, X_minus_z)
  ]
  Bls.pairingCheck pairs

/-- Verify a KZG proof that `p(z) = y` for the committed polynomial `p`. -/
def verifyKzgProofImpl (setup : TrustedSetup)
    (commitmentG1 : G1) (z y : Fr) (proofG1 : G1) : Bool :=
  -- The check above, with `[s]_2` the entry 1 of the monomial form of the `G2` setup.
  verifyKzgProofWith (setup.g2Monomial[1]'(by decide)) commitmentG1 z y proofG1

/-- Verify a KZG proof, taking inputs as raw bytes.

It checks its arguments in the order of [EIP-4844][eip-4844].

That order is the commitment, `z`, `y`, then the proof.

The first invalid argument gives the error.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#cryptographic-helpers
-/
def verifyKzgProof (setup : TrustedSetup)
    (commitmentBytes : Bytes48) (zBytes yBytes : Bytes32) (proofBytes : Bytes48)
    : Except KzgError Bool := do
  -- The byte lengths of the inputs hold by their types.
  --
  -- The commitment is validated, `z` and `y` are decoded into `Fr`, then the proof is validated.
  let commitment ← bytesToKzgCommitment commitmentBytes
  let z ← bytesToBlsField zBytes
  let y ← bytesToBlsField yBytes
  let proof ← bytesToKzgProof proofBytes
  -- The pairing check reads the points, so both are decoded here, as in EIP-4844.
  --
  -- Bytes that passed validation always decode, so neither decoding below fails.
  let commitmentG1 ← uncompressG1 commitment
  let proofG1 ← uncompressG1 proof
  -- The pairing check of the proof.
  return verifyKzgProofImpl setup commitmentG1 z y proofG1

/-- The Fiat-Shamir challenge of a batch of openings.

It hashes the domain, the degree bound, the number of openings, and each opening in order. -/
def computeVerifyKzgProofBatchChallenge (commitments : Array KZGCommitment) (zs ys : Array Fr)
    (proofs : Array KZGProof) : Fr :=
  -- The degree bound 4096, as 8 big-endian bytes.
  let degreePoly : ByteArray := ⟨(Base.ByteOrder.toBE 8 FIELD_ELEMENTS_PER_BLOB).toArray⟩
  -- The number of openings, as 8 big-endian bytes.
  let numCommitments : ByteArray := ⟨(Base.ByteOrder.toBE 8 commitments.size).toArray⟩
  -- The hash input is the 16 ASCII bytes `RCKZGBATCH___V1_`, the bound and the number.
  --
  -- Then, per opening: the commitment, `z` and `y` as 32 big-endian bytes each, and the proof.
  let data := ((commitments.zip zs).zip (ys.zip proofs)).foldl
    (init := RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ++ degreePoly ++ numCommitments)
    fun data ((commitment, z), (y, proof)) => data
        ++ ⟨commitment.toArray⟩
        ++ ⟨(blsFieldToBytes z).toArray⟩
        ++ ⟨(blsFieldToBytes y).toArray⟩
        ++ ⟨proof.toArray⟩
  -- The challenge is the SHA-256 of that input, read as a big-endian integer.
  --
  -- It is reduced modulo the modulus of `Fr`.
  Fr.hashToBlsField data

/-- Verify multiple KZG proofs efficiently using a random linear combination. -/
def verifyKzgProofBatch (setup : TrustedSetup)
    (commitments : Array KZGCommitment)
    (commitmentsG1 : Array G1)
    (zs ys : Array Fr)
    (proofs : Array KZGProof)
    (proofsG1 : Array G1) : Except KzgError Bool := do
  -- There must be as many points `z`, values `y` and proofs as commitments.
  --
  -- The decoded points must come in the same number.
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

  -- The challenge `r`, over arrays of one length, so no opening is dropped.
  let r := computeVerifyKzgProofBatchChallenge commitments zs ys proofs
  -- The powers `r^0, ..., r^(n - 1)`, for `n` openings.
  let rPowers := computePowers r commitments.size

  -- `sum_i r^i pi_i`, for the proof `pi_i` of opening `i`.
  let proofLincombG1 ← g1LincombPoints proofsG1 rPowers
  -- `sum_i (z_i r^i) pi_i`.
  --
  -- The length checks above make the arrays pair up exactly, here and below.
  let zRPowers := Array.zipWith (· * ·) zs rPowers
  let proofZLincombG1 ← g1LincombPoints proofsG1 zRPowers

  -- `C_i - [y_i]_1 = C_i + (-y_i) [1]_1`, for each commitment `C_i`, on decoded points.
  let cMinusYs : Array G1 := Array.zipWith
    (fun commitmentG1 y => Bls.G1.add commitmentG1 (Bls.G1.mul Bls.G1.generator (-y)))
    commitmentsG1 ys
  -- `sum_i r^i (C_i - [y_i]_1)`.
  --
  -- The points stay decoded, with no round trip through bytes.
  let cMinusYLincombG1 ← g1LincombPoints cMinusYs rPowers

  -- The batch is valid when `e(sum_i r^i pi_i, -[s]_2) * e(A, [1]_2) = 1`, on decoded points.
  --
  -- Here `A = sum_i r^i (C_i - [y_i]_1) + sum_i (z_i r^i) pi_i`.
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
  -- The byte length of the blob holds by its type.
  --
  -- The commitment is `sum_i p_i L_i`, for the 4096 values `p_i` of the blob.
  --
  -- Here `L_i` is the Lagrange form of the `G1` setup in bit-reversed order.
  let polynomial ← blobToPolynomial blob
  let commitmentG1 ← g1LincombPoints setup.g1LagrangeBrp.toArray polynomial
  return compressG1 commitmentG1

/-- Compute the KZG proof of a blob against a commitment.

It does not check that the commitment belongs to the blob. -/
def computeBlobKzgProof (setup : TrustedSetup) (blob : Blob) (commitmentBytes : Bytes48) :
    Except KzgError KZGProof := do
  -- The byte lengths of the inputs hold by their types.
  --
  -- The commitment is validated as a `G1` point.
  let commitment ← bytesToKzgCommitment commitmentBytes
  -- The blob is decoded into its 4096 values in `Fr`.
  let polynomial ← blobToPolynomial blob
  -- The challenge `z` of the blob and the commitment.
  let evaluationChallenge := computeChallenge blob commitment
  -- The proof at `z`; the value `p(z)` is not returned.
  let (proof, _) ← computeKzgProofImpl setup polynomial evaluationChallenge
  return proof

/-- Verify that `blob` corresponds to `commitment` via `proof`.

It checks the commitment, then decodes the blob, then checks the proof.

That is the order of [EIP-4844][eip-4844], and the first failure gives the error.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#cryptographic-helpers
-/
def verifyBlobKzgProof (setup : TrustedSetup)
    (blob : Blob) (commitmentBytes : Bytes48) (proofBytes : Bytes48)
    : Except KzgError Bool := do
  -- The byte lengths of the inputs hold by their types.
  --
  -- The commitment is validated as a `G1` point.
  let commitment ← bytesToKzgCommitment commitmentBytes
  -- The blob is decoded into its 4096 values in `Fr`.
  let polynomial ← blobToPolynomial blob
  -- The challenge `z` of the blob and the commitment.
  let evaluationChallenge := computeChallenge blob commitment
  -- `y = p(z)`.
  let y ← evaluatePolynomialInEvaluationForm polynomial evaluationChallenge
  -- The proof is validated as a `G1` point.
  let proof ← bytesToKzgProof proofBytes
  -- The pairing check reads the points, so both are decoded here, as in EIP-4844.
  let commitmentG1 ← uncompressG1 commitment
  let proofG1 ← uncompressG1 proof
  -- The pairing check of the proof that `p(z) = y`.
  return verifyKzgProofImpl setup commitmentG1 evaluationChallenge y proofG1

/-- Verify a batch of triples of a blob, a commitment and a proof.

Each triple checks its commitment, then decodes its blob, then checks its proof.

That is the order of [EIP-4844][eip-4844], and the first failure gives the error.

The empty batch verifies.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#cryptographic-helpers
-/
def verifyBlobKzgProofBatch (setup : TrustedSetup)
    (blobs : Array Blob)
    (commitmentsBytes : Array Bytes48)
    (proofsBytes : Array Bytes48) : Except KzgError Bool := do
  -- There must be as many commitments and proofs as blobs.
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
        -- The commitment is validated as a `G1` point, with its index on failure.
        let commitment ← match bytesToKzgCommitment cb with
                         | .ok c    => pure c
                         | .error _ => throw (.invalidCommitment (some i))
        -- The blob is decoded into its 4096 values in `Fr`.
        let polynomial ← blobToPolynomial blob
        -- The challenge `z` of the blob and the commitment.
        let challenge := computeChallenge blob commitment
        -- `y = p(z)`, kept for the batch check.
        let y ← evaluatePolynomialInEvaluationForm polynomial challenge
        -- The proof is validated as a `G1` point, with its index on failure.
        let proof ← match bytesToKzgProof pb with
                    | .ok p    => pure p
                    | .error _ => throw (.invalidProof (some i))
        -- The pairing check reads the points, so both are decoded here, as in EIP-4844.
        let commitmentG1 ← uncompressG1 commitment
        let proofG1 ← uncompressG1 proof

        pure (commitments.push commitment, commitmentsG1.push commitmentG1,
              challenges.push challenge, ys.push y, proofs.push proof, proofsG1.push proofG1)

  -- The batch check of the openings at the challenges.
  verifyKzgProofBatch setup commitments commitmentsG1 challenges ys proofs proofsG1

end EthLib.Cryptography.Kzg
