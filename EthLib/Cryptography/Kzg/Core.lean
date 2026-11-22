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

The step comments quote the functions that each of them names, in consensus-specs at `8a3df1d7`:
<https://github.com/ethereum/consensus-specs/blob/8a3df1d79d70000801407e33d660171be9cd06d1/specs/deneb/polynomial-commitments.md>

EIP-4844 links that file at `86fb82b2`, where the proof function returns no `y`.

There the setup point is `KZG_SETUP_G2[1]`, and a negation is `(BLS_MODULUS - z) % BLS_MODULUS`.
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
  -- validate_kzg_g1: `if b == G1_POINT_AT_INFINITY: return`.
  if b == G1_POINT_AT_INFINITY then .ok Bls.G1.zero
  -- `assert bls.KeyValidate(b)`.
  else match Bls.G1.keyValidatePoint b with
  | .ok p    => .ok p
  | .error _ => .error .invalidG1Point

/-- BLS validation, allowing the point at infinity. -/
def validateKzgG1 (b : Bytes48) : Bool :=
  -- validate_kzg_g1: `if b == G1_POINT_AT_INFINITY: return`.
  if b == G1_POINT_AT_INFINITY then true
  -- `assert bls.KeyValidate(b)`.
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
  -- bytes_to_kzg_commitment: `validate_kzg_g1(b)`, then `return KZGCommitment(b)`.
  if validateKzgG1 b then .ok b else .error (.invalidCommitment none)

/-- Validate untrusted bytes as a `KZGProof`. -/
def bytesToKzgProof (b : Bytes48) : Except KzgError KZGProof :=
  -- bytes_to_kzg_proof: `validate_kzg_g1(b)`, then `return KZGProof(b)`.
  if validateKzgG1 b then .ok b else .error (.invalidProof none)

/-- Fiat-Shamir challenge for a (blob, commitment) pair. -/
def computeChallenge (blob : Blob) (commitment : KZGCommitment) : Fr :=
  -- compute_challenge: `degree_poly = int.to_bytes(FIELD_ELEMENTS_PER_BLOB, 16, KZG_ENDIANNESS)`.
  let degreePoly : ByteArray := ⟨(Base.natToBytes 16 FIELD_ELEMENTS_PER_BLOB).toArray⟩
  -- `data = FIAT_SHAMIR_PROTOCOL_DOMAIN + degree_poly`.
  --
  -- Then `data += blob` and `data += commitment`.
  let data := FIAT_SHAMIR_PROTOCOL_DOMAIN ++ degreePoly ++ ⟨blob.toArray⟩ ++ ⟨commitment.toArray⟩
  -- `return hash_to_bls_field(data)`.
  Fr.hashToBlsField data

/-- The linear combination `sum_i scalars_i * points_i` of decoded points.

The setup and the inputs are decoded once, so no point goes through bytes in between.
-/
def g1LincombPoints
    (points : Array G1) (scalars : Array Fr) : Except KzgError G1 := do
  -- g1_lincomb: `assert len(points) == len(scalars)`.
  if points.size ≠ scalars.size then
    throw (.lincombLengthMismatch points.size scalars.size)
  -- `if len(points) == 0: return bls.G1_to_bytes48(bls.G1.identity())`.
  if points.size = 0 then
    return Bls.G1.zero
  -- `result = bls.multi_exp(points_g1, scalars)`, on points that are already decoded.
  return Bls.G1.msm points scalars

/-- The quotient `q(z)` of the KZG proof, given `y = p(z)`, when `z` is a root of unity.

The general quotient divides by zero at such a `z`, so this case has its own formula.

It is the section "Dividing when one of the points is zero" of [the multiproofs note][feist].

[feist]: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html
-/
def computeQuotientEvalWithinDomain
    (z : Fr) (polynomial : Polynomial) (y : Fr)
    : Fr :=
  -- compute_quotient_eval_within_domain: `roots_of_unity_brp = bit_reversal_permutation(...)`.
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  -- `denominator = z * (z - omega_i)`, for every `i` at once.
  --
  -- One batch inversion gives every `1 / (z * (z - omega_i))`.
  --
  -- The skipped term has denominator zero, which inverts to zero and is never read.
  let inverses := Fr.batchInverse (domain.map fun omega_i => z * (z - omega_i))
  -- `result = BLSFieldElement(0)`, then the loop over `i, omega_i`.
  --
  -- The caller passes 4096 values, so the zip drops no entry.
  ((domain.zip polynomial).zip inverses).foldl (init := Fr.zero)
    fun result ((omega_i, p_i), inverse_i) =>
      -- `if omega_i == z: continue`.
      if omega_i == z then
        result
      else
        -- `f_i = polynomial[i] - y` and `numerator = f_i * omega_i`.
        let f_i := p_i - y
        let numerator := f_i * omega_i
        -- `result += numerator / denominator`.
        --
        -- Here `z` is in the domain, so `z ≠ 0`, and the skip gives `omega_i ≠ z`.
        result + numerator * inverse_i

/-- Returns the KZG proof at `z` and the evaluation `y = p(z)`. -/
def computeKzgProofImpl (setup : TrustedSetup)
    (polynomial : Polynomial) (z : Fr) : Except KzgError (KZGProof × Fr) := do
  -- compute_kzg_proof_impl: its last step reads `bit_reversal_permutation(KZG_SETUP_G1_LAGRANGE)`.
  --
  -- The setup keeps it, decoded once.
  let g1LagrangeBrp := setup.g1LagrangeBrp.toArray
  -- `roots_of_unity_brp = bit_reversal_permutation(compute_roots_of_unity(...))`.
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB

  -- `y = evaluate_polynomial_in_evaluation_form(polynomial, z)`.
  let y ← evaluatePolynomialInEvaluationForm polynomial z
  -- `polynomial_shifted = [p - y for p in polynomial]`.
  let polynomialShifted := polynomial.map (· - y)

  -- `denominator_poly = [x - z for x in roots_of_unity_brp]`.
  let denominatorPoly := domain.map (· - z)
  -- All the inverses of the denominators with one inversion, for the divisions below.
  let inverses := Fr.batchInverse denominatorPoly

  -- The loop over `i, (a, b)`, over the 4096 values that the evaluation above checked.
  let quotient : Array Fr :=
    (domain.zip (polynomialShifted.zip inverses)).map fun (omega_i, a, inverse_i) =>
      -- `if b == BLSFieldElement(0)`: `z` is a root of unity, the special case.
      if (omega_i - z).isZero then
        computeQuotientEvalWithinDomain omega_i polynomial y
      -- `quotient_polynomial[i] = a / b`.
      else
        a * inverse_i

  -- `g1_lincomb(bit_reversal_permutation(KZG_SETUP_G1_LAGRANGE), quotient_polynomial)`.
  let proofG1 ← g1LincombPoints g1LagrangeBrp quotient
  -- `return KZGProof(...), y`.
  return (compressG1 proofG1, y)

/-- The KZG proof at `z` for the polynomial of a blob, with the value `p(z)`.

The value comes as 32 big-endian bytes. -/
def computeKzgProof (setup : TrustedSetup) (blob : Blob) (zBytes : Bytes32) :
    Except KzgError (KZGProof × Bytes32) := do
  -- compute_kzg_proof: the length asserts hold by the types.
  --
  -- `polynomial = blob_to_polynomial(blob)`.
  let polynomial ← blobToPolynomial blob
  -- `proof, y = compute_kzg_proof_impl(polynomial, bytes_to_bls_field(z_bytes))`.
  let z ← bytesToBlsField zBytes
  let (proof, y) ← computeKzgProofImpl setup polynomial z
  -- `return proof, int(y).to_bytes(BYTES_PER_FIELD_ELEMENT, KZG_ENDIANNESS)`.
  return (proof, blsFieldToBytes y)

/-- Verify a KZG proof that `p(z) == y`, given only the setup point `[s]_2`.

It checks `e(P - [y], -[1]) * e(proof, [s] - [z]) == 1`, where `P` commits to `p`.

A caller that holds only `[s]_2`, such as the point evaluation precompile, can use it. -/
def verifyKzgProofWith (s : G2)
    (commitmentG1 : G1) (z y : Fr) (proofG1 : G1) : Bool :=
  -- verify_kzg_proof_impl: `X_minus_z = bls.add([s]_2, bls.multiply(bls.G2(), -z))`.
  --
  -- Here `[s]_2` is `KZG_SETUP_G2_MONOMIAL[1]`, which the caller passes.
  let X_minus_z : G2 := Bls.G2.add s (Bls.G2.mul Bls.G2.generator (-z))
  -- `P_minus_y = bls.add(commitment, bls.multiply(bls.G1(), -y))`, on decoded points.
  let P_minus_y : G1 := Bls.G1.add commitmentG1 (Bls.G1.mul Bls.G1.generator (-y))
  -- `return bls.pairing_check([[P_minus_y, bls.neg(bls.G2())], [proof, X_minus_z]])`.
  let pairs : Array (G1 × G2) := #[
    (P_minus_y, Bls.G2.neg Bls.G2.generator),
    (proofG1, X_minus_z)
  ]
  Bls.pairingCheck pairs

/-- Verify a KZG proof that `p(z) == y` for the committed polynomial `p`. -/
def verifyKzgProofImpl (setup : TrustedSetup)
    (commitmentG1 : G1) (z y : Fr) (proofG1 : G1) : Bool :=
  -- verify_kzg_proof_impl, with `[s]_2 = KZG_SETUP_G2_MONOMIAL[1]`.
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
  -- verify_kzg_proof: the length asserts hold by the types.
  --
  -- `bytes_to_kzg_commitment`, `bytes_to_bls_field` twice, then `bytes_to_kzg_proof`.
  let commitment ← bytesToKzgCommitment commitmentBytes
  let z ← bytesToBlsField zBytes
  let y ← bytesToBlsField yBytes
  let proof ← bytesToKzgProof proofBytes
  -- The pairing check reads the points, so both are decoded here, as in EIP-4844.
  --
  -- Bytes that passed validation always decode, so neither decoding below fails.
  let commitmentG1 ← uncompressG1 commitment
  let proofG1 ← uncompressG1 proof
  -- `return verify_kzg_proof_impl(...)`.
  return verifyKzgProofImpl setup commitmentG1 z y proofG1

/-- The Fiat-Shamir challenge of a batch of openings.

It hashes the domain, the degree bound, the number of openings, and each opening in order. -/
def computeVerifyKzgProofBatchChallenge (commitments : Array KZGCommitment) (zs ys : Array Fr)
    (proofs : Array KZGProof) : Fr :=
  -- verify_kzg_proof_batch: `degree_poly = int.to_bytes(FIELD_ELEMENTS_PER_BLOB, 8, ...)`.
  let degreePoly : ByteArray := ⟨(Base.natToBytes 8 FIELD_ELEMENTS_PER_BLOB).toArray⟩
  -- `num_commitments = int.to_bytes(len(commitments), 8, KZG_ENDIANNESS)`.
  let numCommitments : ByteArray := ⟨(Base.natToBytes 8 commitments.size).toArray⟩
  -- `data = RANDOM_CHALLENGE_KZG_BATCH_DOMAIN + degree_poly + num_commitments`.
  --
  -- `data += commitment + bls_field_to_bytes(z) + bls_field_to_bytes(y) + proof`, per opening.
  let data := ((commitments.zip zs).zip (ys.zip proofs)).foldl
    (init := RANDOM_CHALLENGE_KZG_BATCH_DOMAIN ++ degreePoly ++ numCommitments)
    fun data ((commitment, z), (y, proof)) => data
        ++ ⟨commitment.toArray⟩
        ++ ⟨(blsFieldToBytes z).toArray⟩
        ++ ⟨(blsFieldToBytes y).toArray⟩
        ++ ⟨proof.toArray⟩
  -- `r = hash_to_bls_field(data)`.
  Fr.hashToBlsField data

/-- Verify multiple KZG proofs efficiently using a random linear combination. -/
def verifyKzgProofBatch (setup : TrustedSetup)
    (commitments : Array KZGCommitment)
    (commitmentsG1 : Array G1)
    (zs ys : Array Fr)
    (proofs : Array KZGProof)
    (proofsG1 : Array G1) : Except KzgError Bool := do
  -- verify_kzg_proof_batch: `assert len(commitments) == len(zs) == len(ys) == len(proofs)`.
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

  -- `r = hash_to_bls_field(data)`, over arrays of one length, so no zip drops an entry.
  let r := computeVerifyKzgProofBatchChallenge commitments zs ys proofs
  -- `r_powers = compute_powers(r, len(commitments))`.
  let rPowers := computePowers r commitments.size

  -- `proof_lincomb = g1_lincomb(proofs, r_powers)`.
  let proofLincombG1 ← g1LincombPoints proofsG1 rPowers
  -- `proof_z_lincomb = g1_lincomb(proofs, [z * r_power for z, r_power in zip(zs, r_powers, ...)])`.
  --
  -- The length checks above make `strict=True` hold, here and below.
  let zRPowers := Array.zipWith (· * ·) zs rPowers
  let proofZLincombG1 ← g1LincombPoints proofsG1 zRPowers

  -- `C_minus_ys = [bls.add(commitment, bls.multiply(bls.G1(), -y)) for ...]`, on decoded points.
  let cMinusYs : Array G1 := Array.zipWith
    (fun commitmentG1 y => Bls.G1.add commitmentG1 (Bls.G1.mul Bls.G1.generator (-y)))
    commitmentsG1 ys
  -- `C_minus_y_lincomb = g1_lincomb(C_minus_y_as_KZGCommitments, r_powers)`.
  --
  -- The points stay decoded, with no round trip through bytes.
  let cMinusYLincombG1 ← g1LincombPoints cMinusYs rPowers

  -- `return bls.pairing_check([...])`, with the pair `[proof_lincomb, bls.neg(...G2_MONOMIAL[1])]`.
  --
  -- The other pair is `[bls.add(C_minus_y_lincomb, proof_z_lincomb), bls.G2()]`, on decoded points.
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
  -- blob_to_kzg_commitment: the length assert holds by the type.
  --
  -- `g1_lincomb(bit_reversal_permutation(KZG_SETUP_G1_LAGRANGE), blob_to_polynomial(blob))`.
  let polynomial ← blobToPolynomial blob
  let commitmentG1 ← g1LincombPoints setup.g1LagrangeBrp.toArray polynomial
  return compressG1 commitmentG1

/-- Compute the KZG proof of a blob against a commitment.

It does not check that the commitment belongs to the blob. -/
def computeBlobKzgProof (setup : TrustedSetup) (blob : Blob) (commitmentBytes : Bytes48) :
    Except KzgError KZGProof := do
  -- compute_blob_kzg_proof: the length asserts hold by the types.
  --
  -- `commitment = bytes_to_kzg_commitment(commitment_bytes)`.
  let commitment ← bytesToKzgCommitment commitmentBytes
  -- `polynomial = blob_to_polynomial(blob)`.
  let polynomial ← blobToPolynomial blob
  -- `evaluation_challenge = compute_challenge(blob, commitment)`.
  let evaluationChallenge := computeChallenge blob commitment
  -- `proof, _ = compute_kzg_proof_impl(polynomial, evaluation_challenge)`.
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
  -- verify_blob_kzg_proof: the length asserts hold by the types.
  --
  -- `commitment = bytes_to_kzg_commitment(commitment_bytes)`.
  let commitment ← bytesToKzgCommitment commitmentBytes
  -- `polynomial = blob_to_polynomial(blob)`.
  let polynomial ← blobToPolynomial blob
  -- `evaluation_challenge = compute_challenge(blob, commitment)`.
  let evaluationChallenge := computeChallenge blob commitment
  -- `y = evaluate_polynomial_in_evaluation_form(polynomial, evaluation_challenge)`.
  let y ← evaluatePolynomialInEvaluationForm polynomial evaluationChallenge
  -- `proof = bytes_to_kzg_proof(proof_bytes)`.
  let proof ← bytesToKzgProof proofBytes
  -- The pairing check reads the points, so both are decoded here, as in EIP-4844.
  let commitmentG1 ← uncompressG1 commitment
  let proofG1 ← uncompressG1 proof
  -- `return verify_kzg_proof_impl(commitment, evaluation_challenge, y, proof)`.
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
  -- verify_blob_kzg_proof_batch: `assert len(blobs) == len(commitments_bytes) == len(...)`.
  --
  -- The third length is that of `proofs_bytes`.
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
        -- `commitment = bytes_to_kzg_commitment(commitment_bytes)`, with its index on failure.
        let commitment ← match bytesToKzgCommitment cb with
                         | .ok c    => pure c
                         | .error _ => throw (.invalidCommitment (some i))
        -- `polynomial = blob_to_polynomial(blob)`.
        let polynomial ← blobToPolynomial blob
        -- `evaluation_challenge = compute_challenge(blob, commitment)`.
        let challenge := computeChallenge blob commitment
        -- `ys.append(evaluate_polynomial_in_evaluation_form(polynomial, evaluation_challenge))`.
        let y ← evaluatePolynomialInEvaluationForm polynomial challenge
        -- `proofs.append(bytes_to_kzg_proof(proof_bytes))`.
        let proof ← match bytesToKzgProof pb with
                    | .ok p    => pure p
                    | .error _ => throw (.invalidProof (some i))
        -- The pairing check reads the points, so both are decoded here, as in EIP-4844.
        let commitmentG1 ← uncompressG1 commitment
        let proofG1 ← uncompressG1 proof

        pure (commitments.push commitment, commitmentsG1.push commitmentG1,
              challenges.push challenge, ys.push y, proofs.push proof, proofsG1.push proofG1)

  -- `return verify_kzg_proof_batch(commitments, evaluation_challenges, ys, proofs)`.
  verifyKzgProofBatch setup commitments commitmentsG1 challenges ys proofs proofsG1

end EthLib.Cryptography.Kzg
