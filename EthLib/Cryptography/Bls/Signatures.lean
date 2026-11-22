module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Bls.Compress
public import EthLib.Cryptography.Bls.HashToCurve
public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Bls.Errors

/-!
# BLS signatures

The signatures of the IRTF BLS signature draft, version 4, and the Ethereum wrappers.

<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04>

Ethereum uses the proof-of-possession scheme of §3.3, with keys in `G1` and signatures in `G2`.

The scheme operations take public keys and signatures with their size in the type.

The core verifications of §2.7 and §2.9 take the encodings as bytes, as the draft writes them.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- A public key: a compressed point of `G1`, 48 bytes. -/
abbrev BLSPubkey := Vector UInt8 48

/-- A signature: a compressed point of `G2`, 96 bytes. -/
abbrev BLSSignature := Vector UInt8 96

end EthLib.Cryptography.Bls

namespace EthLib.Cryptography.Bls.Signatures

open EthLib.Base EthLib.Cryptography.Bls

/-- The domain separation tag for messages in the proof-of-possession ciphersuite (§4.2.3). -/
def DST : ByteArray :=
  String.toUTF8 "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"

/-- The domain separation tag for public keys in the same ciphersuite.

It differs from the message tag, as §3.3.1 requires. -/
def POP_DST : ByteArray :=
  String.toUTF8 "BLS_POP_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_"

/-- The compressed encoding of the `G2` point at infinity.

The beacon chain uses it where a message carries no signature. -/
def G2_POINT_AT_INFINITY : BLSSignature := G2.infinityBytes

/-! ## Keys and encodings -/

/-- A secret key: an integer `SK` with `1 <= SK < r` (§2.3). -/
abbrev SecretKey := { sk : Fr // sk ≠ 0 }

/-- Decode a secret key from 32 big-endian bytes.

It rejects a wrong length, an integer `>= r` and zero. -/
def SecretKey.fromBytes (bytes : ByteArray) : Except BlsError SecretKey :=
  match exactBytes? 32 bytes with
  | none => .error .invalidSecretKey
  | some b =>
    match Fr.fromBytesBE b with
    | .error _ => .error .invalidSecretKey
    | .ok sk => if h : sk = 0 then .error .invalidSecretKey else .ok ⟨sk, h⟩

/-- The public key of a point, in the minimal-pubkey-size variant (§2.2). -/
def pointToPubkey (p : G1) : BLSPubkey := G1.compress p

/-- The signature of a point, in the minimal-pubkey-size variant (§2.2). -/
def pointToSignature (p : G2) : BLSSignature := G2.compress p

/-- The public key `SK * P` of a secret key (§2.4).

The key is secret, and this function does not run in constant time. -/
def skToPk (sk : SecretKey) : BLSPubkey :=
  -- Steps 1 to 3: `xP = SK * P`, and `PK` is the encoding of `xP`.
  pointToPubkey (G1.mul G1.generator sk.val)

/-- The subgroup check of a signature point (§2.7, step 3). -/
def signatureSubgroupCheck (sig : G2) : Bool := G2.inSubgroup sig

/-! ## Core operations -/

/-- The core signature `SK * H(message)`, with `H` the hash to `G2` under `dst` (§2.6).

The key is secret, and this function does not run in constant time.

The error comes from the hash to curve, which never fails. -/
def coreSign (sk : SecretKey) (msg dst : ByteArray) : Except BlsError BLSSignature := do
  -- Step 1: `Q` is the hash of the message to `G2`.
  let q ← HashToCurve.hashToG2 msg dst
  -- Steps 2 to 4: `R = SK * Q`, and the signature is the encoding of `R`.
  return pointToSignature (G2.mul q sk.val)

/-- The core verification: check `e(P, R) = e(PK, H(message))` (§2.7).

It returns `false` on any invalid input. -/
def coreVerify (pk msg sig dst : ByteArray) : Bool :=
  -- Steps 1 and 2: `R` is the point that the signature encodes, or INVALID.
  --
  -- A signature of any length other than 96 bytes is not an output of the encoding.
  match exactBytes? 96 sig with
  | none => false
  | some sig =>
  match G2.uncompress sig with
  | .error _ => false
  | .ok r =>
    -- Step 3: INVALID unless `R` is in `G2`.
    signatureSubgroupCheck r &&
    -- Steps 4 and 5: `PK` passes key validation and encodes `xP`, by one decoding.
    match exactBytes? 48 pk with
    | none => false
    | some pk =>
      match G1.keyValidatePoint pk with
      | .error _ => false
      | .ok xP =>
        -- Step 6: `Q` is the hash of the message to `G2`.
        match HashToCurve.hashToG2 msg dst with
        | .error _ => false
        -- Steps 7 to 9: `C1 = e(Q, xP)`, `C2 = e(R, P)`, and VALID exactly when `C1 = C2`.
        --
        -- The test is `e(P, R) * e(-xP, Q) = 1`, with the point of `G1` first.
        --
        -- It is the same test, by bilinearity.
        | .ok q => pairingCheck #[(G1.generator, r), (G1.neg xP, q)]

/-- The compressed sum of the signatures (§2.8).

It fails on an empty list and on a signature that does not decode.

As in the draft, it does not check that a signature lies in the subgroup. -/
def aggregate (sigs : Array BLSSignature) : Except BlsError BLSSignature := do
  -- The precondition `n >= 1`.
  if sigs.isEmpty then throw .emptySignatureList
  -- Steps 1 to 6: the sum of the points that the signatures encode, or INVALID.
  --
  -- The sum starts at the point at infinity, so step 1 is the first addition.
  --
  -- Adding a point to the point at infinity returns that point exactly.
  let agg ← sigs.foldlM
    (fun agg sig => return G2.add agg (← G2.uncompress sig)) G2.zero
  -- Steps 7 and 8: the signature is the encoding of the sum.
  return pointToSignature agg

/-- The pair `(-PK, H(message))` of one key and its message in the aggregate verification (§2.9).

It fails when the key is not 48 bytes or fails key validation. -/
def keyMessagePair (dst : ByteArray) (entry : ByteArray × ByteArray) :
    Except BlsError (G1 × G2) := do
  -- Steps 6 and 7: `PK_i` passes key validation and encodes `xP`, by one decoding.
  let some pk := exactBytes? 48 entry.1 | throw .invalidG1Point
  let xP ← G1.keyValidatePoint pk
  -- Step 8: `Q` is the hash of the message `message_i` to `G2`.
  let q ← HashToCurve.hashToG2 entry.2 dst
  -- The factor of step 9 is `e(Q, xP)`; the pair is `(-xP, Q)`, for a product equal to 1.
  return (G1.neg xP, q)

/-- The core aggregate verification: check `e(P, R) = prod_i e(PK_i, H(message_i))` (§2.9).

It returns `false` on an empty list, on lists of two sizes and on any invalid input. -/
def coreAggregateVerify (pks msgs : Array ByteArray) (sig dst : ByteArray) : Bool :=
  -- The precondition `n >= 1`, with as many messages as keys.
  if pks.isEmpty || pks.size != msgs.size then false else
  -- Steps 1 and 2: `R` is the point that the signature encodes, or INVALID.
  match exactBytes? 96 sig with
  | none => false
  | some sig =>
  match G2.uncompress sig with
  | .error _ => false
  | .ok r =>
    -- Step 3: INVALID unless `R` is in `G2`.
    signatureSubgroupCheck r &&
    -- Steps 4 to 8: one pair `(-xP_i, Q_i)` for each key, or INVALID.
    match (pks.zip msgs).mapM (keyMessagePair dst) with
    | .error _ => false
    -- Steps 9 to 11: `C1 = prod_i e(Q_i, xP_i)`, `C2 = e(R, P)`, and VALID iff `C1 = C2`.
    --
    -- The test is `e(P, R) * prod_i e(-xP_i, Q_i) = 1`, with the points of `G1` first.
    --
    -- It is the same test, by bilinearity.
    | .ok pairs => pairingCheck (#[(G1.generator, r)] ++ pairs)

/-! ## The proof-of-possession scheme (§3.3)

Signing and both verifications are the core operations under the message tag. -/

/-- Sign a message under the message tag.

The key is secret, and this function does not run in constant time. -/
def sign (sk : SecretKey) (msg : ByteArray) : Except BlsError BLSSignature := coreSign sk msg DST

/-- Verify a signature under the message tag. -/
def verify (pk : BLSPubkey) (msg : ByteArray) (sig : BLSSignature) : Bool :=
  coreVerify (packBytes pk) msg (packBytes sig) DST

/-- Verify an aggregate signature on several messages under the message tag.

The scheme does not require the messages to differ. -/
def aggregateVerify (pks : Array BLSPubkey) (msgs : Array ByteArray) (sig : BLSSignature) :
    Bool :=
  coreAggregateVerify (pks.map packBytes) msgs (packBytes sig) DST

/-- The proof of possession `SK * H'(PK)`, with `H'` the hash under the public key tag (§3.3.2).

It is the core signature of the public key under that tag.

The key is secret, and this function does not run in constant time. -/
def popProve (sk : SecretKey) : Except BlsError BLSSignature :=
  -- Step 1: `PK` is the public key of `SK`.
  --
  -- Steps 2 to 5: `Q` is the hash of `PK` to `G2` under the public key tag, and `R = SK * Q`.
  --
  -- The proof is the encoding of `R`.
  --
  -- That is the core signature of `PK` under the public key tag.
  coreSign sk ⟨(skToPk sk).toArray⟩ POP_DST

/-- Verify a proof of possession (§3.3.3).

It is the core verification of the public key as message, under the public key tag. -/
def popVerify (pk : BLSPubkey) (proof : BLSSignature) : Bool :=
  -- Steps 1 to 9 of the core verification, with the hash under the public key tag at step 6.
  coreVerify (packBytes pk) (packBytes pk) (packBytes proof) POP_DST

/-- Add one validated public key to a running point sum.

It rejects a key that fails key validation (§2.5), and reports its position in the list. -/
def addPubkeyPoint (agg : G1) (entry : BLSPubkey × Nat) : Except BlsError G1 := do
  let (pk, i) := entry
  -- Step 3: `next` is the point that `PK_i` encodes, with key validation added.
  match G1.keyValidatePoint pk with
  | .error _ => throw (.invalidPubkey (some i))
  -- Step 4: `aggregate = aggregate + next`.
  | .ok p => return G1.add agg p

/-- The sum of the validated public keys, as a point of `G1`.

These are the first steps of fast aggregate verification, §3.3.4, with key validation added.

It fails on an empty list and on a key that fails key validation. -/
def aggregatePubkeyPoint (pubkeys : Array BLSPubkey) : Except BlsError G1 := do
  -- The precondition `n >= 1`.
  if pubkeys.isEmpty then throw .emptyPubkeyList
  -- Steps 1 to 4: the sum starts at the point at infinity, so step 1 is the first addition.
  pubkeys.zipIdx.foldlM addPubkeyPoint G1.zero

/-- Sum the public keys, then verify the signature under the sum (§3.3.4).

It returns `false` on an empty list and on a key that fails key validation. -/
def fastAggregateVerify
    (pubkeys : Array BLSPubkey) (msg : ByteArray) (sig : BLSSignature) : Bool :=
  -- Steps 1 to 4: the sum of the keys, or INVALID.
  match aggregatePubkeyPoint pubkeys with
  | .error _ => false
  -- Steps 5 and 6: `PK` is the encoding of the sum, and the core verification of the signature.
  | .ok agg => verify (pointToPubkey agg) msg sig

/-! ## Ethereum wrappers

For context, the consensus-specs state these two rules in Extensions of `altair/bls.md`:
<https://github.com/ethereum/consensus-specs/blob/aa16bb4c/specs/altair/bls.md#extensions>
-/

/-- The aggregation of Ethereum public keys: the sum of the validated keys.

It fails on an empty list and on any invalid key. -/
def ethAggregatePubkeys (pubkeys : Array BLSPubkey) : Except BlsError BLSPubkey := do
  -- The list holds at least one key, and every key passes key validation.
  --
  -- The result is the sum of the keys, as points of `G1`.
  return pointToPubkey (← aggregatePubkeyPoint pubkeys)

/-- The fast aggregate verification of Ethereum.

It is the fast aggregate verification of the draft, except on an empty key list.

An empty key list passes exactly with the signature of the point at infinity. -/
def ethFastAggregateVerify
    (pubkeys : Array BLSPubkey) (msg : ByteArray) (sig : BLSSignature) : Bool :=
  -- An empty key list is VALID exactly with the encoding of the point at infinity.
  --
  -- On an empty list with another signature, the draft's verification returns INVALID anyway.
  if pubkeys.isEmpty then
    sig = G2_POINT_AT_INFINITY
  -- Otherwise, the fast aggregate verification of the draft.
  else
    fastAggregateVerify pubkeys msg sig

end EthLib.Cryptography.Bls.Signatures
