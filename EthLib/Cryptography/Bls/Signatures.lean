module

public import EthLib.Base.Bytes
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

/-- The compressed encoding of the `G2` point at infinity. -/
def G2_POINT_AT_INFINITY : ByteArray := G2.infinityBytes

/-- The same encoding, as a signature.

The beacon chain uses it where a message carries no signature. -/
def infinitySignature : BLSSignature :=
  ⟨G2_POINT_AT_INFINITY.data, by simp [G2_POINT_AT_INFINITY, G2.infinityBytes]⟩

/-! ## Keys and encodings -/

/-- A secret key: an integer `SK` with `1 <= SK < r` (§2.3). -/
abbrev SecretKey := { sk : Fr // sk ≠ 0 }

/-- Decode a secret key from 32 big-endian bytes.

It rejects a wrong length, an integer `>= r` and zero. -/
def SecretKey.fromBytes (bytes : ByteArray) : Except BlsError SecretKey :=
  match Fr.fromBytesBE bytes with
  | .error _ => .error .invalidSecretKey
  | .ok sk => if h : sk = 0 then .error .invalidSecretKey else .ok ⟨sk, h⟩

/-- The public key of a point, in the minimal-pubkey-size variant (§2.2). -/
def pointToPubkey (p : G1) : BLSPubkey := ⟨(G1.compress p).data, G1.size_compress p⟩

/-- The signature of a point, in the minimal-pubkey-size variant (§2.2). -/
def pointToSignature (p : G2) : BLSSignature := ⟨(G2.compress p).data, G2.size_compress p⟩

/-- The public key `SK * P` of a secret key (§2.4).

The key is secret, and this function does not run in constant time. -/
def skToPk (sk : SecretKey) : BLSPubkey := pointToPubkey (G1.mul G1.generator sk.val)

/-- The subgroup check of a signature point (§2.7, step 3). -/
def signatureSubgroupCheck (sig : G2) : Bool := G2.inSubgroup sig

/-! ## Core operations -/

/-- The core signature `SK * H(message)`, with `H` the hash to `G2` under `dst` (§2.6).

The key is secret, and this function does not run in constant time.

The error comes from the hash to curve, which never fails. -/
def coreSign (sk : SecretKey) (msg dst : ByteArray) : Except BlsError BLSSignature := do
  let q ← HashToCurve.hashToG2 msg dst
  return pointToSignature (G2.mul q sk.val)

/-- The core verification: check `e(P, R) = e(PK, H(message))` (§2.7).

It returns `false` on any invalid input. -/
def coreVerify (pk msg sig dst : ByteArray) : Bool :=
  match G2.uncompress sig with
  | .error _ => false
  | .ok r =>
    signatureSubgroupCheck r &&
    -- Key validation returns the public key as a point.
    match G1.keyValidatePoint pk with
    | .error _ => false
    | .ok xP =>
      match HashToCurve.hashToG2 msg dst with
      | .error _ => false
      | .ok q => pairingCheck #[(G1.generator, r), (G1.neg xP, q)]

/-- The compressed sum of the signatures (§2.8).

It fails on an empty list and on a signature that does not decode.

As in the draft, it does not check that a signature lies in the subgroup. -/
def aggregate (sigs : Array BLSSignature) : Except BlsError BLSSignature := do
  if sigs.isEmpty then throw .emptySignatureList
  -- Adding a point to the point at infinity returns that point exactly.
  let agg ← sigs.foldlM
    (fun agg sig => return G2.add agg (← G2.uncompress (packBytes sig))) G2.zero
  return pointToSignature agg

/-- The core aggregate verification: check `e(P, R) = prod_i e(PK_i, H(message_i))` (§2.9).

It returns `false` on an empty list, on lists of two sizes and on any invalid input. -/
def coreAggregateVerify (pks msgs : Array ByteArray) (sig dst : ByteArray) : Bool :=
  if pks.isEmpty || pks.size != msgs.size then false else
  match G2.uncompress sig with
  | .error _ => false
  | .ok r =>
    signatureSubgroupCheck r &&
    -- One pair `(-PK_i, H(message_i))` for each key, so that the product of all pairs is 1.
    match (pks.zip msgs).mapM (fun (pk, msg) => do
        let xP ← G1.keyValidatePoint pk
        let q ← HashToCurve.hashToG2 msg dst
        return (G1.neg xP, q)) with
    | .error _ => false
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
  coreSign sk ⟨(skToPk sk).toArray⟩ POP_DST

/-- Verify a proof of possession (§3.3.3).

It is the core verification of the public key as message, under the public key tag. -/
def popVerify (pk : BLSPubkey) (proof : BLSSignature) : Bool :=
  coreVerify (packBytes pk) (packBytes pk) (packBytes proof) POP_DST

/-- Add one validated public key to a running point sum.

It rejects a key that fails key validation (§2.5), and reports its position in the list. -/
def addPubkeyPoint (agg : G1) (entry : BLSPubkey × Nat) : Except BlsError G1 := do
  let (pk, i) := entry
  match G1.keyValidatePoint (packBytes pk) with
  | .error _ => throw (.invalidPubkey (some i))
  | .ok p => return G1.add agg p

/-- The sum of the validated public keys, as a point of `G1`.

These are the first steps of fast aggregate verification, §3.3.4, with key validation added.

It fails on an empty list and on a key that fails key validation. -/
def aggregatePubkeyPoint (pubkeys : Array BLSPubkey) : Except BlsError G1 := do
  if pubkeys.isEmpty then throw .emptyPubkeyList
  pubkeys.zipIdx.foldlM addPubkeyPoint G1.zero

/-- Sum the public keys, then verify the signature under the sum (§3.3.4).

It returns `false` on an empty list and on a key that fails key validation. -/
def fastAggregateVerify
    (pubkeys : Array BLSPubkey) (msg : ByteArray) (sig : BLSSignature) : Bool :=
  match aggregatePubkeyPoint pubkeys with
  | .error _ => false
  | .ok agg => verify (pointToPubkey agg) msg sig

/-! ## Ethereum wrappers -/

/-- The aggregation of Ethereum public keys: the sum of the validated keys.

It fails on an empty list and on any invalid key. -/
def ethAggregatePubkeys (pubkeys : Array BLSPubkey) : Except BlsError BLSPubkey := do
  return pointToPubkey (← aggregatePubkeyPoint pubkeys)

/-- The fast aggregate verification of Ethereum.

It is the fast aggregate verification of the draft, except on an empty key list.

An empty key list passes exactly with the signature of the point at infinity. -/
def ethFastAggregateVerify
    (pubkeys : Array BLSPubkey) (msg : ByteArray) (sig : BLSSignature) : Bool :=
  if pubkeys.isEmpty then
    sig = infinitySignature
  else
    fastAggregateVerify pubkeys msg sig

end EthLib.Cryptography.Bls.Signatures
