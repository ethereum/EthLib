import EthLib.Cryptography.Xmss.Verify
import EthLib.Cryptography.Xmss.Errors
import Ssz.Codec.Deserialize

/-!
# `Xmss.Serialization`

SSZ encodings of the public key and the signature.

Both are containers of fixed-size byte vectors.
So the encoding is the fields concatenated, with no offsets and no length prefixes.
-/

namespace EthLib.Cryptography.Xmss

open Constants

/-- The public key layout, 32 bytes.

```text
    [ Merkle root: 16 | public parameter: 16 ]
```
-/
def publicKeySsz : Ssz.Desc :=
  .container ["merkle_root", "public_param"]
    [.byteVector DIGEST_LEN, .byteVector PUBLIC_PARAM_LEN]

/-- The signature layout, 1208 bytes.

```text
    [ randomizer: 24 | 42 chain values: 672 | 32 siblings: 512 ]
```

- The randomizer comes first, as in the paper's signature tuple.
- Chain values are in chain order.
- Siblings run from the leaf up to the root.
-/
def signatureSsz : Ssz.Desc :=
  .container ["randomness", "chain_values", "merkle_path"]
    [.byteVector RANDOMNESS_LEN, .byteVector (V * DIGEST_LEN),
      .byteVector (LOG_LIFETIME * DIGEST_LEN)]

/-- The public key as the codec's untyped value. -/
def publicKeySszValue (pk : PublicKey) : Ssz.Value :=
  -- The lengths are dropped here and checked again by the codec.
  .seq [.bytes pk.merkleRoot.toArray, .bytes pk.publicParam.toArray]

/-- The signature as the codec's untyped value. -/
def signatureSszValue (sig : Signature) : Ssz.Value :=
  -- Each digest list becomes one byte field, digests kept in order.
  .seq [.bytes sig.randomness.toArray, .bytes sig.chainElements.flatten.toArray,
    .bytes sig.merklePath.flatten.toArray]

/-- Encode a public key as 32 bytes. -/
def encodePublicKey (pk : PublicKey) : ByteArray :=
  match Ssz.serialize publicKeySsz (publicKeySszValue pk) with
  | .ok bytes => ⟨bytes⟩
  -- Unreachable: both fields have their declared lengths.
  | .error _ => .empty

/-- Encode a signature as 1208 bytes. -/
def encodeSignature (sig : Signature) : ByteArray :=
  match Ssz.serialize signatureSsz (signatureSszValue sig) with
  | .ok bytes => ⟨bytes⟩
  -- Unreachable: all three fields have their declared lengths.
  | .error _ => .empty

/-- Cut a byte field into consecutive 16-byte digests. -/
def splitDigests {n : Nat} (bytes : Vector UInt8 (n * DIGEST_LEN)) : Vector Digest n :=
  -- Byte j of digest i sits at position 16 i + j of the field.
  Vector.ofFn fun i => Vector.ofFn fun j => bytes[i.val * DIGEST_LEN + j.val]'(by
    -- With i < n and j < 16, that position is below 16 n.
    have hi := i.isLt
    have hj := j.isLt
    simp only [DIGEST_LEN] at *
    omega)

/-- The public key held by a decoded codec value, if it has the right shape. -/
def publicKeyFromSsz? : Ssz.Value → Option PublicKey
  | .seq [.bytes root, .bytes param] => do
    -- Recover each field's length in its type.
    let root ← unpackBytes? DIGEST_LEN ⟨root⟩
    let param ← unpackBytes? PUBLIC_PARAM_LEN ⟨param⟩
    return ⟨root, param⟩
  | _ => none

/-- The signature held by a decoded codec value, if it has the right shape. -/
def signatureFromSsz? : Ssz.Value → Option Signature
  | .seq [.bytes randomizer, .bytes chains, .bytes siblings] => do
    -- Recover each field's length in its type, then cut the digest lists apart.
    let randomizer ← unpackBytes? RANDOMNESS_LEN ⟨randomizer⟩
    let chains ← unpackBytes? (V * DIGEST_LEN) ⟨chains⟩
    let siblings ← unpackBytes? (LOG_LIFETIME * DIGEST_LEN) ⟨siblings⟩
    return ⟨splitDigests chains, randomizer, splitDigests siblings⟩
  | _ => none

/-- Decode a public key from 32 bytes.

Length is the only check: every 32-byte string is a public key.
-/
def decodePublicKey (bytes : ByteArray) : Except XmssError PublicKey :=
  match Ssz.deserialize publicKeySsz bytes.data with
  | .ok value =>
    -- The codec has already checked each field's length, so this always succeeds.
    match publicKeyFromSsz? value with
    | some pk => .ok pk
    | none => .error (.badPublicKeySize bytes.size)
  -- With only fixed-size fields, the codec rejects nothing but a wrong total length.
  | .error _ => .error (.badPublicKeySize bytes.size)

/-- Decode a signature from 1208 bytes.

Length is the only check: every 1208-byte string decodes.
Decoding does not verify the signature.
-/
def decodeSignature (bytes : ByteArray) : Except XmssError Signature :=
  match Ssz.deserialize signatureSsz bytes.data with
  | .ok value =>
    -- The codec has already checked each field's length, so this always succeeds.
    match signatureFromSsz? value with
    | some sig => .ok sig
    | none => .error (.badSignatureSize bytes.size)
  -- With only fixed-size fields, the codec rejects nothing but a wrong total length.
  | .error _ => .error (.badSignatureSize bytes.size)

end EthLib.Cryptography.Xmss
