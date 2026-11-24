module

public import EthLib.Base.ByteOrder
public import EthLib.Serialization.Der
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Cryptography.Secp256k1.Sign

/-!
# libp2p secp256k1 identity keys

Ethereum's libp2p identity uses the secp256k1 profile of [peer IDs][peerids].

Its peer ID is an identity multihash, so it holds the key itself, and decodes back to it.

Message signatures have no transaction sighash byte.

The profile cites BIP 62 for its DER and low-s rules.

They are rules 1 and 5 of the section New rules of [BIP 62][bip62].

[peerids]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/peer-ids/peer-ids.md#secp256k1
[bip62]: https://github.com/bitcoin/bips/blob/24e96e870fffaa257b465ce1f0370c14aac588e8/bip-0062.mediawiki#new-rules
-/

@[expose] public section

namespace EthLib.Networking.Libp2p

open EthLib.Cryptography.Secp256k1
open EthLib.Serialization

/-- A malformed key, peer ID, secret or DER signature, or a failure to sign. -/
inductive IdentityError where
  /-- The bytes are not the canonical protobuf of a compressed point of the curve. -/
  | publicKey
  /-- The bytes do not start with the identity code 0 and the length 37.

  The field holds the first two bytes, or fewer when the input is shorter. -/
  | peerId (header : List UInt8)
  /-- The secret is 0, or, in the exports, its bytes give a value at least the group order. -/
  | privateKey
  /-- The bytes are not a strict DER signature with r in [1, n) and s in [1, n/2]. -/
  | signature
  /-- ECDSA signing failed. -/
  | signing (error : Secp256k1Error)
deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def IdentityError.code : IdentityError → UInt32
  | .publicKey => 1
  | .peerId _ => 2
  | .privateKey => 3
  | .signature => 4
  | .signing _ => 5

/-- The deterministic protobuf `PublicKey` of a point, from the section Keys of peer-IDs. -/
def encodePublicKey (point : Point) : ByteArray :=
  -- The fields in tag order, all included, with minimal varints.
  --
  -- 0x08 0x02 is field 1, the key type.
  --
  -- Its value is the key type Secp256k1, 2.
  --
  -- 0x12 0x21 is field 2, the key data, of 33 bytes: the standard Bitcoin EC encoding of the key.
  --
  -- The profile does not say compressed; EthLib takes the 33 compressed bytes of SEC 1 v2 §2.3.3.
  --
  -- The test vector of the public key in the section Keys has that form.
  ⟨#[0x08, 0x02, 0x12, 0x21]⟩ ++ point.encodeCompressed

/-- Accept exactly the canonical secp256k1 protobuf and a usable compressed point. -/
def decodePublicKey (key : ByteArray) : Except IdentityError Point := do
  -- The canonical protobuf has 4 header bytes and 33 key bytes.
  if key.size != 37 then throw .publicKey
  -- The 33 bytes after the header must be a point of the curve, other than infinity.
  let point ← (Point.decode (key.extract 4 37)).mapError fun _ => .publicKey
  -- Encoding is deterministic, so EthLib accepts only the bytes it would write itself.
  --
  -- That rejects another key type, other field encodings and an uncompressed point.
  if encodePublicKey point = key then return point else throw .publicKey

/-- The peer ID of a secp256k1 public key, from the section Peer Ids of peer-IDs.

The key is a point of the curve other than infinity, as every public key is. -/
def peerId (point : Point) : ByteArray :=
  -- Encode the public key as the section Keys describes, in 37 bytes.
  --
  -- 37 is at most 42, so the peer ID is the identity multihash of those bytes: no hashing.
  --
  -- The multihash format is the code byte 0x00, the varint length 0x25, then the bytes.
  ⟨#[0x00, 0x25]⟩ ++ encodePublicKey point

/-- The public key that a secp256k1 peer ID names.

The peer ID must be the binary identity multihash of a canonical 37-byte key protobuf.

Text forms and hashed peer IDs of longer keys are not read. -/
def decodePeerId (id : ByteArray) : Except IdentityError Point :=
  match id.data.toList with
  -- The identity multihash header, code 0x00 and length 37, then the key protobuf.
  | 0x00 :: 0x25 :: key => decodePublicKey ⟨key.toArray⟩
  -- Any other header names another key type, or a key over 42 bytes hashed with SHA-256.
  | bytes => .error (.peerId (bytes.take 2))

/-- Derive and serialize the public key of a secp256k1 secret scalar, which must be nonzero.

The secret key must stay private, and this function makes no constant-time claim. -/
def publicKey (secret : Fn) : Except IdentityError ByteArray :=
  -- A secret of 0 has no public key other than infinity, so it is rejected.
  if secret = 0 then .error .privateKey
  -- The public key `secret * G`, in its protobuf.
  else .ok (encodePublicKey (Point.mul secret .generator))

/-- Decode a strict DER sequence and require the secp256k1 low-s scalar ranges, BIP 62. -/
def decodeSignature (signature : ByteArray) : Except IdentityError (Nat × Nat) :=
  -- BIP 62 rule 1: a strict DER sequence of two positive integers `r` and `s`.
  match Der.decodeEcdsaScalars signature with
  | some (r, s) =>
    -- `r < n`, as ECDSA requires, and BIP 62 rule 5, low `s`: `s <= n / 2`, for the order `n`.
    if r < Fn.modulus ∧ s ≤ Fn.modulus / 2 then .ok (r, s) else .error .signature
  | none => .error .signature

/-- Sign a message with a secret key, from the section Secp256k1 of peer-IDs.

The secret key must stay private, and this function makes no constant-time claim. -/
def sign (secret : Fn) (message : ByteArray) : Except IdentityError ByteArray := do
  -- A secret of 0 is not a key.
  if secret = 0 then throw .privateKey
  -- Hash the message with SHA-256, then sign it with ECDSA, low `s` as BIP 62 asks.
  --
  -- The recovery bit is dropped: the signature is only `(r, s)`.
  let (r, s, _) ← (Ecdsa.sign secret
    (EthLib.Cryptography.Hash.Sha256.hash32 message)).mapError IdentityError.signing
  -- The standard Bitcoin encoding: the DER sequence of `r` and `s`.
  return Der.encodeEcdsaSignature r.val s.val

/-- Check a signature of a message under a key protobuf, from the section Secp256k1 of peer-IDs. -/
def verify (publicKey message signature : ByteArray) : Bool :=
  -- The canonical key protobuf, and the strict DER low-s signature.
  match decodePublicKey publicKey, decodeSignature signature with
  -- ECDSA verification of `(r, s)` on the SHA-256 hash of the message.
  | .ok point, .ok (r, s) =>
    Ecdsa.verify point (EthLib.Cryptography.Hash.Sha256.hash32 message) r s
  -- A malformed key or signature never verifies.
  | _, _ => false

end EthLib.Networking.Libp2p
