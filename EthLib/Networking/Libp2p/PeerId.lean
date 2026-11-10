module

public import EthLib.Base.BigEndian
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Cryptography.Secp256k1.Sign

/-!
# libp2p secp256k1 identity keys

Ethereum's libp2p identity uses the secp256k1 profile of [peer IDs][peerids].

Its public-key protobuf is deterministic, and its peer ID is an identity multihash.

So a peer ID holds the key itself, and decodes back to it.

Message signatures use SHA-256, low-s ECDSA and strict DER, without a transaction sighash byte.

The DER and low-s rules are rules 1 and 5 of [BIP 62, "New rules"][bip62], which the profile cites.

[peerids]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/peer-ids/peer-ids.md#secp256k1
[bip62]: https://github.com/bitcoin/bips/blob/24e96e870fffaa257b465ce1f0370c14aac588e8/bip-0062.mediawiki#new-rules
-/

@[expose] public section

namespace EthLib.Networking.Libp2p

open EthLib.Cryptography.Secp256k1

/-- A malformed key, peer ID, secret or DER signature. -/
inductive IdentityError where
  | publicKey
  | peerId
  | privateKey
  | signature
  | signing (error : Secp256k1Error)
deriving Repr, DecidableEq

/-- Deterministic protobuf `PublicKey`, type 2 and 33 compressed bytes, peer-IDs "Keys". -/
def encodePublicKey (point : Point) : ByteArray :=
  ⟨#[0x08, 0x02, 0x12, 0x21]⟩ ++ point.encodeCompressed

/-- Accept exactly the canonical secp256k1 protobuf and a usable compressed point. -/
def decodePublicKey (key : ByteArray) : Except IdentityError Point := do
  if key.size != 37 then throw .publicKey
  let point ← (Point.decode (key.extract 4 37)).mapError fun _ => .publicKey
  if encodePublicKey point = key then return point else throw .publicKey

/-- The peer ID of a secp256k1 public key, peer-IDs "Peer Ids".

The key is a point of the curve other than infinity, as every public key is.

Its protobuf has 37 bytes, which is at most 42, so the peer ID is its identity multihash.

That multihash is the identity code 0, the length 37, then the protobuf. -/
def peerId (point : Point) : ByteArray := ⟨#[0x00, 0x25]⟩ ++ encodePublicKey point

/-- The public key that a secp256k1 peer ID names.

The peer ID must be the binary identity multihash of a canonical 37-byte key protobuf.

Text forms and hashed peer IDs of longer keys are not read. -/
def decodePeerId (id : ByteArray) : Except IdentityError Point :=
  match id.data.toList with
  | 0x00 :: 0x25 :: key => decodePublicKey ⟨key.toArray⟩
  | _ => .error .peerId

/-- Derive and serialize the public key of a secret in [1, n), with n the secp256k1 group order.

The secret key must stay private, and this function makes no constant-time claim. -/
def publicKey (secret : Vector UInt8 32) : Except IdentityError ByteArray :=
  let n := EthLib.Base.bytesToNat secret.toList
  if h : 0 < n ∧ n < Fn.modulus then
    .ok (encodePublicKey (Point.mul ⟨n, h.2⟩ .generator))
  else .error .privateKey

/-- A positive DER INTEGER with the required leading zero when its high bit is set, BIP 62. -/
def derInteger (n : Nat) : List UInt8 :=
  let bytes := (EthLib.Base.natToBytes 32 n).dropWhile (· == 0)
  let bytes := match bytes with
    | [] => [0]
    | b :: _ => if b.toNat ≥ 128 then 0 :: bytes else bytes
  [0x02, UInt8.ofNat bytes.length] ++ bytes

/-- The DER sequence of the two ECDSA scalars, without a transaction sighash flag, BIP 62. -/
def encodeSignature (r s : Nat) : ByteArray :=
  let integers := derInteger r ++ derInteger s
  ⟨([0x30, UInt8.ofNat integers.length] ++ integers).toArray⟩

/-- Decode a strict DER sequence and require the secp256k1 low-s scalar ranges, BIP 62. -/
def decodeSignature (signature : ByteArray) : Except IdentityError (Nat × Nat) := do
  match signature.data.toList with
  | 0x30 :: total :: 0x02 :: rLength :: rest =>
    if total.toNat + 2 != signature.size then throw .signature
    let rBytes := rest.take rLength.toNat
    match rest.drop rLength.toNat with
    | 0x02 :: sLength :: sBytes =>
      if sLength.toNat != sBytes.length then throw .signature
      let r := EthLib.Base.bytesToNat rBytes
      let s := EthLib.Base.bytesToNat sBytes
      if 0 < r ∧ r < Fn.modulus ∧ 0 < s ∧ s ≤ Fn.modulus / 2 ∧
          encodeSignature r s = signature then
        return (r, s)
      else throw .signature
    | _ => throw .signature
  | _ => throw .signature

/-- Sign SHA-256 of the message, then write its low-s signature in DER, peer-IDs "Secp256k1".

The secret key must stay private, and this function makes no constant-time claim. -/
def sign (secret : Vector UInt8 32) (message : ByteArray) : Except IdentityError ByteArray := do
  let n := EthLib.Base.bytesToNat secret.toList
  if h : 0 < n ∧ n < Fn.modulus then
    let (r, s, _) ← (Ecdsa.sign ⟨n, h.2⟩
      (EthLib.Cryptography.Hash.Sha256.hash32 message)).mapError IdentityError.signing
    return encodeSignature r.val s.val
  else throw .privateKey

/-- Check the canonical key and DER signature on SHA-256 of the message, peer-IDs "Secp256k1". -/
def verify (publicKey message signature : ByteArray) : Bool :=
  match decodePublicKey publicKey, decodeSignature signature with
  | .ok point, .ok (r, s) =>
    Ecdsa.verify point (EthLib.Cryptography.Hash.Sha256.hash32 message) r s
  | _, _ => false

end EthLib.Networking.Libp2p
