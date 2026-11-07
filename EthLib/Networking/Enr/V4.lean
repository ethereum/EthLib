module

public import EthLib.Networking.Enr.Record
public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Secp256k1.Sign

/-!
# `Networking.Enr.V4`

The "v4" identity scheme of EIP-778, from its section of that name.

Source: EIP-778, at
<https://github.com/ethereum/EIPs/blob/7622abc1c6569b7e7ade9ed957dde4ed2271cc40/EIPS/eip-778.md>.

The `id` pair names the scheme, and the `secp256k1` pair holds the compressed public key.

The signature is 64 bytes, `r` then `s`, on the Keccak-256 hash of the RLP content.

The node ID is the Keccak-256 hash of the uncompressed public key.

The EIP does not say which uncompressed form.

Here it is the 64 bytes `x` then `y`, without the SEC 1 prefix `04`.

That form gives the node ID of the EIP's test vector, and the form with `04` does not.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Serialization.Rlp
open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1

/-- The name of the scheme, `v4`, in ASCII. -/
def SCHEME_V4 : ByteArray := ⟨#[0x76, 0x34]⟩

/-- The key `secp256k1`, in ASCII. -/
def KEY_SECP256K1 : ByteArray := ⟨#[0x73, 0x65, 0x63, 0x70, 0x32, 0x35, 0x36, 0x6b, 0x31]⟩

/-- The value of the pair with the key `key`, if the record has one. -/
def Enr.get (r : Enr) (key : ByteArray) : Option Item :=
  (r.pairs.find? (·.1 = key)).map (·.2)

/-- The public key of a "v4" record.

It fails unless the scheme is "v4" and the `secp256k1` value is a compressed point.

A compressed point is 33 bytes, and it must lie on the curve. -/
def Enr.publicKeyV4 (r : Enr) : Except EnrError Point :=
  match r.get KEY_ID with
  | none => .error .missingId
  | some id =>
    if id = .bytes SCHEME_V4 then
      match r.get KEY_SECP256K1 with
      | some (.bytes key) =>
        -- The EIP gives the key in the compressed form only.
        if key.size = 33 then (Point.decode key).mapError fun _ => .invalidPublicKey
        else .error .invalidPublicKey
      | _ => .error .invalidPublicKey
    else .error .unknownScheme

/-- Whether a record is a valid "v4" record: its signature verifies under its public key.

The signature is on the Keccak-256 hash of the RLP encoding of the content.

The RLP decoder accepts only canonical bytes, so for a decoded record this is what was signed.

ECDSA accepts a high `s` here, since the EIP adds no low-s rule. -/
def verifyV4 (r : Enr) : Bool :=
  match r.publicKeyV4, Serialization.Rlp.encode r.content with
  | .ok q, .ok content =>
    if r.signature.size = 64 then
      let sig := r.signature.data.toList
      Ecdsa.verify q (Hash.Keccak.keccak256 content)
        (Base.bytesToNat (sig.take 32)) (Base.bytesToNat (sig.drop 32))
    else false
  | _, _ => false

/-- The node ID of a "v4" record: the Keccak-256 hash of `x` then `y` of its public key.

It does not check the signature. -/
def nodeId (r : Enr) : Except EnrError (Vector UInt8 32) := do
  match ← r.publicKeyV4 with
  | .affine x y => return Hash.Keccak.keccak256 (publicKeyBytes x y)
  -- The point decoder never returns the point at infinity.
  | .infinity => throw .invalidPublicKey

/-- The record, signed with the private key `sk` by the "v4" scheme.

It signs the Keccak-256 hash of the RLP encoding of the content, with the nonce of RFC 6979.

The signature is `r` then `s`, each in 32 big-endian bytes, and `s` is low.

It keeps the sequence number and the pairs.

So the caller puts the `id` pair and the `secp256k1` pair of `sk G` among them, in key order. -/
def signV4 (sk : Fn) (r : Enr) : Except EnrError Enr := do
  let content ← (Serialization.Rlp.encode r.content).mapError .rlp
  let (rr, ss, _) ← (Ecdsa.sign sk (Hash.Keccak.keccak256 content)).mapError fun _ => .signing
  return { r with signature := ⟨(Base.natToBytes 32 rr.val ++ Base.natToBytes 32 ss.val).toArray⟩ }

/-- The pairs with one more pair, placed before the first pair whose key is larger. -/
def insertPair (p : ByteArray × Item) : List (ByteArray × Item) → List (ByteArray × Item)
  | [] => [p]
  | q :: rest => if keyLt p.1 q.1 then p :: q :: rest else q :: insertPair p rest

/-- A signed "v4" record of the private key `sk`, with a sequence number and other pairs.

It adds the pair `id` with `v4` and the pair `secp256k1` with the compressed form of `sk G`.

The keys must then strictly increase, so the other pairs come in key order and use neither key.

It fails on a record of more than 300 bytes, which the decoder rejects. -/
def makeRecordV4 (sk : Fn) (seq : UInt64) (pairs : List (ByteArray × Item)) :
    Except EnrError Enr := do
  let key := (Point.mul sk Point.generator).encodeCompressed
  let all := insertPair (KEY_ID, .bytes SCHEME_V4) (insertPair (KEY_SECP256K1, .bytes key) pairs)
  checkKeys all
  let r ← signV4 sk ⟨.empty, seq, all⟩
  let bytes ← r.encode.mapError .rlp
  if MAX_RECORD_SIZE < bytes.size then throw (.tooLarge bytes.size)
  return r

end EthLib.Networking.Enr
