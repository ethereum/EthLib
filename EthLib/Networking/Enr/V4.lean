module

public import EthLib.Networking.Enr.Record
public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Secp256k1.Sign
public import EthLib.Cryptography.Ecdsa.Encoding

/-!
# `Networking.Enr.V4`

The v4 identity scheme of node records: the signature and the node ID.

The source is the section v4 Identity Scheme of [EIP-778][eip-778].

[eip-778]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-778.md#v4-identity-scheme
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

/-- The public key of a v4 record. -/
def Enr.publicKeyV4 (r : Enr) : Except EnrError Point :=
  -- `id` is the name of the identity scheme, and every record has it.
  match r.get KEY_ID with
  | none => .error .missingId
  | some id =>
    -- The scheme is v4.
    if id = .bytes SCHEME_V4 then
      -- `secp256k1`: the compressed secp256k1 public key, 33 bytes.
      match r.get KEY_SECP256K1 with
      | some (.bytes key) =>
        -- The EIP gives the key in the compressed form only.
        --
        -- EthLib also requires a point of the curve.
        if key.size = 33 then (Point.decode key).mapError fun _ => .invalidPublicKey
        else .error .invalidPublicKey
      -- Without a `secp256k1` byte string, the record has no public key.
      | _ => .error .invalidPublicKey
    -- The EIP defines the v4 scheme only, so EthLib knows no other.
    else .error (.unknownScheme id)

/-- Whether a record is a valid v4 record: its signature verifies under its public key.

The signature is on the Keccak-256 hash of the RLP encoding of the content.

The RLP decoder accepts only canonical bytes, so for a decoded record this is what was signed.

ECDSA accepts a high `s` here, since the EIP adds no low-s rule. -/
def verifyV4 (r : Enr) : Bool :=
  -- The public key in the `secp256k1` pair, and `content = [seq, k, v, ...]`.
  match r.publicKeyV4, Serialization.Rlp.encode r.content with
  | .ok q, .ok content =>
    -- The signature is 64 bytes, `r || s`, with the recovery ID `v` omitted.
    match Cryptography.Ecdsa.read? r.signature with
    -- Check that the signature of `keccak256(content)` was made by that public key.
    | some (rr, ss) => Ecdsa.verify q (Hash.Keccak.keccak256 content) rr ss
    | none => false
  | _, _ => false

/-- The node ID of a v4 record: the Keccak-256 hash of `x` then `y` of its public key.

It does not check the signature. -/
def nodeId (r : Enr) : Except EnrError (Vector UInt8 32) := do
  match ← r.publicKeyV4 with
  -- To derive a node address, take the keccak256 hash of the uncompressed public key.
  --
  -- The EIP does not say which uncompressed form.
  --
  -- EthLib takes the 64 bytes `x || y`, without the SEC 1 prefix `04`.
  --
  -- That form gives the node ID of the test vector of the EIP, and the form with `04` does not.
  | .affine x y => return Hash.Keccak.keccak256 (publicKeyBytes x y)
  -- The point decoder never returns the point at infinity.
  | .infinity => throw .invalidPublicKey

/-- The record, signed with the private key `sk` by the v4 scheme.

It keeps the sequence number and the pairs.

So the caller puts the `id` pair and the `secp256k1` pair of `sk G` among them, in key order. -/
def signV4 (sk : Fn) (r : Enr) : Except EnrError Enr := do
  -- RLP Encoding: `content = [seq, k, v, ...]`.
  let content ← (Serialization.Rlp.encode r.content).mapError .rlp
  -- Apply keccak256 to `content`, then create a signature of the hash.
  --
  -- The EIP names no nonce.
  --
  -- EthLib takes the deterministic nonce of RFC 6979 and the low `s` of EIP-2.
  let (rr, ss, _) ← (Ecdsa.sign sk (Hash.Keccak.keccak256 content)).mapError fun _ => .signing
  -- The 64-byte signature is `r || s`, each in 32 big-endian bytes, and `v` is omitted.
  --
  -- RLP Encoding: `record = [signature, seq, k, v, ...]`.
  return { r with signature := Base.packBytes (Cryptography.Ecdsa.toBytes rr.val ss.val) }

/-- The pairs with one more pair, placed before the first pair whose key is larger. -/
def insertPair (p : ByteArray × Item) : List (ByteArray × Item) → List (ByteArray × Item)
  -- The key/value pairs must be sorted by key, so the new pair takes its place in that order.
  | [] => [p]
  | q :: rest => if keyLt p.1 q.1 then p :: q :: rest else q :: insertPair p rest

/-- A signed v4 record of the private key `sk`, with a sequence number and other pairs.

The other pairs come in key order and use neither the key `id` nor the key `secp256k1`.

It fails on a record of more than 300 bytes, which the decoder rejects. -/
def makeRecordV4 (sk : Fn) (seq : UInt64) (pairs : List (ByteArray × Item)) :
    Except EnrError Enr := do
  -- `secp256k1`: the compressed public key `sk G`, 33 bytes.
  let key := (Point.mul sk Point.generator).encodeCompressed
  -- `id` = v4, and `secp256k1` = that key, each inserted in key order.
  let all := insertPair (KEY_ID, .bytes SCHEME_V4) (insertPair (KEY_SECP256K1, .bytes key) pairs)
  -- The key/value pairs must be sorted by key and must be unique.
  checkKeys all
  -- `signature = sign(content)`, by the v4 scheme.
  let r ← signV4 sk ⟨.empty, seq, all⟩
  let bytes ← r.encode.mapError .rlp
  -- RLP Encoding: at most 300 bytes, so EthLib refuses a larger record here, as the decoder would.
  if MAX_RECORD_SIZE < bytes.size then throw (.tooLarge bytes.size)
  return r

end EthLib.Networking.Enr
