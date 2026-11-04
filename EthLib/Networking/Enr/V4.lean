module

public import EthLib.Networking.Enr.Record
public import EthLib.Cryptography.Secp256k1.Address
public import EthLib.Cryptography.Secp256k1.Ecdsa

/-!
# `Networking.Enr.V4`

The "v4" identity scheme of EIP-778, from its section of that name.

Source: [EIP-778](https://github.com/ethereum/EIPs/blob/7622abc1c6569b7e7ade9ed957dde4ed2271cc40/EIPS/eip-778.md).

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

/-- The key `id`, in ASCII. -/
def KEY_ID : ByteArray := ⟨#[0x69, 0x64]⟩

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
        (ofBytesBE (sig.take 32)) (ofBytesBE (sig.drop 32))
    else false
  | _, _ => false

/-- The node ID of a "v4" record: the Keccak-256 hash of `x` then `y` of its public key.

It does not check the signature. -/
def nodeId (r : Enr) : Except EnrError (Vector UInt8 32) := do
  match ← r.publicKeyV4 with
  | .affine x y => return Hash.Keccak.keccak256 (publicKeyBytes x y)
  -- The point decoder never returns the point at infinity.
  | .infinity => throw .invalidPublicKey

end EthLib.Networking.Enr
