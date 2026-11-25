module

public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Sec1

/-!
# `Secp256r1.Encoding`

The two encodings of a point as bytes, by SEC 1 v2 §2.3.3, and the decoding of a public key.

The compressed form has 33 bytes, and the uncompressed form 65.

A public key is decoded by SEC 1 v2 §2.3.4, then validated by §3.2.2.1, which rejects `O`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- What SEC 1 reads from `Fp`: an element takes 32 octets, and its root for `p = 3 mod 4`. -/
def sec1 : Sec1.Params Fp.modulus := ⟨32, by decide, by decide, by decide, Sec1.sqrt3Mod4⟩

/-- A coordinate as 32 bytes, by SEC 1 v2 §2.3.5. -/
abbrev Fp.toBytes (x : Fp) : ByteArray := Sec1.fieldToBytes sec1 x

namespace Point

/-- The point as 33 bytes, by SEC 1 v2 §2.3.3 with point compression, or `O` as one byte. -/
abbrev encodeCompressed (q : Point) : ByteArray := Sec1.encode sec1 true q

/-- The point as 65 bytes, by SEC 1 v2 §2.3.3 without point compression, or `O` as one byte. -/
abbrev encodeUncompressed (q : Point) : ByteArray := Sec1.encode sec1 false q

/-- Decode a public key from either form: SEC 1 v2 §2.3.4, then the validation of §3.2.2.1.

Validation rejects `O`, and skips the check `n Q = O`, since the cofactor is 1. -/
def decode (bytes : ByteArray) : Except Sec1.Sec1Error Point :=
  Sec1.decode sec1 bytes >>= Sec1.validatePublicKey Fn.modulus 1

/-- Decode a public key in the uncompressed form only, or `none`.

TLS 1.3 key shares and the keys of the libp2p TLS handshake accept no other form. -/
def decodeUncompressed (bytes : ByteArray) : Option Point :=
  -- The uncompressed form `04 || X || Y` has `2 * 32 + 1` octets.
  if bytes.size = 65 then (decode bytes).toOption else none

end Point

end EthLib.Cryptography.Secp256r1
