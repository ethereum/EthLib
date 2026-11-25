module

public import EthLib.Cryptography.Secp256k1.Curve
public import EthLib.Cryptography.Secp256k1.Errors
public import EthLib.Cryptography.Secp256k1.Sqrt
public import EthLib.Cryptography.Sec1

/-!
# `Secp256k1.Encoding`

The two encodings of a point as bytes, by SEC 1 v2 §2.3.3, and the decoding of a public key.

The compressed form has 33 bytes, and the uncompressed form 65.

A public key is decoded by SEC 1 v2 §2.3.4, then validated by §3.2.2.1, which rejects `O`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- What SEC 1 reads from `Fp`: an element takes 32 octets, and its square root. -/
def sec1 : Sec1.Params Fp.modulus := ⟨32, by decide, by decide, by decide, Fp.sqrt⟩

/-- A coordinate as 32 bytes, by SEC 1 v2 §2.3.5. -/
abbrev Fp.toBytes (x : Fp) : ByteArray := Sec1.fieldToBytes sec1 x

/-- Big-endian bytes as a scalar, if their integer is below `n`.

A larger value is rejected rather than reduced, so each scalar has one encoding. -/
def Fn.ofBytes? (bytes : List UInt8) : Option Fn :=
  if h : Base.ByteOrder.ofBE bytes < Fn.modulus then some ⟨_, h⟩ else none

namespace Point

/-- The point as 33 bytes, by SEC 1 v2 §2.3.3 with point compression, or `O` as one byte. -/
abbrev encodeCompressed (q : Point) : ByteArray := Sec1.encode sec1 true q

/-- The point as 65 bytes, by SEC 1 v2 §2.3.3 without point compression, or `O` as one byte. -/
abbrev encodeUncompressed (q : Point) : ByteArray := Sec1.encode sec1 false q

/-- The point with coordinate `x` whose `y` has parity `odd`, by SEC 1 v2 §2.3.4 step 2.4.1. -/
def decompress (x : Fp) (odd : Bool) : Except Secp256k1Error Point :=
  (Sec1.decompress sec1 x odd).mapError .ofSec1

/-- Decode a public key from either encoding: SEC 1 v2 §2.3.4, then the validation of §3.2.2.1.

Validation rejects `O`, and skips the check `n Q = O`, since the cofactor is 1. -/
def decode (bytes : ByteArray) : Except Secp256k1Error Point :=
  (Sec1.decode sec1 bytes >>= Sec1.validatePublicKey Fn.modulus 1).mapError .ofSec1

end Point

end EthLib.Cryptography.Secp256k1
