import EthLib.Cryptography.Secp256k1.Curve
import EthLib.Cryptography.Secp256k1.Errors

/-!
# `Secp256k1.Encoding`

The two encodings of a point as bytes, from SEC 1 v2 §2.3.3, and their decoding, from SEC 1 v2 §2.3.4.

```text
    compressed     [ 02 or 03: 1 | x: 32 ]              33 bytes
    uncompressed   [ 04: 1 | x: 32 | y: 32 ]            65 bytes
```

A coordinate is written as 32 big-endian bytes, by SEC 1 v2 §2.3.5 and §2.3.7.

The compressed form keeps only the parity of `y`, in the prefix: `02` for even, `03` for odd.

The equation leaves two roots `y` and `p - y`, one of each parity, so the parity picks one.

SEC 1 encodes the point at infinity as the single byte `00`.

A public key is never that point, by SEC 1 v2 §3.2.2.1, so the decoder rejects it.
-/

namespace EthLib.Cryptography.Secp256k1

/-- The `k` big-endian bytes of `v mod 256^k`, by SEC 1 v2 §2.3.7. -/
def toBytesBE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, v => toBytesBE k (v / 256) ++ [UInt8.ofNat (v % 256)]

/-- The integer that big-endian bytes write, by SEC 1 v2 §2.3.8. -/
def ofBytesBE (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- A coordinate as 32 bytes, by SEC 1 v2 §2.3.5. -/
def Fp.toBytes (x : Fp) : List UInt8 := toBytesBE 32 x.val

/-- 32 bytes as a coordinate, by SEC 1 v2 §2.3.6: the integer must be below `p`. -/
def Fp.ofBytes (bytes : List UInt8) : Except Secp256k1Error Fp :=
  if h : ofBytesBE bytes < Fp.modulus then .ok ⟨_, h⟩ else .error .coordinateTooLarge

namespace Point

/-- The point as 33 bytes, by SEC 1 v2 §2.3.3 with point compression.

`O` is the single byte `00`. -/
def encodeCompressed : Point → ByteArray
  | infinity => ⟨#[0x00]⟩
  | affine x y => ⟨((if y.val % 2 = 0 then 0x02 else 0x03) :: x.toBytes).toArray⟩

/-- The point as 65 bytes, by SEC 1 v2 §2.3.3 without point compression.

`O` is the single byte `00`. -/
def encodeUncompressed : Point → ByteArray
  | infinity => ⟨#[0x00]⟩
  | affine x y => ⟨(0x04 :: x.toBytes ++ y.toBytes).toArray⟩

/-- The point with coordinate `x` whose `y` has parity `odd`, by SEC 1 v2 §2.3.4 step 2.4.1.

`beta` is a square root of `x^3 + 7`, and `p - beta` is the other one, of the other parity. -/
def decompress (x : Fp) (odd : Bool) : Except Secp256k1Error Point :=
  match (x * x * x + b).sqrt with
  | none => .error .noPointWithX
  | some beta => .ok (affine x (if decide (beta.val % 2 = 1) = odd then beta else -beta))

/-- Decode a public key from either encoding, by SEC 1 v2 §2.3.4.

The point at infinity is rejected, as public key validation requires in SEC 1 v2 §3.2.2.1.

That validation also checks `n Q = O`, which holds for every point, since the cofactor is 1. -/
def decode (bytes : ByteArray) : Except Secp256k1Error Point :=
  match bytes.data.toList with
  | [] => .error (.invalidEncodingLength 0)
  | tag :: rest =>
    if tag = 0x00 ∧ rest = [] then .error .pointAtInfinity
    else if rest.length = 32 then
      -- Compressed: the prefix carries the parity of `y`.
      if tag = 0x02 ∨ tag = 0x03 then do
        let x ← Fp.ofBytes rest
        decompress x (tag == 0x03)
      else .error (.invalidPrefix tag)
    else if rest.length = 64 then
      -- Uncompressed: both coordinates, which must satisfy the equation.
      if tag = 0x04 then do
        let x ← Fp.ofBytes (rest.take 32)
        let y ← Fp.ofBytes (rest.drop 32)
        if (affine x y).isOnCurve then .ok (affine x y) else .error .notOnCurve
      else .error (.invalidPrefix tag)
    else .error (.invalidEncodingLength bytes.size)

end Point

end EthLib.Cryptography.Secp256k1
