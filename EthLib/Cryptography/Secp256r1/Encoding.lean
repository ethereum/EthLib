module

public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Base.BigEndian

/-!
# `Secp256r1.Encoding`

The uncompressed encoding of a point, from SEC 1 v2 §2.3.3, and its decoding from §2.3.4.

The encoding is the prefix `04`, then `x`, then `y`, each as 32 big-endian bytes (§2.3.5).

The decoder accepts only that form, with both coordinates below `p` and the point on the curve.

The cofactor is one, so a decoded point also passes the subgroup check of SEC 1 v2 §3.2.2.1.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- A coordinate as 32 big-endian bytes, by SEC 1 v2 §2.3.5. -/
def Fp.toBytes (x : Fp) : List UInt8 := Base.natToBytes 32 x.val

/-- The uncompressed encoding `04 ‖ x ‖ y` of an affine point, by SEC 1 v2 §2.3.3. -/
def encodeUncompressed (x y : Fp) : List UInt8 := 4 :: (x.toBytes ++ y.toBytes)

/-- Decode an uncompressed point, by SEC 1 v2 §2.3.4.

The result is `none` for another length or prefix, or for a coordinate of `p` or more.

It is also `none` for a point off the curve. -/
def decodeUncompressed (bytes : List UInt8) : Option Point :=
  match bytes with
  | 4 :: coords =>
    if coords.length = 64 then
      let x := Base.bytesToNat (coords.take 32)
      let y := Base.bytesToNat (coords.drop 32)
      if hx : x < Fp.modulus then
        if hy : y < Fp.modulus then
          let point := Point.affine ⟨x, hx⟩ ⟨y, hy⟩
          if point.isOnCurve then some point else none
        else none
      else none
    else none
  | _ => none

end EthLib.Cryptography.Secp256r1
