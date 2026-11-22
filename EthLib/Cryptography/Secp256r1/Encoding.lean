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
def Fp.toBytes (x : Fp) : List UInt8 :=
  -- Step 1: `q = p` is an odd prime, so `M` is the integer `a` as `mlen = 32` octets, by §2.3.7.
  Base.natToBytes 32 x.val

/-- The uncompressed encoding `04 ‖ x ‖ y` of an affine point, by SEC 1 v2 §2.3.3. -/
def encodeUncompressed (x y : Fp) : List UInt8 :=
  -- Steps 3.1 to 3.3: `X` from `x_P`, `Y` from `y_P`, and `M = 04 || X || Y`.
  4 :: (x.toBytes ++ y.toBytes)

/-- Decode an uncompressed point, by SEC 1 v2 §2.3.4.

The result is `none` for another length or prefix, or for a coordinate of `p` or more.

It is also `none` for a point off the curve. -/
def decodeUncompressed (bytes : List UInt8) : Option Point :=
  -- Steps 1 and 2, for `00` and the compressed form, are not implemented: they give `none`.
  --
  -- Steps 3.1 and 3.2: `M = W || X || Y`, and "invalid" unless `W = 04`.
  match bytes with
  | 4 :: coords =>
    -- Step 3 applies only when `M` has `2 * 32 + 1` octets.
    if coords.length = 64 then
      let x := Base.bytesToNat (coords.take 32)
      let y := Base.bytesToNat (coords.drop 32)
      -- Steps 3.3 and 3.4: `x_P` and `y_P` by §2.3.6, "invalid" unless in `[0, p-1]`.
      if hx : x < Fp.modulus then
        if hy : y < Fp.modulus then
          let point := Point.affine ⟨x, hx⟩ ⟨y, hy⟩
          -- Steps 3.5 and 3.6: `(x_P, y_P)` must satisfy the curve equation.
          if point.isOnCurve then some point else none
        else none
      else none
    else none
  | _ => none

end EthLib.Cryptography.Secp256r1
