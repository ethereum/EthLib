module

public import EthLib.Cryptography.Secp256k1.Curve
public import EthLib.Cryptography.Secp256k1.Errors
public import EthLib.Cryptography.Secp256k1.Sqrt
public import EthLib.Base.ByteOrder

/-!
# `Secp256k1.Encoding`

The two encodings of a point as bytes, from SEC 1 v2 §2.3.3, and their decoding, from §2.3.4.

The compressed form has 33 bytes, and the uncompressed form 65.

A public key is never the point at infinity, by SEC 1 v2 §3.2.2.1, so the decoder rejects it.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- A coordinate as 32 bytes, by SEC 1 v2 §2.3.5. -/
def Fp.toBytes (x : Fp) : List UInt8 :=
  -- Step 1: `q = p` is an odd prime, so `M` is the integer `a` as `mlen = 32` octets, by §2.3.7.
  (Base.ByteOrder.toBE 32 x.val).toList

/-- A coordinate is 32 bytes long. -/
theorem Fp.length_toBytes (x : Fp) : x.toBytes.length = 32 := by
  simp [Fp.toBytes]

/-- 32 bytes as a coordinate, by SEC 1 v2 §2.3.6: the integer must be below `p`. -/
def Fp.ofBytes (bytes : List UInt8) : Except Secp256k1Error Fp :=
  -- Step 1: `a` is the integer of `M`, by §2.3.8, and "invalid" unless `a` lies in `[0, p-1]`.
  if h : Base.ByteOrder.ofBE bytes < Fp.modulus then .ok ⟨_, h⟩
  else .error (.coordinateTooLarge (Base.ByteOrder.ofBE bytes))

/-- Big-endian bytes as a scalar, if their integer is below `n`.

A larger value is rejected rather than reduced, so each scalar has one encoding. -/
def Fn.ofBytes? (bytes : List UInt8) : Option Fn :=
  if h : Base.ByteOrder.ofBE bytes < Fn.modulus then some ⟨_, h⟩ else none

namespace Point

/-- The point as 33 bytes, by SEC 1 v2 §2.3.3 with point compression, or `O` as one byte. -/
def encodeCompressed : Point → ByteArray
  -- Step 1: if `P = O`, output `M = 00`.
  | infinity => ⟨#[0x00]⟩
  -- Steps 2.1 to 2.4: `X` from `x_P`, `~y_P = y_P mod 2`, `Y = 02` or `03`, and `M = Y || X`.
  | affine x y => ⟨((if y.val % 2 = 0 then 0x02 else 0x03) :: x.toBytes).toArray⟩

/-- The point as 65 bytes, by SEC 1 v2 §2.3.3 without point compression, or `O` as one byte. -/
def encodeUncompressed : Point → ByteArray
  -- Step 1: if `P = O`, output `M = 00`.
  | infinity => ⟨#[0x00]⟩
  -- Steps 3.1 to 3.3: `X` from `x_P`, `Y` from `y_P`, and `M = 04 || X || Y`.
  | affine x y => ⟨(0x04 :: x.toBytes ++ y.toBytes).toArray⟩

/-- The point with coordinate `x` whose `y` has parity `odd`, by SEC 1 v2 §2.3.4 step 2.4.1. -/
def decompress (x : Fp) (odd : Bool) : Except Secp256k1Error Point :=
  -- Step 2.4.1: `alpha = x_P^3 + a x_P + b mod p`, with `a = 0`, and `beta` a square root of it.
  --
  -- "invalid" if `alpha` has no square root.
  --
  -- The root stays an argument here, so a proof can split on it before anything evaluates it.
  (x * x * x + b).sqrt.elim (.error .noPointWithX) fun beta =>
    -- `y_P = beta` if `beta = ~y_P mod 2`, else `y_P = p - beta`.
    --
    -- `p - beta` has the other parity, since `p` is odd.
    .ok (affine x (if decide (beta.val % 2 = 1) = odd then beta else -beta))

/-- Decode a public key from either encoding, by SEC 1 v2 §2.3.4.

The point at infinity is rejected, as public key validation requires in SEC 1 v2 §3.2.2.1.

That validation also checks `n Q = O`, which holds for every point, since the cofactor is 1. -/
def decode (bytes : ByteArray) : Except Secp256k1Error Point :=
  -- The input `M` is `00`, or 33 or 65 octets long; any other length is rejected.
  match bytes.data.toList with
  | [] => .error (.invalidEncodingLength 0)
  | tag :: rest =>
    -- Step 1 outputs `O` for `M = 00`, which is not a public key.
    if tag = 0x00 ∧ rest = [] then .error .pointAtInfinity
    else if rest.length = 32 then
      -- Step 2.1: `M = Y || X`.
      --
      -- Step 2.3, checked before step 2.2: `Y = 02` gives `~y_P = 0`, `03` gives 1, else "invalid".
      if tag = 0x02 ∨ tag = 0x03 then do
        -- Step 2.2: `x_P` from `X`, by §2.3.6.
        let x ← Fp.ofBytes rest
        -- Steps 2.4 and 2.5: the point `(x_P, y_P)` with the parity `~y_P`.
        decompress x (tag == 0x03)
      else .error (.invalidPrefix tag)
    else if rest.length = 64 then
      -- Steps 3.1 and 3.2: `M = W || X || Y`, and "invalid" unless `W = 04`.
      if tag = 0x04 then do
        -- Steps 3.3 and 3.4: `x_P` from `X` and `y_P` from `Y`, by §2.3.6.
        let x ← Fp.ofBytes (rest.take 32)
        let y ← Fp.ofBytes (rest.drop 32)
        -- Steps 3.5 and 3.6: `(x_P, y_P)` must satisfy the curve equation.
        if (affine x y).isOnCurve then .ok (affine x y) else .error .notOnCurve
      else .error (.invalidPrefix tag)
    else .error (.invalidEncodingLength bytes.size)

end Point

end EthLib.Cryptography.Secp256k1
