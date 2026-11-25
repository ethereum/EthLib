module

public import EthLib.Base.ByteOrder
public import EthLib.Base.Pow
public import EthLib.Cryptography.ShortWeierstrass

/-!
# SEC 1 point encoding

The octet strings of the points of a short Weierstrass curve over a prime field `F_p`.

They follow [SEC 1 v2][sec1] §2.3.3 to §2.3.8; public key validation follows §3.2.2.1.

[sec1]: https://www.secg.org/sec1-v2.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Sec1

open ShortWeierstrass (Point)
open ShortWeierstrass.Point (rhs)

/-- What the encoding reads from the prime field `F_p`, besides the curve. -/
structure Params (p : Nat) where
  /-- The length `mlen = ceil((log2 p) / 8)` of a field element in octets, from §2.3.5. -/
  mlen : Nat
  /-- Every element of the field fits in `mlen` octets. -/
  fits : p ≤ 256 ^ mlen
  /-- No shorter length fits, so `mlen` is the length of §2.3.5. -/
  minimal : 256 ^ (mlen - 1) < p
  /-- `p` is odd, so `y` and `p - y` have opposite parities, as compression needs. -/
  odd : p % 2 = 1
  /-- A square root, or `none` when the element is not a square.

  Its law is a hypothesis of the proofs. -/
  sqrt? : Fin p → Option (Fin p)

variable {p : Nat}

/-- A square root for `p = 3 mod 4`: `β = α^((p + 1) / 4)`, returned only when `β^2 = α`.

When `α` is a square, `β` is a root of it, by Euler's criterion (HAC Fact 2.146 (i)). -/
def sqrt3Mod4 [NeZero p] (α : Fin p) : Option (Fin p) :=
  -- RFC 9380, Appendix I.1: the root is `α^c1` with `c1 = (p + 1) / 4`.
  --
  -- The exponent is below `2^(log2 p + 1)`, so that many bits hold it.
  let β := Base.powBits (p.log2 + 1) α ((p + 1) / 4)
  -- A non-square has no root, so its candidate fails this check.
  if β * β = α then some β else none

/-- A field element as `mlen` octets, by §2.3.5. -/
def fieldToBytes (params : Params p) (a : Fin p) : ByteArray :=
  -- Step 1: `a` is an integer in `[0, p - 1]`, written by §2.3.7 as `mlen` big-endian octets.
  ⟨(Base.ByteOrder.toBE params.mlen a.val).toArray⟩

/-- `mlen` octets as a field element, by §2.3.6, or `none` where SEC 1 outputs "invalid". -/
def fieldOfBytes? (params : Params p) (M : ByteArray) : Option (Fin p) :=
  -- The input has `mlen` octets.
  if M.size = params.mlen then
    -- Step 1: `a` is the integer of `M` by §2.3.8, and "invalid" unless `a` is in `[0, p - 1]`.
    if h : Base.ByteOrder.ofBE M.data.toList < p then some ⟨_, h⟩ else none
  else none

/-- Each cause of "invalid" in point decoding (§2.3.4) and public key validation (§3.2.2.1). -/
inductive Sec1Error where
  /-- The octet string has `size` octets: not `00`, and neither `mlen + 1` nor `2 mlen + 1` long. -/
  | invalidLength (size : Nat)
  /-- The first octet, `byte`, is not a form of that length: steps 2.3 and 3.2 of decoding. -/
  | invalidPrefix (byte : UInt8)
  /-- The integer of a coordinate, `value`, is `p` or more, by §2.3.6.

  Decoding reads `x` first, so `value` is `x` when both coordinates are too large. -/
  | coordinateTooLarge (value : Nat)
  /-- `α = x^3 + a x + b` has no square root, so no point has this `x`: step 2.4.1. -/
  | noSquareRoot
  /-- The only root of `α` is `0`, which is even, and the prefix asks for an odd `y`: step 2.4.1. -/
  | noRootOfParity
  /-- The pair does not satisfy the curve equation: step 3.5, or step 2 of validation. -/
  | notOnCurve
  /-- The public key is the point at infinity: step 1 of validation. -/
  | pointAtInfinity
  /-- `n Q` is not the point at infinity: step 4 of validation. -/
  | notInSubgroup
deriving DecidableEq, Repr

section Curve

variable [NeZero p] [ShortWeierstrass.Params (Fin p)]

/-- The octet string of a point, by §2.3.3, with point compression when `compressed` holds. -/
def encode (params : Params p) (compressed : Bool) : Point (Fin p) → ByteArray
  -- Step 1: `O` is the single octet `00`.
  | .infinity => ⟨#[0x00]⟩
  | .affine x y =>
    if compressed then
      -- Steps 2.1 to 2.4: `X` from `x_P`, `Y = 02` if `y_P mod 2 = 0`, else `03`, and `M = Y || X`.
      ⟨#[if y.val % 2 = 0 then 0x02 else 0x03]⟩ ++ fieldToBytes params x
    else
      -- Steps 3.1 to 3.3: `X` from `x_P`, `Y` from `y_P`, and `M = 04 || X || Y`.
      ⟨#[0x04]⟩ ++ fieldToBytes params x ++ fieldToBytes params y

/-- The point with coordinate `x` whose `y` has the parity `ybit`, by step 2.4.1 of §2.3.4. -/
def decompress (params : Params p) (x : Fin p) (ybit : Bool) : Except Sec1Error (Point (Fin p)) :=
  -- `α = x_P^3 + a x_P + b`, and "invalid" if `α` has no square root `β`.
  match params.sqrt? (rhs x) with
  | none => .error .noSquareRoot
  | some β =>
    -- `y_P = β` if `β = ~y_P (mod 2)`.
    if decide (β.val % 2 = 1) = ybit then .ok (.affine x β)
    -- Else `y_P = p - β`, which is not in `[0, p - 1]` when `β = 0`: no point has that parity.
    --
    -- SEC 1 leaves this case open; reading `p - 0` as `0` would give `(x, 0)` two encodings.
    --
    -- EthLib reads it as "invalid", so each point has one compressed form.
    else if β = 0 then .error .noRootOfParity
    -- For `β > 0`, `p - β` is `-β`, of the other parity since `p` is odd.
    else .ok (.affine x (-β))

/-- `mlen` octets `X` as a field element, or the error that names their integer.

Decoding calls it only on `mlen` octets, so a failure means the integer is `p` or more. -/
def readField (params : Params p) (X : ByteArray) : Except Sec1Error (Fin p) :=
  match fieldOfBytes? params X with
  | some a => .ok a
  | none => .error (.coordinateTooLarge (Base.ByteOrder.ofBE X.data.toList))

/-- The point of an octet string, by §2.3.4, or the cause of "invalid".

The single octet `00` decodes to the point at infinity. -/
def decode (params : Params p) (M : ByteArray) : Except Sec1Error (Point (Fin p)) :=
  -- The input is `00`, or `mlen + 1` or `2 mlen + 1` octets; any other length is "invalid".
  if h1 : M.size = 1 then
    -- Step 1: `M = 00` gives `P = O`.
    --
    -- Any other single octet has none of the three lengths.
    if M[0] = 0x00 then .ok .infinity else .error (.invalidLength 1)
  else if h2 : M.size = params.mlen + 1 then do
    -- Step 2.1: `M = Y || X`, one octet `Y` then `mlen` octets `X`.
    --
    -- Step 2.2: `x_P` from `X` by §2.3.6.
    let x ← readField params (M.extract 1 M.size)
    -- Step 2.3: `Y = 02` gives `~y_P = 0`, `Y = 03` gives `~y_P = 1`, and any other `Y` "invalid".
    let Y := M[0]'(by omega)
    if Y = 0x02 then decompress params x false
    else if Y = 0x03 then decompress params x true
    else .error (.invalidPrefix Y)
  else if h3 : M.size = 2 * params.mlen + 1 then do
    -- Step 3.1: `M = W || X || Y`, one octet `W` then `mlen` octets each for `X` and `Y`.
    let W := M[0]'(by omega)
    -- Step 3.2: "invalid" unless `W = 04`.
    --
    -- The hybrid forms `06` and `07` of ANSI X9.62 are not forms of SEC 1, so they fail here.
    if W ≠ 0x04 then .error (.invalidPrefix W)
    else
      -- Steps 3.3 and 3.4: `x_P` from `X` and `y_P` from `Y`, by §2.3.6.
      let x ← readField params (M.extract 1 (params.mlen + 1))
      let y ← readField params (M.extract (params.mlen + 1) M.size)
      -- Steps 3.5 and 3.6: `(x_P, y_P)` must satisfy the curve equation.
      if (Point.affine x y).isOnCurve then .ok (.affine x y) else .error .notOnCurve
  else .error (.invalidLength M.size)

/-- Public key validation, by §3.2.2.1, with the order `n` of the base point and the cofactor `h`.

The domain parameters must be valid: `n h` is the number of points of the curve.

It returns the key when it is valid. -/
def validatePublicKey (n h : Nat) (Q : Point (Fin p)) : Except Sec1Error (Point (Fin p)) :=
  -- Step 1: `Q ≠ O`.
  if Q = .infinity then .error .pointAtInfinity
  -- Step 2: `x_Q` and `y_Q` are in `[0, p - 1]` by their type, and `Q` satisfies the equation.
  else if !Q.isOnCurve then .error .notOnCurve
  -- Step 4: `n Q = O`.
  --
  -- When `h = 1`, every point of the curve satisfies it, as SEC 1 notes, so the check is skipped.
  else if h ≠ 1 ∧ Q.mulBits id ShortWeierstrass.Params.inv id ShortWeierstrass.Params.a
      (n.log2 + 1) n ≠ .infinity then .error .notInSubgroup
  else .ok Q

end Curve

end EthLib.Cryptography.Sec1
