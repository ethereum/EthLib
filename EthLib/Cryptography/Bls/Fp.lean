module

public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Inverse
public import EthLib.Cryptography.BaseField

/-!
# `Fp`

The base field of BLS12-381, the integers mod the prime `p`.

In hexadecimal, `p` is the 96 digits of these two lines, joined:

- `1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624`
- `1eabfffeb153ffffb9feffffffffaaab`

`Fp` is `Fin p`, so every element is below `p` by construction.

Core gives `Fin` its `+`, `-`, `*` and negation, all reduced mod `p`.

The inverse comes from the extended Euclidean algorithm.

Since `p = 3 mod 4`, a square root of a square `x` is `x^((p + 1) / 4)`.

The code aims at clarity, so it has no Montgomery form and no other optimization.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- BLS12-381 base field modulus. -/
def Fp.modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

protected theorem Fp.modulus_pos : 0 < Fp.modulus := by decide

-- Named explicitly, since the anonymous instances of `Fp` and `Fr` would get the same name.
instance Fp.instNeZeroModulus : NeZero Fp.modulus := ⟨by decide⟩

/-- An element of the BLS12-381 base field. -/
abbrev Fp := Fin Fp.modulus

namespace Fp

@[inline] def ofNat (n : Nat) : Fp := Fin.ofNat modulus n

@[inline] def zero : Fp := ⟨0, Fp.modulus_pos⟩
@[inline] def one  : Fp := ⟨1, by decide⟩

@[inline] def add (a b : Fp) : Fp := a + b
@[inline] def sub (a b : Fp) : Fp := a - b
@[inline] def neg (a : Fp)   : Fp := -a
@[inline] def mul (a b : Fp) : Fp := a * b

@[inline] def beq (a b : Fp) : Bool := a.val == b.val
@[inline] def isZero (a : Fp) : Bool := a.val == 0

/-- Square-and-multiply modular exponentiation. -/
def powNat (base : Fp) (e : Nat) : Fp :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
termination_by e
decreasing_by omega

/-- Multiplicative inverse by the extended Euclidean algorithm.

The inverse of `0` is `0`. -/
@[inline] def inverse (a : Fp) : Fp := Fin.inverse a

/-- Field division `a * b⁻¹`.

Core already has a division on `Fin n`, which divides the integers.

That division is wrong for a field element, so this instance has high priority. -/
instance (priority := high) : Div Fp := ⟨fun a b => a * b.inverse⟩

/-- Square root, valid since `p = 3 mod 4`.

The root it returns is `a ^ ((p + 1) / 4)`.

It fails when `a` is not a square. -/
def sqrt (a : Fp) : Except BlsError Fp :=
  let cand := powNat a ((modulus + 1) / 4)
  if (cand * cand).beq a then .ok cand else .error .notASquare

/-- The operations that the extensions and curves of BLS12-381 read from `Fp`. -/
instance : BaseField Fp where
  zero := zero
  one := one
  ofNat := ofNat
  beq := beq
  isZero := isZero
  inverse := inverse
  powNat := powNat
  sqrt a := match Fp.sqrt a with
    | .ok s => some s
    | .error _ => none
  sgn0 a := a.val % 2 == 1

/-- Decode big-endian bytes as a `Nat`. -/
def bytesBEToNat (b : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:b.size] do
    acc := (acc <<< 8) ||| b[i]!.toNat
  return acc

/-- Decode a 48-byte big-endian integer as an element of `Fp`.

It rejects an input of the wrong size, and an integer of at least `p`. -/
def fromBytesBE (b : ByteArray) : Except BlsError Fp :=
  if b.size ≠ 48 then .error .nonCanonicalFieldElement
  else
    let n := bytesBEToNat b
    if h : n < modulus then .ok ⟨n, h⟩ else .error .nonCanonicalFieldElement

/-- Encode as 48 big-endian bytes. -/
def toBytesBE (a : Fp) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := 48) fun i =>
    UInt8.ofNat ((a.val >>> ((47 - i.val) * 8)) &&& 0xff)

end Fp

/-- A square root in a base field, or the error of `Fp.sqrt` when the element is not a square. -/
def sqrtOrError {F : Type} [BaseField F] (a : F) : Except BlsError F :=
  match BaseField.sqrt a with
  | some s => .ok s
  | none => .error .notASquare

end EthLib.Cryptography.Bls
