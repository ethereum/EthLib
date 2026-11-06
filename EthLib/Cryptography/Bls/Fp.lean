module

public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Inverse
public import EthLib.Cryptography.BaseField
public import EthLib.Cryptography.Montgomery
public import EthLib.Base.BigEndian

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

/-- The modulus `p` as twelve limbs of 32 bits, the lowest first.

It is inline, so that the compiler sees each limb as a constant. -/
@[inline] def Fp.pLimbs : Montgomery.Limbs12 :=
  ⟨4294945451, 3120496639, 2975072255, 514588670, 4138792484, 1731252896, 4085584575, 1685539716,
    1129032919, 1260103606, 964683418, 436277738⟩

/-- `-p⁻¹ mod 2 ^ 32`. -/
@[inline] def Fp.pinv : UInt64 := 4294770685

/-- The limbs write the modulus. -/
theorem Fp.val_pLimbs : Montgomery.Limbs.val (n := 12) Fp.pLimbs = modulus := by decide

open Montgomery in
/-- Rows `0` to `5` of the Montgomery product of the limbs `a` and `b`, as limbs.

The product is compiled in two halves: unrolled whole, it exceeds the default compile budget. -/
def Fp.mulLow (a b : Limbs12) : Limbs12 :=
  Montgomery.mulLow (n := 12) 6 (Limbs.get (n := 12) Fp.pLimbs) Fp.pinv (Limbs.get (n := 12) a)
    (Limbs.get (n := 12) b)

open Montgomery in
/-- Rows `6` to `11` of the Montgomery product of `a` and `b`, then the final reduction.

The limbs `lo` hold rows `0` to `5`. -/
def Fp.mulHigh (a b lo : Limbs12) : Limbs12 :=
  Montgomery.mulHigh (n := 12) 6 (Limbs.get (n := 12) Fp.pLimbs) Fp.pinv (Limbs.get (n := 12) a)
    (Limbs.get (n := 12) b) 6 lo Limbs.pack

open Montgomery in
/-- The modulus `p` with the constants of its Montgomery arithmetic, on twelve limbs.

It is inline, so that the compiler sees its fields as constants at each use.

The product runs in two halves, joined by twelve limbs alone.

That holds because `2 p < 2 ^ 384`: the rows keep the state below `2 p`, so no word lies above. -/
@[inline] def Fp.params : Modulus 12 where
  p := modulus
  pLimbs := Fp.pLimbs
  pinv := Fp.pinv
  r1 := ⟨196605, 1980301312, 3289120770, 3958636555, 1405573306, 1598593111, 1884444485,
    2010011731, 2723605613, 1543969431, 4202751123, 368467651⟩
  r2 := ⟨473175878, 4108263220, 164693233, 175564454, 1284880085, 2380613484, 2476573632,
    1743489193, 3038352685, 2591637125, 2462770090, 295210981⟩
  pm2 := ⟨4294945449, 3120496639, 2975072255, 514588670, 4138792484, 1731252896, 4085584575,
    1685539716, 1129032919, 1260103606, 964683418, 436277738⟩
  pLimbs_spec := Fp.val_pLimbs
  pinv_spec := by decide
  r1_spec := by decide +kernel
  r2_spec := by decide +kernel
  pm2_spec := by decide
  mul a b := Fp.mulHigh a b (Fp.mulLow a b)
  mul_spec a b ha := by
    unfold Fp.mulHigh Fp.mulLow
    exact mulHigh_mulLow (n := 12) (k := 6) (m := 6) rfl (Limbs.fits _ 0) (by decide)
      (by decide +kernel) (Limbs.fits a 0) (Fp.val_pLimbs.symm ▸ ha :) (Limbs.fits b 0) _

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
  sqrt a := (Fp.sqrt a).toOption
  sgn0 a := a.val % 2 == 1

/-- Decode a 48-byte big-endian integer as an element of `Fp`.

It rejects an input of the wrong size, and an integer of at least `p`. -/
def fromBytesBE (b : ByteArray) : Except BlsError Fp :=
  if b.size ≠ 48 then .error .nonCanonicalFieldElement
  else
    let n := Base.bytesToNat b.data.toList
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
