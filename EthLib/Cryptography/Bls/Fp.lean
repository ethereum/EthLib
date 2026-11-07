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

An element is held in Montgomery form, as twelve limbs of 32 bits.

The limbs hold `a R mod p` for the element `a`, with `R = 2 ^ 384`.

So a product needs no division by `p`, and an element reads and writes its bytes directly.

The inverse comes from the extended Euclidean algorithm, on the integer of the element.

Since `p = 3 mod 4`, a square root of a square `x` is `x^((p + 1) / 4)`.
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
abbrev Fp := Montgomery Fp.params

namespace Fp

/-- The element that stands for `n mod p`. -/
@[inline] def ofNat (n : Nat) : Fp := Montgomery.ofNat n

/-- The integer below `p` that the element stands for.

Proofs use its lemmas, never its unfolding, which runs a Montgomery reduction. -/
@[inline, irreducible] def val (a : Fp) : Nat := Montgomery.toNat a

@[inline] def zero : Fp := Montgomery.zero
@[inline] def one  : Fp := Montgomery.one

@[inline] def add (a b : Fp) : Fp := a + b
@[inline] def sub (a b : Fp) : Fp := a - b
@[inline] def neg (a : Fp)   : Fp := -a
@[inline] def mul (a b : Fp) : Fp := a * b

@[inline] def beq (a b : Fp) : Bool := a == b
@[inline] def isZero (a : Fp) : Bool := a == zero

/-- Square-and-multiply modular exponentiation. -/
@[inline] def powNat (base : Fp) (e : Nat) : Fp := Montgomery.pow base e

/-- Multiplicative inverse by the extended Euclidean algorithm, on the integer of the element.

The inverse of `0` is `0`. -/
@[inline] def inverse (a : Fp) : Fp := ofNat (euclid a.val modulus 1 0 % modulus).toNat

/-- Field division `a * b⁻¹`. -/
instance : Div Fp := ⟨fun a b => a * b.inverse⟩

open Montgomery in
/-- The exponent `(p + 1) / 4` of the square root, as twelve 32-bit limbs, the lowest first. -/
@[inline] def sqrtExponent : Limbs.T 12 :=
  ⟨4294961835, 4001349631, 2891251711, 128647167, 1034698121, 3654038696, 1021396143,
    3642610401, 2429741877, 2462509549, 2388654502, 109069434⟩

open Montgomery in
/-- The limbs of the exponent write `(p + 1) / 4`. -/
theorem val_sqrtExponent : Limbs.val sqrtExponent = (modulus + 1) / 4 := by decide

/-- Square root, valid since `p = 3 mod 4`.

The root it returns is `a ^ ((p + 1) / 4)`.

The power runs four bits of the exponent at a time.

It fails when `a` is not a square. -/
def sqrt (a : Fp) : Except BlsError Fp :=
  let cand : Fp := Montgomery.powLimbs a sqrtExponent
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
    match Montgomery.ofBytesBE b 0 with
    | some a => .ok a
    | none => .error .nonCanonicalFieldElement

/-- Encode as 48 big-endian bytes. -/
@[inline] def toBytesBE (a : Fp) : ByteArray := Montgomery.toBytesBE a

end Fp

/-- A square root in a base field, or the error of `Fp.sqrt` when the element is not a square. -/
def sqrtOrError {F : Type} [BaseField F] (a : F) : Except BlsError F :=
  match BaseField.sqrt a with
  | some s => .ok s
  | none => .error .notASquare

end EthLib.Cryptography.Bls
