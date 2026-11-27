module

public import EthLib.Cryptography.Bls.Errors
public import EthLib.Cryptography.Inverse
public import EthLib.Cryptography.BaseField
public import EthLib.Cryptography.Montgomery
public import EthLib.Cryptography.Word64.Six
public import EthLib.Base.ByteOrder

/-!
# `Fp`

The base field of BLS12-381, the integers mod the prime `p`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- BLS12-381 base field modulus.

In hexadecimal, `p` is the 96 digits of these two lines, joined:

- `1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624`
- `1eabfffeb153ffffb9feffffffffaaab`
-/
def Fp.modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

protected theorem Fp.modulus_pos : 0 < Fp.modulus := by decide

-- Named explicitly, since the anonymous instances of `Fp` and `Fr` would get the same name.
instance Fp.instNeZeroModulus : NeZero Fp.modulus := ⟨by decide⟩

/-- The modulus `p` as twelve limbs of 32 bits, two to a word, the lowest first.

It is not inline, so a product reads its words from memory.

The C compiler then keeps each product by a word of `p` as one wide multiplication. -/
@[noinline] def Fp.pLimbs : Montgomery.Limbs.T 12 :=
  ⟨0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf,
    0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a⟩

/-- `-p⁻¹ mod 2 ^ 32`. -/
@[inline] def Fp.pinv : UInt64 := 4294770685

/-- The limbs write the modulus. -/
theorem Fp.val_pLimbs : Montgomery.Limbs.val (n := 12) Fp.pLimbs = modulus := by decide

/-- `-p⁻¹ mod 2 ^ 64`. -/
@[inline] def Fp.pinvWord : UInt64 := 0x89f3fffcfffcfffd

open Montgomery in
/-- The Montgomery product of the limbs `a` and `b`, computed on six words of 64 bits.

The limbs are stored as those words, and both widths have `R = 2 ^ 384`.

So the product is the one of the twelve limbs. -/
def Fp.mulWords (a b : Limbs.T 12) : Limbs.T 12 :=
  Word64.mul6 Fp.pLimbs Fp.pinvWord a b

/-- Two integers below `p` with the same product by `2^384` mod `p` are equal. -/
private theorem Fp.eq_of_mul_mod {x y : Nat} (hx : x < modulus) (hy : y < modulus)
    (h : 2^384 * x % modulus = 2^384 * y % modulus) : x = y := by
  -- An inverse `r` of `2^384` mod `p`, written in two halves of 192 bits.
  obtain ⟨r, hR⟩ : ∃ r, r * 2^384 % modulus = 1 :=
    ⟨0x14fec701e8fb0ce9ed5e64273c4f538b1797ab1458a88de9 * 2^192 +
      0x343ea97914956dc87fe11274d898fafbf4d38259380b4820, by decide +kernel⟩
  -- `2^384` as an atom, so that no step tries to evaluate it.
  generalize (2:Nat)^384 = R at hR h ⊢
  -- `z = r (2^384 z mod p) mod p` for `z` below `p`.
  have key (z : Nat) (hz : z < modulus) : z = r * (R * z % modulus) % modulus := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_mod, hR, Nat.one_mul,
      Nat.mod_mod, Nat.mod_eq_of_lt hz]
  rw [key x hx, key y hy, h]

open Montgomery in
/-- The product on six words is the product on twelve limbs, for `a` below `p`. -/
theorem Fp.mulWords_eq (a b : Limbs.T 12) (ha : Limbs.val (n := 12) a < modulus) :
    Fp.mulWords a b =
      Montgomery.mulWords (n := 12) (Limbs.get (n := 12) Fp.pLimbs) Fp.pinv
        (Limbs.get (n := 12) a)
        (Limbs.get (n := 12) b) Limbs.pack := by
  -- The product on six words, from its spec: below `p`, and `a b 2^(-384)` mod `p`.
  have hpw : Word64.Words6.val Fp.pLimbs = modulus := by decide +kernel
  have hp : 2 * Word64.Words6.val Fp.pLimbs < 2^384 := by decide +kernel
  have hpinv : (Word64.Words6.val Fp.pLimbs * Fp.pinvWord.toNat + 1) % 2^64 = 0 := by
    decide +kernel
  have ha' : Word64.Words6.val a < Word64.Words6.val Fp.pLimbs := by
    rw [hpw, ← Limbs.val_words6]; exact ha
  obtain ⟨hl6, he6⟩ := Word64.mul6_spec hp hpinv ha' b
  rw [hpw, ← Limbs.val_words6 a, ← Limbs.val_words6 b] at he6
  rw [hpw] at hl6
  -- The product on twelve limbs, from its spec.
  have hn : num 12 (Limbs.get (n := 12) Fp.pLimbs) 0 = modulus := Fp.val_pLimbs
  obtain ⟨hf, hl, he⟩ := Internal.mulWords_spec (n := 12) (pinv := Fp.pinv)
    (Limbs.fits (n := 12) Fp.pLimbs 0)
    (by rw [hn]; decide) (Limbs.fits (n := 12) a 0) (by rw [hn]; exact ha)
    (Limbs.fits (n := 12) b 0)
  rw [hn] at hl he
  rw [Internal.mulWords_out]
  apply Limbs.val_injective (n := 12)
  rw [Limbs.val_pack hf, Fp.mulWords, Limbs.val_words6]
  -- Both are below `p` and agree after a product by `2^384`, so they are equal.
  rw [show 32 * 12 = 384 from rfl] at he
  exact Fp.eq_of_mul_mod hl6 hl (he6.trans he.symm)

open Montgomery in
/-- The modulus `p` with the constants of its Montgomery arithmetic, on twelve limbs.

It is inline, so that the compiler sees its fields as constants at each use.

The product runs on six words of 64 bits. -/
@[inline] def Fp.params : Modulus 12 where
  p := modulus
  pLimbs := Fp.pLimbs
  pinv := Fp.pinv
  r1 := ⟨0x760900000002fffd, 0xebf4000bc40c0002, 0x5f48985753c758ba, 0x77ce585370525745,
    0x5c071a97a256ec6d, 0x15f65ec3fa80e493⟩
  r2 := ⟨0xf4df1f341c341746, 0x0a76e6a609d104f1, 0x8de5476c4c95b6d5, 0x67eb88a9939d83c0,
    0x9a793e85b519952d, 0x11988fe592cae3aa⟩
  pm2 := ⟨0xb9feffffffffaaa9, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf,
    0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a⟩
  pLimbs_spec := Fp.val_pLimbs
  pinv_spec := by decide
  r1_spec := by decide +kernel
  r2_spec := by decide +kernel
  pm2_spec := by decide
  mul := Fp.mulWords
  mul_spec a b ha := Fp.mulWords_eq a b ha

/-- An element of the BLS12-381 base field.

An element is held in Montgomery form, as twelve limbs of 32 bits, two to a word.

The limbs hold `a R mod p` for the element `a`, with `R = 2 ^ 384`.

So a product needs no division by `p`, and an element reads and writes its bytes directly. -/
abbrev Fp := Montgomery Fp.params

namespace Fp

/-- The element that stands for `n mod p`. -/
@[inline] def ofNat (n : Nat) : Fp := Montgomery.ofNat n

/-- The integer below `p` that the element stands for.

Proofs use its lemmas, never its unfolding, which runs a Montgomery reduction. -/
@[inline, irreducible] def val (a : Fp) : Nat := Montgomery.toNat a

@[inline] def zero : Fp := Montgomery.zero
@[inline] def one  : Fp := Montgomery.one

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
/-- The exponent `(p + 1) / 4` of the square root, as twelve 32-bit limbs, two to a word. -/
@[inline] def sqrtExponent : Limbs.T 12 :=
  ⟨0xee7fbfffffffeaab, 0x07aaffffac54ffff, 0xd9cc34a83dac3d89, 0xd91dd2e13ce144af,
    0x92c6e9ed90d2eb35, 0x0680447a8e5ff9a6⟩

open Montgomery in
/-- The limbs of the exponent write `(p + 1) / 4`. -/
theorem val_sqrtExponent : Limbs.val sqrtExponent = (modulus + 1) / 4 := by decide

/-- The power `a^((p + 1) / 4)` of RFC 9380, Appendix I.1, before checking its square. -/
@[inline] def sqrtCandidate (a : Fp) : Fp := Montgomery.powLimbs a sqrtExponent

/-- Square root, valid since `p = 3 mod 4`.

The root it returns is `a ^ ((p + 1) / 4)`.

The power runs four bits of the exponent at a time.

It fails when `a` is not a square. -/
def sqrt (a : Fp) : Except BlsError Fp :=
  -- RFC 9380, Appendix I.1, step 1: the root is `x^c1`, with `c1 = (q + 1) / 4`.
  let cand := sqrtCandidate a
  -- The RFC guarantees the square only for a square `x`, so a power whose square is not `x` fails.
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
  sqrtCandidate := Fp.sqrtCandidate
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

end EthLib.Cryptography.Bls
