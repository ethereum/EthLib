module

public import EthLib.Cryptography.Secp256k1.Field

/-!
# `Secp256k1.Montgomery`

The base field of secp256k1 in Montgomery form, on four 64-bit words, with `R = 2^256`.

An element holds `a R mod p`, below `p`, so equality of words is equality in the field.

Multiplication and squaring sum word products by output column.

Squaring doubles each off-diagonal product once.

Montgomery reduction, from [Montgomery (1985)][redc], cancels the low half of a wide product.

The complement is `2^256 - p = 2^32 + 977`.

A full product is reduced two words at a time, with the inverse of the complement mod `2^128`.

A fused step is reduced one word at a time, with the inverse of the complement mod `2^64`.

The fused operations interleave each word product with one reduction step.

That is the CIOS method of [Koç, Acar and Kaliski][cios].

[redc]: <https://doi.org/10.1090/S0025-5718-1985-0777282-X>

[cios]: <https://www.microsoft.com/en-us/research/publication/analyzing-and-comparing-montgomery-multiplication-algorithms/>
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Montgomery

/-- The radix of one word, `2^64`. -/
abbrev wordRadix : Nat := 2^64
/-- The complement of the modulus, `2^256 - p = 2^32 + 977`. -/
def complement : UInt64 := 4294968273
/-- The inverse of the complement mod `2^64`.

It is also `-p^(-1) mod 2^64`, since `-p = 2^32 + 977 mod 2^64`. -/
def inverseComplement : UInt64 := 0xd838091dd2253531

/-- Four words and a carry word above them, least significant first. -/
structure Words64 where
  /-- Bits 0 through 63. -/
  w0 : UInt64
  /-- Bits 64 through 127. -/
  w1 : UInt64
  /-- Bits 128 through 191. -/
  w2 : UInt64
  /-- Bits 192 through 255. -/
  w3 : UInt64
  /-- The carry above bit 255. -/
  top : UInt64

/-- The high word of the product of two words, from four 32-bit products. -/
@[inline] def mulHigh (a b : UInt64) : UInt64 :=
  let alo := a &&& 0xffffffff
  let ahi := a >>> 32
  let blo := b &&& 0xffffffff
  let bhi := b >>> 32
  let w0 := alo * blo
  let t := ahi * blo + (w0 >>> 32)
  let w1 := alo * bhi + (t &&& 0xffffffff)
  ahi * bhi + (t >>> 32) + (w1 >>> 32)

private abbrev halfRadix : Nat := 2^32

private theorem low_eq (x : UInt64) : (x &&& 0xffffffff).toNat = x.toNat % halfRadix := by
  rw [UInt64.toNat_and]
  change x.toNat &&& (2^32 - 1) = x.toNat % 2^32
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem high_eq (x : UInt64) : (x >>> 32).toNat = x.toNat / halfRadix := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

private theorem prod_le {a b : Nat} (ha : a < halfRadix) (hb : b < halfRadix) :
    a * b ≤ (halfRadix - 1) * (halfRadix - 1) := Nat.mul_le_mul (by omega) (by omega)

private theorem half_le {a : Nat} (ha : a < halfRadix) : a ≤ halfRadix - 1 := by omega

private theorem mul_exact {a b : UInt64} (h : a.toNat*b.toNat ≤ (halfRadix - 1)*(halfRadix - 1)) :
    (a*b).toNat = a.toNat*b.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h (by decide))]

private theorem add_exact {a b : UInt64} (h : a.toNat + b.toNat < 2^64) :
    (a+b).toNat = a.toNat+b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

private theorem model_mulHigh (a b c d : Nat) :
    let w0 := a * c
    let t := b * c + w0 / halfRadix
    let w1 := a * d + t % halfRadix
    ((a + halfRadix*b) * (c + halfRadix*d)) / (halfRadix*halfRadix) =
      b*d + t/halfRadix + w1/halfRadix := by
  dsimp only
  let w0 := a * c
  let t := b * c + w0 / halfRadix
  let w1 := a * d + t % halfRadix
  let lo := w0 % halfRadix + halfRadix * (w1 % halfRadix)
  let hi := b*d + t/halfRadix + w1/halfRadix
  have hlo : lo < halfRadix*halfRadix := by
    have h0 := half_le (Nat.mod_lt w0 (show 0 < halfRadix by decide))
    have h1 := half_le (Nat.mod_lt w1 (show 0 < halfRadix by decide))
    exact Nat.lt_of_le_of_lt (Nat.add_le_add h0 (Nat.mul_le_mul_left halfRadix h1)) (by decide)
  have h : (a + halfRadix*b) * (c + halfRadix*d) = lo + halfRadix*halfRadix*hi := by
    calc
      _ = w0 + halfRadix*(a*d + b*c) + halfRadix*halfRadix*(b*d) := by dsimp only [w0]; grind
      _ = w0 % halfRadix + halfRadix*(a*d + t) + halfRadix*halfRadix*(b*d) := by
        conv => lhs; rw [← Nat.mod_add_div w0 halfRadix]
        dsimp only [t]
        grind
      _ = w0 % halfRadix + halfRadix*(w1 + halfRadix*(t/halfRadix)) +
          halfRadix*halfRadix*(b*d) := by
        conv => lhs; rw [← Nat.mod_add_div t halfRadix]
        dsimp only [w1]
        grind
      _ = lo + halfRadix*halfRadix*hi := by
        conv => lhs; rw [← Nat.mod_add_div w1 halfRadix]
        dsimp only [lo, hi]
        grind
  change ((a + halfRadix*b) * (c + halfRadix*d)) / (halfRadix*halfRadix) = hi
  rw [h, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo, Nat.zero_add]

private theorem mulHigh_spec (a b : UInt64) : (mulHigh a b).toNat = a.toNat*b.toNat / 2^64 := by
  let a0 := a &&& 0xffffffff
  let a1 := a >>> 32
  let b0 := b &&& 0xffffffff
  let b1 := b >>> 32
  let w0 := a0*b0
  let t := a1*b0 + (w0 >>> 32)
  let w1 := a0*b1 + (t &&& 0xffffffff)
  have ha0 : a0.toNat < halfRadix := by rw [low_eq]; exact Nat.mod_lt _ (by decide)
  have hb0 : b0.toNat < halfRadix := by rw [low_eq]; exact Nat.mod_lt _ (by decide)
  have ha1 : a1.toNat < halfRadix := by
    rw [high_eq]
    exact Nat.div_lt_of_lt_mul a.toNat_lt
  have hb1 : b1.toNat < halfRadix := by
    rw [high_eq]
    exact Nat.div_lt_of_lt_mul b.toNat_lt
  have h00 := prod_le ha0 hb0
  have h01 := prod_le ha0 hb1
  have h10 := prod_le ha1 hb0
  have h11 := prod_le ha1 hb1
  have h0 : w0.toNat = a0.toNat*b0.toNat := mul_exact h00
  have ht : t.toNat = a1.toNat*b0.toNat + (w0.toNat/halfRadix) := by
    have hw0 : w0.toNat/halfRadix < halfRadix := Nat.div_lt_of_lt_mul w0.toNat_lt
    change (a1*b0 + (w0 >>> 32)).toNat = _
    rw [add_exact (by
      rw [mul_exact h10, high_eq w0]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add h10 (half_le hw0)) (by decide)),
      mul_exact h10, high_eq w0]
  have hw : w1.toNat = a0.toNat*b1.toNat + t.toNat % halfRadix := by
    have htm := Nat.mod_lt t.toNat (show 0 < halfRadix by decide)
    change (a0*b1 + (t &&& 0xffffffff)).toNat = _
    rw [add_exact (by
      rw [mul_exact h01, low_eq t]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add h01 (half_le htm)) (by decide)),
      mul_exact h01, low_eq t]
  have htd : t.toNat/halfRadix < halfRadix := Nat.div_lt_of_lt_mul t.toNat_lt
  have hwd : w1.toNat/halfRadix < halfRadix := Nat.div_lt_of_lt_mul w1.toNat_lt
  have he : (mulHigh a b).toNat = a1.toNat*b1.toNat + t.toNat/halfRadix + w1.toNat/halfRadix := by
    change (a1*b1 + (t >>> 32) + (w1 >>> 32)).toNat = _
    have h1 := Nat.add_le_add h11 (half_le htd)
    have e := add_exact (a := a1*b1) (b := t >>> 32) (by
      rw [mul_exact h11, high_eq t]
      exact Nat.lt_of_le_of_lt h1 (by decide))
    rw [add_exact (by
      rw [e, mul_exact h11, high_eq t, high_eq w1]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 (half_le hwd)) (by decide)),
      e, mul_exact h11, high_eq t, high_eq w1]
  rw [he, hw, ht, h0]
  have ea : a.toNat = a0.toNat + halfRadix*a1.toNat := by
    dsimp only [a0, a1]
    rw [low_eq a, high_eq a, Nat.mod_add_div]
  have eb : b.toNat = b0.toNat + halfRadix*b1.toNat := by
    dsimp only [b0, b1]
    rw [low_eq b, high_eq b, Nat.mod_add_div]
  conv => rhs; rw [ea, eb]
  exact (model_mulHigh a0.toNat a1.toNat b0.toNat b1.toNat).symm

/-- One for `true` and zero for `false`. -/
@[inline] def yes (b : Bool) : UInt64 := b.toUInt64

/-- The addition and its overflow bit represent the full 65-bit sum. -/
private theorem add_with_carry (a b : UInt64) :
    (a + b).toNat + 2^64 * (yes (a + b < a)).toNat = a.toNat + b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  by_cases h : a + b < a
  · have hl : (a.toNat + b.toNat) % 2^64 < a.toNat := by
      simpa only [UInt64.toNat_add] using (show (a + b).toNat < a.toNat from h)
    simp only [yes, Bool.toUInt64, h, decide_true, ite_true, UInt64.toNat_add,
      UInt64.toNat_one, Nat.mul_one]
    omega
  · have hl : ¬ (a.toNat + b.toNat) % 2^64 < a.toNat := by
      simpa only [UInt64.toNat_add] using (show ¬ (a + b).toNat < a.toNat from h)
    simp only [yes, Bool.toUInt64, h, decide_false, Bool.false_eq_true, ite_false, UInt64.toNat_add,
      UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
    omega

/-- Two words, least significant first. -/
structure Pair where
  /-- The low word. -/
  lo : UInt64
  /-- The high word, or the carry. -/
  hi : UInt64

/-- `a b + w + cin`, the step of a column, as two words. -/
@[inline] def mac (a b w cin : UInt64) : Pair :=
  let lo := a*b
  let hi := mulHigh a b
  let s := lo+w
  let t := s+cin
  ⟨t, hi + yes (s < lo) + yes (t < s)⟩

/-- The wide MAC represents the integer product and both added words. -/
private theorem mac_spec (a b w cin : UInt64) :
    (mac a b w cin).lo.toNat + 2^64 * (mac a b w cin).hi.toNat =
      a.toNat*b.toNat + w.toNat + cin.toNat := by
  let lo := a*b
  let hi := mulHigh a b
  let s := lo + w
  let t := s + cin
  let c1 := yes (s < lo)
  let c2 := yes (t < s)
  have hmul : lo.toNat + 2^64 * hi.toNat = a.toNat*b.toNat := by
    dsimp only [lo, hi]
    rw [UInt64.toNat_mul, mulHigh_spec, Nat.mod_add_div]
  have hadd1 : s.toNat + 2^64 * c1.toNat = lo.toNat + w.toNat := add_with_carry lo w
  have hadd2 : t.toNat + 2^64 * c2.toNat = s.toNat + cin.toNat := add_with_carry s cin
  have hproduct : a.toNat*b.toNat ≤ (2^64 - 1)*(2^64 - 1) := Nat.mul_le_mul
    (by have := a.toNat_lt; omega) (by have := b.toNat_lt; omega)
  have hw := w.toNat_lt
  have hc := cin.toNat_lt
  have eh : t.toNat + 2^64 * (hi.toNat + c1.toNat + c2.toNat) =
      a.toNat*b.toNat + w.toNat + cin.toNat := by omega
  have hh : hi.toNat + c1.toNat + c2.toNat < 2^64 := by omega
  change t.toNat + 2^64 * (hi + c1 + c2).toNat = _
  rw [add_exact (a := hi + c1) (b := c2) (by rw [add_exact (by omega)]; exact hh),
    add_exact (a := hi) (b := c1) (by omega)]
  exact eh


private def addComplement (r : Words64) : Words64 :=
  let v0 := r.w0 + complement
  let v1 := r.w1 + yes (v0 < r.w0)
  let v2 := r.w2 + yes (v1 < r.w1)
  let v3 := r.w3 + yes (v2 < r.w2)
  ⟨v0, v1, v2, v3, 0⟩

private def shouldReduce (r : Words64) : Bool :=
  r.top != 0 || (r.w3 == 0xffffffffffffffff && r.w2 == 0xffffffffffffffff &&
    r.w1 == 0xffffffffffffffff && r.w0 ≥ 0xfffffffefffffc2f)

/-- The reduction that the faster ones are proved against. -/
private def reduce (r : Words64) : Words64 :=
  if shouldReduce r then addComplement r else r

/-- The integer of the four low words. -/
def lowValue (w : Words64) : Nat :=
  w.w0.toNat + wordRadix*w.w1.toNat + wordRadix^2*w.w2.toNat + wordRadix^3*w.w3.toNat

/-- The integer of all five words. -/
def value (w : Words64) : Nat := lowValue w + wordRadix^4*w.top.toNat

private theorem lowValue_lt (w : Words64) : lowValue w < wordRadix^4 := by
  have h0 := w.w0.toNat_lt
  have h1 := w.w1.toNat_lt
  have h2 := w.w2.toNat_lt
  have h3 := w.w3.toNat_lt
  simp only [lowValue, wordRadix]
  omega

private theorem low_ge_iff (w : Words64) :
    (w.w3 == 0xffffffffffffffff && w.w2 == 0xffffffffffffffff &&
      w.w1 == 0xffffffffffffffff && w.w0 ≥ 0xfffffffefffffc2f) = true ↔
      Fp.modulus ≤ lowValue w := by
  have h0 := w.w0.toNat_lt
  have h1 := w.w1.toNat_lt
  have h2 := w.w2.toNat_lt
  have h3 := w.w3.toNat_lt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj,
    UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, lowValue, Fp.modulus, wordRadix]
  omega

private theorem reduce_condition_iff (w : Words64) :
    shouldReduce w = true ↔ Fp.modulus ≤ value w := by
  unfold shouldReduce
  have htop : (w.top != 0) = true ↔ w.top.toNat ≠ 0 := by
    simp only [bne_iff_ne]
    have h : w.top.toNat = (0 : UInt64).toNat ↔ w.top = (0 : UInt64) := UInt64.toNat_inj
    rw [UInt64.toNat_zero] at h
    exact not_congr h.symm
  simp only [Bool.or_eq_true, htop, low_ge_iff, value, wordRadix]
  have hp : Fp.modulus < 2^256 := by decide
  omega

private theorem sub_split (a b : UInt64) :
    (a-b).toNat + b.toNat = a.toNat + wordRadix * (yes (a < b)).toNat := by
  have ha : a.toNat < wordRadix := a.toNat_lt
  have hb : b.toNat < wordRadix := b.toNat_lt
  simp only [wordRadix] at *
  by_cases h : a < b
  · have hn : a.toNat < b.toNat := h
    simp [yes, Bool.toUInt64, h, UInt64.toNat_sub]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have hn : ¬ a.toNat < b.toNat := h
    have hab : b ≤ a := by change b.toNat ≤ a.toNat; omega
    simp [yes, Bool.toUInt64, h, UInt64.toNat_sub_of_le _ _ hab]
    omega

private theorem radix_q (s : UInt64) : s * inverseComplement * complement = s := by
  rw [UInt64.mul_assoc, show inverseComplement * complement = 1 by decide, UInt64.mul_one]

/-- The complementary modulus and its inverse modulo the word radix. -/
structure CancellationConstants where
  /-- `2^256 - p`. -/
  factor : UInt64
  /-- The inverse of the factor modulo `2^64`. -/
  inverse : UInt64

/-- Keep both factors as words when compiling the cancellation.

The compiler can use a wide multiply when it reads the factors at runtime.
-/
@[noinline] def cancellationConstants : CancellationConstants := ⟨complement, inverseComplement⟩

/-- Return the high word of `q * (2^32 + 977)`. -/
@[inline] def mulHighComplement (q : UInt64) : UInt64 := mulHigh q cancellationConstants.factor

private theorem mulHighComplement_spec (q : UInt64) :
    (mulHighComplement q).toNat = q.toNat * complement.toNat / wordRadix := mulHigh_spec q _

/-- One step of reduction: add `q p`, with `q = -s0 p^(-1) mod 2^64`, then drop the low word.

The sum clears the low word, so dropping it divides by `2^64`. -/
@[inline] def red (highProd : UInt64 → UInt64 → UInt64) (s0 s1 s2 s3 s4 s5 : UInt64) : Words64 :=
  let q := s0 * cancellationConstants.inverse
  let d := highProd q complement
  let v0 := s1 - d
  let v3 := s4 + q
  let h := s5 + yes (v3 < s4)
  if s1 ≥ d then ⟨v0, s2, s3, v3, h⟩
  else
    let b1 := yes (s2 = 0)
    let b2 := yes (s3 < b1)
    ⟨v0, s2 - 1, s3 - b1, v3 - b2, h - yes (v3 < b2)⟩

private theorem red_spec (mulHi : UInt64 → UInt64 → UInt64)
    (hiSpec : ∀ a, (mulHi a complement).toNat = a.toNat * complement.toNat / wordRadix)
    (s0 s1 s2 s3 s4 s5 : UInt64) (hs5 : s5.toNat ≤ 2) :
    wordRadix * value (red mulHi s0 s1 s2 s3 s4 s5) =
      s0.toNat + wordRadix * value ⟨s1,s2,s3,s4,s5⟩ +
        (s0 * inverseComplement).toNat * Fp.modulus := by
  let q := s0 * cancellationConstants.inverse
  let d := mulHi q complement
  let v0 := s1 - d
  let v3 := s4 + q
  let h := s5 + yes (v3 < s4)
  have hprod : q.toNat * complement.toNat = s0.toNat + wordRadix * d.toNat := by
    have hlow := congrArg UInt64.toNat (radix_q s0)
    rw [UInt64.toNat_mul] at hlow
    change q.toNat * complement.toNat % wordRadix = s0.toNat at hlow
    rw [show d.toNat = q.toNat * complement.toNat / wordRadix from hiSpec _,
      ← hlow, Nat.mod_add_div]
  have hv3 : v3.toNat + wordRadix * (yes (v3 < s4)).toNat = s4.toNat + q.toNat :=
    add_with_carry s4 q
  have hcarry (b : Bool) : (yes b).toNat ≤ 1 := by cases b <;> decide
  have hh : h.toNat = s5.toNat + (yes (v3 < s4)).toNat := by
    change (s5 + yes (v3 < s4)).toNat = _
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have := hcarry (v3 < s4); omega)]
  have hpc : Fp.modulus + complement.toNat = wordRadix^4 := by decide
  have hmul := congrArg (q.toNat * ·) hpc
  rw [Nat.mul_add] at hmul
  change wordRadix * value (if s1 ≥ d then ⟨v0, s2, s3, v3, h⟩ else _) = _
  split
  · rename_i hgood
    have h0 : v0.toNat + d.toNat = s1.toNat := by
      change (s1-d).toNat + d.toNat = _
      rw [UInt64.toNat_sub_of_le _ _ hgood]
      have hx : d.toNat ≤ s1.toNat := hgood
      omega
    change wordRadix * value ⟨v0,s2,s3,v3,h⟩ =
      s0.toNat + wordRadix * value ⟨s1,s2,s3,s4,s5⟩ + q.toNat * Fp.modulus
    simp only [value, lowValue, wordRadix] at *
    omega
  · rename_i hbad
    have hy : s1 < d := by change s1.toNat < d.toNat; change ¬ d.toNat ≤ s1.toNat at hbad; omega
    have h0 : v0.toNat + d.toNat = s1.toNat + wordRadix := by
      simpa [hy, yes, Bool.toUInt64] using sub_split s1 d
    let b1 := yes (s2 = 0)
    let b2 := yes (s3 < b1)
    let b3 := yes (v3 < b2)
    have e1 : (s2 - 1).toNat + 1 = s2.toNat + wordRadix * b1.toNat := by
      have e : (s2 < (1 : UInt64)) = (s2 = 0) := propext (by
        change s2.toNat < 1 ↔ s2 = 0
        rw [← UInt64.toNat_inj, UInt64.toNat_zero]; omega)
      simpa only [e, UInt64.toNat_one] using sub_split s2 1
    have e2 : (s3-b1).toNat + b1.toNat = s3.toNat + wordRadix * b2.toNat :=
      sub_split s3 b1
    have e3 : (v3-b2).toNat + b2.toNat = v3.toNat + wordRadix * b3.toNat :=
      sub_split v3 b2
    have hb3 : b3 ≤ h := by
      by_cases hn : b3 ≤ h
      · exact hn
      have hn' : ¬ b3.toNat ≤ h.toNat := hn
      have hb3' : b3.toNat ≤ 1 := hcarry _
      have hz : h.toNat = 0 := by omega
      have hb : v3 < b2 := by
        by_cases hv : v3 < b2
        · exact hv
        · have hfalse : b3.toNat = 0 := by simp [b3, yes, Bool.toUInt64, hv]
          omega
      have hv : v3.toNat < b2.toNat := hb
      have hb2' : b2.toNat ≤ 1 := hcarry _
      have hq : q.toNat = 0 := by simp only [wordRadix] at hv3; omega
      have hd : d.toNat = 0 := by simp [d, hiSpec, hq]
      have hbad' : s1.toNat < d.toNat := hy
      omega
    have e4 : (h-b3).toNat + b3.toNat = h.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hb3]
      have hb3' : b3.toNat ≤ h.toNat := hb3
      omega
    change wordRadix * value ⟨v0,s2-1,s3-b1,v3-b2,h-b3⟩ =
      s0.toNat + wordRadix * value ⟨s1,s2,s3,s4,s5⟩ + q.toNat * Fp.modulus
    simp only [value, lowValue, wordRadix] at *
    omega


/-- The low and high words of an unsigned product. -/
@[inline] def wordProduct (a b : UInt64) : Pair := ⟨a * b, mulHigh a b⟩

private theorem wordProduct_comm (a b : UInt64) : wordProduct a b = wordProduct b a := by
  have h : mulHigh a b = mulHigh b a := by
    apply UInt64.toNat_inj.mp
    rw [mulHigh_spec, mulHigh_spec, Nat.mul_comm a.toNat b.toNat]
  unfold wordProduct
  rw [UInt64.mul_comm a b, h]

private theorem reduction_from_add {lo top out carry p c : Nat}
    (hpc : p + c = 2^256) (hout : out < 2^256)
    (he : out + 2^256*carry = lo + c)
    (hge : p ≤ lo + 2^256*top) (hlt : lo + 2^256*top < 2*p) :
    out = (lo + 2^256*top) % p := by
  have hsum : top + carry = 1 := by omega
  rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem add_chain {w0 w1 w2 w3 v0 v1 v2 v3 x c0 c1 c2 c3 : Nat}
    (h0 : v0 + wordRadix*c0 = w0 + x) (h1 : v1 + wordRadix*c1 = w1 + c0)
    (h2 : v2 + wordRadix*c2 = w2 + c1) (h3 : v3 + wordRadix*c3 = w3 + c2) :
    v0 + wordRadix*v1 + wordRadix^2*v2 + wordRadix^3*v3 + wordRadix^4*c3 =
      w0 + wordRadix*w1 + wordRadix^2*w2 + wordRadix^3*w3 + x := by
  simp only [wordRadix] at *
  omega

private theorem top_mk (w0 w1 w2 w3 top : UInt64) : (Words64.mk w0 w1 w2 w3 top).top = top := rfl

private theorem value_mk_zero (w0 w1 w2 w3 : UInt64) :
    value (Words64.mk w0 w1 w2 w3 0) =
      w0.toNat + wordRadix*w1.toNat + wordRadix^2*w2.toNat + wordRadix^3*w3.toNat := by
  simp only [value, lowValue, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]

private theorem addComplement_top (r : Words64) : (addComplement r).top = 0 :=
  top_mk _ _ _ _ 0

private theorem addComplement_value (r : Words64) :
    value (addComplement r) + wordRadix ^ 4 * (yes ((addComplement r).w3 < r.w3)).toNat =
      lowValue r + complement.toNat := by
  let v0 := r.w0 + complement
  let v1 := r.w1 + yes (v0 < r.w0)
  let v2 := r.w2 + yes (v1 < r.w1)
  let v3 := r.w3 + yes (v2 < r.w2)
  change value (Words64.mk v0 v1 v2 v3 0) + wordRadix ^ 4 * (yes (v3 < r.w3)).toNat = _
  rw [value_mk_zero, lowValue]
  exact add_chain (add_with_carry r.w0 complement) (add_with_carry r.w1 (yes (v0 < r.w0)))
    (add_with_carry r.w2 (yes (v1 < r.w1))) (add_with_carry r.w3 (yes (v2 < r.w2)))

private theorem value_low_of_top_zero (w : Words64) (h : w.top = 0) :
    value w = lowValue w := by
  simp only [value, h, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]

private theorem value_as_nat (w : Words64) : value w = lowValue w + 2^256*w.top.toNat := rfl

private theorem remainder_of_complement (r v : Words64) (carry : Nat)
    (ht : v.top = 0) (he : value v + wordRadix^4*carry = lowValue r + complement.toNat)
    (hge : Fp.modulus ≤ value r) (hbound : value r < 2*Fp.modulus) :
    value v = value r % Fp.modulus := by
  have hv : value v < wordRadix^4 := by rw [value_low_of_top_zero v ht]; exact lowValue_lt v
  rw [value_as_nat r] at hge hbound ⊢
  exact reduction_from_add (by decide : Fp.modulus + complement.toNat = 2^256) hv he hge hbound

private theorem reduce_yes (r : Words64) (hge : Fp.modulus ≤ value r)
    (hbound : value r < 2*Fp.modulus) :
    (addComplement r).top = 0 ∧ value (addComplement r) = value r % Fp.modulus :=
  ⟨addComplement_top r,
    remainder_of_complement r (addComplement r) (yes ((addComplement r).w3 < r.w3)).toNat
      (addComplement_top r) (addComplement_value r) hge hbound⟩

private theorem reduce_no (r : Words64) (hlt : value r < Fp.modulus) :
    r.top = 0 ∧ value r = value r % Fp.modulus := by
  have hp : Fp.modulus < wordRadix^4 := by decide
  have htop : r.top.toNat = 0 := by
    simp only [value, wordRadix] at hlt
    simp only [wordRadix] at hp
    omega
  exact ⟨UInt64.toNat_inj.mp (by simpa only [UInt64.toNat_zero] using htop),
    (Nat.mod_eq_of_lt hlt).symm⟩

private theorem ite_predicate {α : Type} (P : α → Prop) (condition : Bool) (y n : α)
    (hy : condition = true → P y) (hn : ¬ condition = true → P n) :
    P (if condition then y else n) := by
  cases condition
  · exact hn (by decide)
  · exact hy rfl

/-- Reduction reads as the remainder and leaves no word above the 256-bit result. -/
private theorem reduce_spec (r : Words64) (hbound : value r < 2*Fp.modulus) :
    (reduce r).top = 0 ∧ value (reduce r) = value r % Fp.modulus :=
  ite_predicate (fun w : Words64 => w.top = 0 ∧ value w = value r % Fp.modulus)
    (shouldReduce r) (addComplement r) r
    (fun h => reduce_yes r ((reduce_condition_iff r).1 h) hbound)
    (fun h => reduce_no r (Nat.lt_of_not_ge (fun hc => h ((reduce_condition_iff r).2 hc))))

/-- A 256-bit integer in four words, with the least significant word first. -/
structure Raw where
  /-- Bits 0 through 63. -/
  w0 : UInt64
  /-- Bits 64 through 127. -/
  w1 : UInt64
  /-- Bits 128 through 191. -/
  w2 : UInt64
  /-- Bits 192 through 255. -/
  w3 : UInt64
deriving DecidableEq

/-- The four low words, without the carry word. -/
@[inline] def Raw.fromWords (r : Words64) : Raw := ⟨r.w0, r.w1, r.w2, r.w3⟩

/-- Extend the four words with a zero carry word. -/
@[inline] def Raw.words (t : Raw) : Words64 := ⟨t.w0, t.w1, t.w2, t.w3, 0⟩

/-- The natural number represented by the four words. -/
def Raw.val (t : Raw) : Nat := lowValue t.words

theorem Raw.val_eq (t : Raw) : t.val = value t.words := by
  rw [value_low_of_top_zero _ rfl]
  rfl

theorem Raw.fromWords_val (w : Words64) (h : w.top = 0) :
    (Raw.fromWords w).val = value w := by
  rw [value_low_of_top_zero w h]
  rfl

end Montgomery

/-- An element of the base field in Montgomery form, with `R = 2^256`.

The words hold `a R mod p`, below `p`, so each element has one encoding. -/
structure Montgomery where
  /-- The canonical Montgomery residue. -/
  raw : Montgomery.Raw
  /-- A residue below the field modulus has a unique encoding. -/
  lt : raw.val < Fp.modulus
deriving DecidableEq

/-- An element of the base field held in Montgomery form. -/
abbrev Fp.Montgomery := Secp256k1.Montgomery

namespace Montgomery

/-- Zero, whose Montgomery form is zero. -/
instance : OfNat Montgomery 0 := ⟨⟨⟨0, 0, 0, 0⟩, by decide⟩⟩

/-- One, whose Montgomery form is `R mod p = 2^32 + 977`. -/
instance : OfNat Montgomery 1 := ⟨⟨⟨0x1000003d1, 0, 0, 0⟩, by decide⟩⟩

/-- Add the masked complement when the words represent an integer at least `p`. -/
@[inline] def reduceMasked (r : Words64) : Words64 :=
  let ge := yes ((r.w3 &&& r.w2 &&& r.w1) == 0xffffffffffffffff) &&&
    yes (r.w0 ≥ 0xfffffffefffffc2f)
  let flag := yes (r.top != 0) ||| ge
  let addend := complement &&& ((0 : UInt64) - flag)
  let v0 := r.w0 + addend
  let v1 := r.w1 + yes (v0 < r.w0)
  let v2 := r.w2 + yes (v1 < r.w1)
  let v3 := r.w3 + yes (v2 < r.w2)
  ⟨v0, v1, v2, v3, 0⟩

private theorem and_all_bits_iff (a b : UInt64) :
    a &&& b = 0xffffffffffffffff ↔ a = 0xffffffffffffffff ∧ b = 0xffffffffffffffff := by
  constructor
  · intro h
    have hn := congrArg UInt64.toNat h
    rw [UInt64.toNat_and] at hn
    change a.toNat &&& b.toNat = 2^64 - 1 at hn
    have ha := Nat.and_le_left (n := a.toNat) (m := b.toNat)
    have hb := Nat.and_le_right (n := a.toNat) (m := b.toNat)
    have halt := a.toNat_lt
    have hblt := b.toNat_lt
    constructor <;> apply UInt64.toNat_inj.mp <;> change _ = 2^64 - 1 <;> omega
  · rintro ⟨rfl, rfl⟩
    decide

private theorem lowFlag_eq (r : Words64) :
    ((r.w3 &&& r.w2 &&& r.w1) == 0xffffffffffffffff) =
      (r.w3 == 0xffffffffffffffff && r.w2 == 0xffffffffffffffff &&
        r.w1 == 0xffffffffffffffff) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq, and_all_bits_iff, and_assoc]

private theorem yes_and (a b : Bool) : yes a &&& yes b = yes (a && b) := by
  cases a <;> cases b <;> decide

private theorem yes_or (a b : Bool) : yes a ||| yes b = yes (a || b) := by
  cases a <;> cases b <;> decide

private theorem mask_complement (b : Bool) :
    complement &&& ((0 : UInt64) - yes b) = if b then complement else 0 := by
  cases b <;> decide

private theorem shouldReduce_top_zero (r : Words64) (h : shouldReduce r = false) : r.top = 0 := by
  by_cases ht : r.top = 0
  · exact ht
  · have hb : (r.top != 0) = true := bne_iff_ne.mpr ht
    simp only [shouldReduce, hb, Bool.true_or] at h
    contradiction

/-- Masked correction and conditional correction give identical words. -/
private theorem reduceMasked_eq_reduce (r : Words64) : reduceMasked r = reduce r := by
  unfold reduceMasked
  simp only [lowFlag_eq, yes_and, yes_or, Bool.and_assoc]
  change _ =
    if shouldReduce r then addComplement r else r
  have he :
      (yes (r.top != 0 || (r.w3 == 0xffffffffffffffff && (r.w2 == 0xffffffffffffffff &&
        (r.w1 == 0xffffffffffffffff && r.w0 ≥ 0xfffffffefffffc2f))))) =
      yes (shouldReduce r) := by
    simp only [shouldReduce, Bool.and_assoc]
  rw [he, mask_complement]
  cases h : shouldReduce r with
  | false =>
    have ht := shouldReduce_top_zero r h
    cases r with
    | mk _ _ _ _ top =>
      change top = 0 at ht
      subst top
      simp [yes, Bool.toUInt64]
  | true => simp only [ite_true, addComplement]

theorem reduceMasked_spec (r : Words64) (h : value r < 2*Fp.modulus) :
    (reduceMasked r).top = 0 ∧ value (reduceMasked r) = value r % Fp.modulus := by
  rw [reduceMasked_eq_reduce]
  exact reduce_spec r h

/-- Reduce with a single-word correction when the low word leaves room for it. -/
@[inline] def reduceFast (r : Words64) : Words64 :=
  if r.w0 < 0xfffffffefffffc2f then
    let addend : UInt64 := if r.top == 0 then 0 else complement
    ⟨r.w0 + addend, r.w1, r.w2, r.w3, 0⟩
  else reduceMasked r

theorem reduceFast_eq_reduceMasked (r : Words64) : reduceFast r = reduceMasked r := by
  unfold reduceFast
  split
  · next h =>
    rw [reduceMasked_eq_reduce]
    have hn : ¬ r.w0 ≥ 0xfffffffefffffc2f := UInt64.not_le.mpr h
    by_cases hz : r.top = 0
    · simp [reduce, shouldReduce, hz, hn]
      cases r
      simp_all
    · have hh : (r.top != 0) = true := by simp [hz]
      have hh' : (r.top == 0) = false := by simp [hz]
      have hn' : (r.w0 + complement).toNat < r.w0.toNat → False := by
        have hv : r.w0.toNat < 0xfffffffefffffc2f := h
        rw [UInt64.toNat_add, show complement.toNat = 4294968273 by decide]
        omega
      have hnc : ¬ r.w0 + complement < r.w0 := hn'
      simp [reduce, shouldReduce, hh, hh', addComplement, hnc, yes, Bool.toUInt64]
  · rfl

theorem reduceFast_spec (r : Words64) (h : value r < 2*Fp.modulus) :
    (reduceFast r).top = 0 ∧ value (reduceFast r) = value r % Fp.modulus := by
  rw [reduceFast_eq_reduceMasked]
  exact reduceMasked_spec r h

/-- Reduce the intermediate words and keep the canonical residue. -/
@[inline] def finish (t : Words64) (ht : value t < 2*Fp.modulus) : Montgomery :=
  let u := reduceFast t
  have hu := reduceFast_spec t ht
  ⟨Raw.fromWords u, by
    rw [Raw.fromWords_val u hu.1, hu.2]
    exact Nat.mod_lt _ (by decide)⟩

/-- Three words hold the sum of the products in one column. -/
structure ProductColumn where
  /-- The word of the column itself. -/
  lo : UInt64
  /-- The carry into the next column. -/
  mid : UInt64
  /-- The carry into the column after it. -/
  hi : UInt64

/-- The integer of the three words of a column. -/
def ProductColumn.val (c : ProductColumn) : Nat :=
  c.lo.toNat + wordRadix * c.mid.toNat + wordRadix^2 * c.hi.toNat

/-- Add a two-word product to a column, with its carries. -/
@[inline] def ProductColumn.add (c : ProductColumn) (p : Pair) : ProductColumn :=
  let lo := c.lo + p.lo
  let mid := c.mid + p.hi
  let word := mid + yes (lo < c.lo)
  ⟨lo, word, c.hi + yes (mid < c.mid) + yes (word < mid)⟩

/-- Move to the next column: the carries become its words. -/
@[inline] def ProductColumn.next (c : ProductColumn) : ProductColumn := ⟨c.mid, c.hi, 0⟩

private theorem wordProduct_value (a b : UInt64) :
    (wordProduct a b).lo.toNat + wordRadix * (wordProduct a b).hi.toNat = a.toNat * b.toNat := by
  simp only [wordProduct, UInt64.toNat_mul, mulHigh_spec, wordRadix]
  exact Nat.mod_add_div _ _

private theorem ProductColumn.add_spec (c : ProductColumn) (p : Pair) (hb : c.hi.toNat < 16) :
    (c.add p).val = c.val + p.lo.toNat + wordRadix * p.hi.toNat ∧
      (c.add p).hi.toNat ≤ c.hi.toNat + 2 := by
  let lo := c.lo + p.lo
  let mid := c.mid + p.hi
  let k := yes (lo < c.lo)
  let word := mid + k
  let j := yes (mid < c.mid)
  let h := yes (word < mid)
  have e0 : lo.toNat + 2^64 * k.toNat = c.lo.toNat + p.lo.toNat :=
    add_with_carry c.lo p.lo
  have e1 : mid.toNat + 2^64 * j.toNat = c.mid.toNat + p.hi.toNat :=
    add_with_carry c.mid p.hi
  have e2 : word.toNat + 2^64 * h.toNat = mid.toNat + k.toNat :=
    add_with_carry mid k
  have hiFlag (b : Bool) : (yes b).toNat ≤ 1 := by cases b <;> decide
  have ej : j.toNat ≤ 1 := hiFlag _
  have eh : h.toNat ≤ 1 := hiFlag _
  have ht1 : (c.hi + j).toNat = c.hi.toNat + j.toNat := add_exact (by omega)
  have ht2 : (c.hi + j + h).toNat = c.hi.toNat + j.toNat + h.toNat := by
    rw [add_exact (by rw [ht1]; omega), ht1]
  change lo.toNat + 2^64 * word.toNat + 2^128 * (c.hi + j + h).toNat =
    c.lo.toNat + 2^64 * c.mid.toNat + 2^128 * c.hi.toNat + p.lo.toNat +
      2^64 * p.hi.toNat ∧ _
  change _ ∧ (c.hi + j + h).toNat ≤ c.hi.toNat + 2
  rw [ht2]
  omega

private theorem ProductColumn.product_spec (c : ProductColumn) (a b : UInt64)
    (hb : c.hi.toNat < 16) :
    (c.add (wordProduct a b)).val = c.val + a.toNat * b.toNat ∧
      (c.add (wordProduct a b)).hi.toNat ≤ c.hi.toNat + 2 := by
  obtain ⟨hv, hh⟩ := c.add_spec (wordProduct a b) hb
  rw [Nat.add_assoc, wordProduct_value] at hv
  exact ⟨hv, hh⟩

private theorem ProductColumn.next_spec (c : ProductColumn) :
    c.val = c.lo.toNat + wordRadix * c.next.val := by
  simp only [ProductColumn.val, ProductColumn.next, UInt64.toNat_zero, Nat.mul_zero,
    Nat.add_zero, wordRadix]
  omega

/-- Add the next high product word and cancel one low word. -/
@[inline] def reduceColumn (r : Words64) (high : UInt64) : Words64 :=
  let s := r.top + high
  red (fun q _ => mulHighComplement q) r.w0 r.w1 r.w2 r.w3 s (yes (s < r.top))

private theorem reduceColumn_spec (r : Words64) (high : UInt64) :
    wordRadix * value (reduceColumn r high) =
      value r + wordRadix^4*high.toNat + (r.w0 * inverseComplement).toNat * Fp.modulus := by
  let s := r.top + high
  let t := yes (s < r.top)
  have hb : t.toNat ≤ 1 := by
    change (yes (decide _)).toNat ≤ 1
    cases decide (s < r.top) <;> decide
  have he := red_spec (fun q _ => mulHighComplement q) mulHighComplement_spec
    r.w0 r.w1 r.w2 r.w3 s t (by omega)
  have hh : s.toNat + wordRadix*t.toNat = r.top.toNat + high.toNat := add_with_carry r.top high
  change wordRadix * value (reduceColumn r high) =
    r.w0.toNat + wordRadix * value ⟨r.w1, r.w2, r.w3, s, t⟩ +
      (r.w0 * inverseComplement).toNat * Fp.modulus at he
  simp only [value, lowValue, wordRadix] at he hh ⊢
  omega

/-- Cancel the four low words of a wide product. -/
@[inline] def reduceWideProduct (low high : Words64) : Words64 :=
  let r := reduceColumn {low with top := high.w0} 0
  let r := reduceColumn r high.w1
  let r := reduceColumn r high.w2
  reduceColumn r high.w3

private theorem reduceWideProduct_math
    (low w0 w1 w2 w3 r0 r1 r2 r3 q0 q1 q2 q3 : Nat)
    (e0 : wordRadix*r0 = low + wordRadix^4*w0 + q0*Fp.modulus)
    (e1 : wordRadix*r1 = r0 + wordRadix^4*w1 + q1*Fp.modulus)
    (e2 : wordRadix*r2 = r1 + wordRadix^4*w2 + q2*Fp.modulus)
    (e3 : wordRadix*r3 = r2 + wordRadix^4*w3 + q3*Fp.modulus)
    (hq0 : q0 < wordRadix) (hq1 : q1 < wordRadix)
    (hq2 : q2 < wordRadix) (hq3 : q3 < wordRadix)
    (ht : low + wordRadix^4*(w0 + wordRadix*w1 + wordRadix^2*w2 + wordRadix^3*w3) <
      Fp.modulus^2) :
    r3 < 2 * Fp.modulus ∧
      (wordRadix^4 * r3) % Fp.modulus =
        (low + wordRadix^4*(w0 + wordRadix*w1 + wordRadix^2*w2 + wordRadix^3*w3)) % Fp.modulus := by
  let q := q0 + wordRadix*q1 + wordRadix^2*q2 + wordRadix^3*q3
  have he : wordRadix^4*r3 =
      low + wordRadix^4*(w0 + wordRadix*w1 + wordRadix^2*w2 + wordRadix^3*w3) + q*Fp.modulus := by
    simp only [q, Nat.mul_add, Nat.add_mul, wordRadix, Fp.modulus] at e0 e1 e2 e3 ⊢
    omega
  have hq : q < wordRadix^4 := by
    simp only [q, wordRadix] at hq0 hq1 hq2 hq3 ⊢
    omega
  have hqp := Nat.mul_le_mul_right Fp.modulus (Nat.le_of_lt hq)
  refine ⟨?_, by rw [he, Nat.add_mul_mod_self_right]⟩
  simp only [wordRadix, Fp.modulus] at he hqp ht ⊢
  omega

theorem reduceWideProduct_spec (low high : Words64)
    (h : lowValue low + wordRadix^4 * lowValue high < Fp.modulus^2) :
    value (reduceWideProduct low high) < 2 * Fp.modulus ∧
      (wordRadix^4 * value (reduceWideProduct low high)) % Fp.modulus =
        (lowValue low + wordRadix^4 * lowValue high) % Fp.modulus := by
  let a := {low with top := high.w0}
  let r0 := reduceColumn a 0
  let r1 := reduceColumn r0 high.w1
  let r2 := reduceColumn r1 high.w2
  let r3 := reduceColumn r2 high.w3
  let q0 := (a.w0 * inverseComplement).toNat
  let q1 := (r0.w0 * inverseComplement).toNat
  let q2 := (r1.w0 * inverseComplement).toNat
  let q3 := (r2.w0 * inverseComplement).toNat
  have h0 : wordRadix * value r0 = lowValue low + wordRadix^4*high.w0.toNat + q0*Fp.modulus := by
    have e : value a = lowValue low + wordRadix^4*high.w0.toNat := rfl
    have h := reduceColumn_spec a 0
    rw [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero, e] at h
    exact h
  have h1 : wordRadix * value r1 = value r0 + wordRadix^4*high.w1.toNat + q1*Fp.modulus :=
    reduceColumn_spec r0 high.w1
  have h2 : wordRadix * value r2 = value r1 + wordRadix^4*high.w2.toNat + q2*Fp.modulus :=
    reduceColumn_spec r1 high.w2
  have h3 : wordRadix * value r3 = value r2 + wordRadix^4*high.w3.toNat + q3*Fp.modulus :=
    reduceColumn_spec r2 high.w3
  exact reduceWideProduct_math (lowValue low) high.w0.toNat high.w1.toNat
    high.w2.toNat high.w3.toNat
    (value r0) (value r1) (value r2) (value r3) q0 q1 q2 q3 h0 h1 h2 h3
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _) h

/-- Add two copies of a product after doubling it once. -/
@[inline] def ProductColumn.addDouble (c : ProductColumn) (p : Pair) : ProductColumn :=
  let d := (⟨p.lo, p.hi, 0⟩ : ProductColumn).add p
  let sum := c.add ⟨d.lo, d.mid⟩
  {sum with hi := sum.hi + d.hi}

private theorem ProductColumn.double_spec (c : ProductColumn) (a b : UInt64)
    (hb : c.hi.toNat < 16) :
    (c.addDouble (wordProduct a b)).val = c.val + a.toNat*b.toNat + a.toNat*b.toNat ∧
      (c.addDouble (wordProduct a b)).hi.toNat ≤ c.hi.toNat + 4 := by
  let p := wordProduct a b
  let d := (⟨p.lo, p.hi, 0⟩ : ProductColumn).add p
  let sum := c.add ⟨d.lo, d.mid⟩
  have hp := wordProduct_value a b
  change p.lo.toNat + wordRadix*p.hi.toNat = _ at hp
  obtain ⟨hd, hdhi⟩ := ProductColumn.add_spec (⟨p.lo, p.hi, 0⟩ : ProductColumn) p
    (by change (0 : UInt64).toNat < 16; decide)
  change d.val = (⟨p.lo, p.hi, 0⟩ : ProductColumn).val + p.lo.toNat + wordRadix*p.hi.toNat at hd
  change d.hi.toNat ≤ (0 : UInt64).toNat + 2 at hdhi
  rw [UInt64.toNat_zero, Nat.zero_add] at hdhi
  have hpv : (⟨p.lo, p.hi, 0⟩ : ProductColumn).val = p.lo.toNat + wordRadix*p.hi.toNat := by
    simp only [ProductColumn.val, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
  obtain ⟨hs, hshi⟩ := ProductColumn.add_spec c ⟨d.lo, d.mid⟩ hb
  change sum.hi.toNat ≤ c.hi.toNat + 2 at hshi
  change sum.val = c.val + d.lo.toNat + wordRadix*d.mid.toNat at hs
  have hadd : (sum.hi + d.hi).toNat = sum.hi.toNat + d.hi.toNat := add_exact (by omega)
  change ({sum with hi := sum.hi + d.hi} : ProductColumn).val = _ ∧ _
  change _ ∧ (sum.hi + d.hi).toNat ≤ _
  simp only [ProductColumn.val, wordRadix] at hpv hp hd hs ⊢
  rw [hadd]
  omega

/-- Add a precomputed column to the carry from the preceding column. -/
@[inline] def ProductColumn.addColumn (c t : ProductColumn) : ProductColumn :=
  let r := c.add ⟨t.lo, t.mid⟩
  {r with hi := r.hi + t.hi}

private theorem ProductColumn.addColumn_spec (c t : ProductColumn)
    (hc : c.hi.toNat < 16) (ht : t.hi.toNat ≤ 8) :
    (c.addColumn t).val = c.val + t.val := by
  let r := c.add ⟨t.lo, t.mid⟩
  obtain ⟨hv, hh⟩ := c.add_spec ⟨t.lo, t.mid⟩ hc
  change r.val = c.val + t.lo.toNat + wordRadix*t.mid.toNat at hv
  change r.hi.toNat ≤ c.hi.toNat + 2 at hh
  have hsum : (r.hi + t.hi).toNat = r.hi.toNat + t.hi.toNat := add_exact (by omega)
  change ({r with hi := r.hi + t.hi} : ProductColumn).val = c.val + t.val
  simp only [ProductColumn.val, wordRadix] at hv ⊢
  rw [hsum]
  omega

/-- Compute the wide square one word column at a time.

Sum each of the three middle columns before adding the carry from the preceding column.
-/
@[inline] def squareColumns (a : Words64) : Words64 × Words64 :=
  let zero : ProductColumn := ⟨0, 0, 0⟩
  let c0 := zero.add (wordProduct a.w0 a.w0)
  let c1 := c0.next.addDouble (wordProduct a.w0 a.w1)
  let p2 := (zero.addDouble (wordProduct a.w0 a.w2)).add (wordProduct a.w1 a.w1)
  let p3 := (zero.addDouble (wordProduct a.w0 a.w3)).addDouble (wordProduct a.w1 a.w2)
  let p4 := (zero.addDouble (wordProduct a.w1 a.w3)).add (wordProduct a.w2 a.w2)
  let c2 := c1.next.addColumn p2
  let c3 := c2.next.addColumn p3
  let c4 := c3.next.addColumn p4
  let c5 := c4.next.addDouble (wordProduct a.w2 a.w3)
  let c6 := c5.next.add (wordProduct a.w3 a.w3)
  (⟨c0.lo, c1.lo, c2.lo, c3.lo, 0⟩, ⟨c4.lo, c5.lo, c6.lo, c6.mid, 0⟩)

private theorem squareColumns_spec (a : Words64) :
    lowValue (squareColumns a).1 +
      wordRadix^4 * lowValue (squareColumns a).2 =
      lowValue a * lowValue a := by
  let c0start : ProductColumn := ⟨0, 0, 0⟩
  let c0 := c0start.add (wordProduct a.w0 a.w0)
  let c1start : ProductColumn := c0.next
  let c1 := c1start.addDouble (wordProduct a.w0 a.w1)
  let c2start : ProductColumn := c1.next
  let p2start := c0start.addDouble (wordProduct a.w0 a.w2)
  let p2 := p2start.add (wordProduct a.w1 a.w1)
  let c2 := c2start.addColumn p2
  let c3start := c2.next
  let p3start := c0start.addDouble (wordProduct a.w0 a.w3)
  let p3 := p3start.addDouble (wordProduct a.w1 a.w2)
  let c3 := c3start.addColumn p3
  let c4start := c3.next
  let p4start := c0start.addDouble (wordProduct a.w1 a.w3)
  let p4 := p4start.add (wordProduct a.w2 a.w2)
  let c4 := c4start.addColumn p4
  let c5start : ProductColumn := c4.next
  let c5 := c5start.addDouble (wordProduct a.w2 a.w3)
  let c6start : ProductColumn := c5.next
  let c6 := c6start.add (wordProduct a.w3 a.w3)
  let n0 := a.w0.toNat
  let n1 := a.w1.toNat
  let n2 := a.w2.toNat
  let n3 := a.w3.toNat
  have nextBound (c : ProductColumn) : c.next.hi.toNat < 16 := by
    change (0 : UInt64).toNat < 16
    decide
  have hc0 : c0.val = n0*n0 := by
    have h := (ProductColumn.product_spec c0start a.w0 a.w0 (by decide)).1
    have hz : c0start.val = 0 := rfl
    change c0.val = c0start.val + n0*n0 at h
    rw [hz, Nat.zero_add] at h
    exact h
  have hc1 : c1.val = c1start.val + n0*n1 + n0*n1 :=
    (ProductColumn.double_spec c1start a.w0 a.w1 (nextBound c0)).1
  have doubleFromZero (x y : UInt64) :
      (c0start.addDouble (wordProduct x y)).val = 2*(x.toNat*y.toNat) ∧
        (c0start.addDouble (wordProduct x y)).hi.toNat ≤ 4 := by
    have h := ProductColumn.double_spec c0start x y (by decide)
    have hz : c0start.val = 0 := rfl
    change _ = c0start.val + x.toNat*y.toNat + x.toNat*y.toNat ∧ _ ≤ 4 at h
    simpa only [hz, Nat.zero_add, Nat.two_mul] using h
  have hc2 : c2.val = c2start.val + 2*(n0*n2) + n1*n1 := by
    obtain ⟨h, hb⟩ := doubleFromZero a.w0 a.w2
    change p2start.hi.toNat ≤ 4 at hb
    have h' : p2start.hi.toNat < 16 := Nat.lt_of_le_of_lt hb (by decide)
    obtain ⟨hvalue, hbound⟩ := ProductColumn.product_spec p2start a.w1 a.w1 h'
    change p2.hi.toNat ≤ p2start.hi.toNat + 2 at hbound
    have hm : c2.val = c2start.val + p2.val :=
      ProductColumn.addColumn_spec c2start p2 (nextBound c1) (by omega)
    change p2start.val = 2*(n0*n2) at h
    change p2.val = p2start.val + n1*n1 at hvalue
    omega
  have hc3 : c3.val = c3start.val + 2*(n0*n3) + 2*(n1*n2) := by
    obtain ⟨h, hb⟩ := doubleFromZero a.w0 a.w3
    change p3start.hi.toNat ≤ 4 at hb
    have h' : p3start.hi.toNat < 16 := Nat.lt_of_le_of_lt hb (by decide)
    obtain ⟨hvalue, hbound⟩ := ProductColumn.double_spec p3start a.w1 a.w2 h'
    change p3.hi.toNat ≤ p3start.hi.toNat + 4 at hbound
    have hm : c3.val = c3start.val + p3.val :=
      ProductColumn.addColumn_spec c3start p3 (nextBound c2) (by omega)
    change p3start.val = 2*(n0*n3) at h
    change p3.val = p3start.val + n1*n2 + n1*n2 at hvalue
    omega
  have hc4 : c4.val = c4start.val + 2*(n1*n3) + n2*n2 := by
    obtain ⟨h, hb⟩ := doubleFromZero a.w1 a.w3
    change p4start.hi.toNat ≤ 4 at hb
    have h' : p4start.hi.toNat < 16 := Nat.lt_of_le_of_lt hb (by decide)
    obtain ⟨hvalue, hbound⟩ := ProductColumn.product_spec p4start a.w2 a.w2 h'
    change p4.hi.toNat ≤ p4start.hi.toNat + 2 at hbound
    have hm : c4.val = c4start.val + p4.val :=
      ProductColumn.addColumn_spec c4start p4 (nextBound c3) (by omega)
    change p4start.val = 2*(n1*n3) at h
    change p4.val = p4start.val + n2*n2 at hvalue
    omega
  have hc5 : c5.val = c5start.val + n2*n3 + n2*n3 :=
    (ProductColumn.double_spec c5start a.w2 a.w3 (nextBound c4)).1
  have hc6 : c6.val = c6start.val + n3*n3 :=
    (ProductColumn.product_spec c6start a.w3 a.w3 (nextBound c5)).1
  have hn0 : c0.val = c0.lo.toNat + wordRadix * c1start.val := c0.next_spec
  have hn1 : c1.val = c1.lo.toNat + wordRadix * c2start.val := c1.next_spec
  have hn2 : c2.val = c2.lo.toNat + wordRadix * c3start.val := c2.next_spec
  have hn3 : c3.val = c3.lo.toNat + wordRadix * c4start.val := c3.next_spec
  have hn4 : c4.val = c4.lo.toNat + wordRadix * c5start.val := c4.next_spec
  have hn5 : c5.val = c5.lo.toNat + wordRadix * c6start.val := c5.next_spec
  have hn6 : c6.val = c6.lo.toNat + wordRadix*c6.mid.toNat + wordRadix^2*c6.hi.toNat := rfl
  have hp : lowValue a * lowValue a = n0*n0 + wordRadix * (2*(n0*n1)) +
      wordRadix^2 * (2*(n0*n2) + n1*n1) + wordRadix^3 * (2*(n0*n3) + 2*(n1*n2)) +
      wordRadix^4 * (2*(n1*n3) + n2*n2) + wordRadix^5 * (2*(n2*n3)) +
      wordRadix^6 * (n3*n3) := by
    change (n0 + wordRadix*n1 + wordRadix^2*n2 + wordRadix^3*n3) *
      (n0 + wordRadix*n1 + wordRadix^2*n2 + wordRadix^3*n3) = _
    generalize wordRadix = radix
    simp only [Nat.two_mul, Nat.mul_add, Nat.add_mul, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    ac_rfl
  have hprod : lowValue a * lowValue a < wordRadix^8 := by
    have h := Nat.mul_lt_mul'' (lowValue_lt a) (lowValue_lt a)
    exact h
  change lowValue ⟨c0.lo, c1.lo, c2.lo, c3.lo, 0⟩ +
    wordRadix^4 * lowValue ⟨c4.lo, c5.lo, c6.lo, c6.mid, 0⟩ =
      lowValue a * lowValue a
  rw [hp] at hprod ⊢
  simp only [lowValue, Nat.mul_add, wordRadix] at *
  omega

theorem squareColumns_bound (a : Words64) (ha : lowValue a < Fp.modulus) :
    lowValue (squareColumns a).1 + wordRadix^4 * lowValue (squareColumns a).2 <
      Fp.modulus^2 := by
  rw [squareColumns_spec]
  exact Nat.mul_lt_mul'' ha ha

/-- The inverse of the complement modulo two words, stored as a pair. -/
@[noinline] def inverseComplementPair : Pair := ⟨inverseComplement, 0xbcb223fedc24a059⟩

/-- The high word of a two-word quotient multiplied by the complement.

The canceled input word records whether the carry into that word overflowed.
-/
@[inline] def redQuotientHigh (q x : UInt64) : UInt64 :=
  let p := wordProduct q cancellationConstants.factor
  p.hi + yes (x < p.lo)

/-- Add the quotient to the high product words and subtract the carry from cancellation. -/
@[inline] def redQuotientFinish (low high : Words64) (q0 q1 q2 q3 d : UInt64) : Words64 :=
  let s0 := mac 1 high.w0 q0 0
  let s1 := mac 1 high.w1 q1 s0.hi
  let s2 := mac 1 high.w2 q2 s1.hi
  let s3 := mac 1 high.w3 q3 s2.hi
  if s0.lo ≥ d then ⟨s0.lo - d, s1.lo, s2.lo, s3.lo, s3.hi⟩
  else reduceWideProduct low high

/-- Compute two words of quotient by multiplying by the inverse of the complement. -/
@[inline] def inverseQuotientPair (x y : UInt64) : Pair :=
  let i := inverseComplementPair
  let p := wordProduct x i.lo
  ⟨p.lo, x * i.hi + y * i.lo + p.hi⟩

/-- Cancel two low words at a time.

Use the one-word reduction when subtracting a carry would borrow from the next word.
-/
@[inline] def reduceWideInverse (low high : Words64) : Words64 :=
  let q01 := inverseQuotientPair low.w0 low.w1
  let d := redQuotientHigh q01.hi low.w1
  if low.w2 ≥ d then
    let q23 := inverseQuotientPair (low.w2 - d) low.w3
    let highCarry := redQuotientHigh q23.hi low.w3
    redQuotientFinish low high q01.lo q01.hi q23.lo q23.hi highCarry
  else reduceWideProduct low high

private def pairValue (q : Pair) : Nat := q.lo.toNat + wordRadix * q.hi.toNat

private theorem pairValue_lt (q : Pair) : pairValue q < wordRadix^2 := by
  have h0 := q.lo.toNat_lt
  have h1 := q.hi.toNat_lt
  simp only [pairValue, wordRadix]
  omega

private theorem pair_product_remainder (r lo h a b v : Nat) (hlo : lo < r) :
    lo + r * ((a + b + h) % r) =
      (lo + r*h + r*(a+b) + r^2*v) % r^2 := by
  have e : lo + r*h + r*(a+b) + r^2*v = lo + r*(a+b+h) + r^2*v := by
    simp only [Nat.mul_add]
    ac_rfl
  rw [e, Nat.add_mul_mod_self_left]
  have e' : lo + r*(a+b+h) =
      (lo + r*((a+b+h)%r)) + r^2*((a+b+h)/r) := by
    conv => lhs; rw [← Nat.mod_add_div (a+b+h) r]
    rw [Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, ← Nat.pow_two]
  rw [e', Nat.add_mul_mod_self_left]
  symm
  apply Nat.mod_eq_of_lt
  have hr : 0 < r := Nat.zero_lt_of_lt hlo
  calc
    _ < r + r*((a+b+h)%r) := Nat.add_lt_add_right hlo _
    _ = r * (((a+b+h)%r)+1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    _ ≤ r*r := Nat.mul_le_mul_left r (Nat.mod_lt _ hr)
    _ = r^2 := (Nat.pow_two _).symm

private theorem pair_product_expansion (r x y a b : Nat) :
    (x + r*y) * (a + r*b) = x*a + r*(x*b+y*a) + r^2*(y*b) := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.pow_two]
  ac_rfl

private theorem inversePair_model (x y i0 i1 : UInt64) :
    let p := wordProduct x i0
    let q : Pair := ⟨p.lo, x*i1 + y*i0 + p.hi⟩
    pairValue q = (pairValue ⟨x, y⟩ * pairValue ⟨i0, i1⟩) % wordRadix^2 := by
  let p := wordProduct x i0
  let a := x.toNat*i1.toNat
  let b := y.toNat*i0.toNat
  let v := y.toNat*i1.toNat
  have hword : (x*i1 + y*i0 + p.hi).toNat = (a+b+p.hi.toNat) % wordRadix := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, Nat.mod_add_mod, Nat.add_mod_mod,
      a, b, wordRadix]
  have hp : p.lo.toNat + wordRadix*p.hi.toNat = x.toNat*i0.toNat := wordProduct_value x i0
  change p.lo.toNat + wordRadix*(x*i1 + y*i0 + p.hi).toNat = _
  rw [hword]
  exact (pair_product_remainder wordRadix p.lo.toNat p.hi.toNat a b v p.lo.toNat_lt).trans
    (congrArg (fun n => n % wordRadix^2)
      ((congrArg (fun n => n + wordRadix*(a+b) + wordRadix^2*v) hp).trans
        (pair_product_expansion wordRadix x.toNat y.toNat i0.toNat i1.toNat).symm))

private theorem inverseComplementPair_mod :
    (pairValue ⟨inverseComplementPair.lo, inverseComplementPair.hi⟩ * complement.toNat) %
      wordRadix^2 = 1 := by
  decide

private theorem inverseQuotientPair_mod (x y : UInt64) :
    pairValue (inverseQuotientPair x y) * complement.toNat % wordRadix^2 =
      pairValue ⟨x, y⟩ := by
  let m := wordRadix^2
  let u := pairValue ⟨x, y⟩
  let q := pairValue ⟨inverseComplementPair.lo, inverseComplementPair.hi⟩
  let c := complement.toNat
  have hq : pairValue (inverseQuotientPair x y) = (u*q) % m :=
    inversePair_model x y inverseComplementPair.lo inverseComplementPair.hi
  calc
    _ = ((u * q) * c) % m := by rw [hq, Nat.mod_mul_mod]
    _ = (u * ((q * c) % m)) % m := by rw [Nat.mul_assoc, Nat.mul_mod_mod]
    _ = u := by
      have hi : (q*c)%m = 1 := inverseComplementPair_mod
      rw [hi, Nat.mul_one, Nat.mod_eq_of_lt (pairValue_lt ⟨x,y⟩)]

private theorem redQuotientHigh_spec (q : Pair) (x y : UInt64)
    (hq : pairValue q * complement.toNat % wordRadix^2 = pairValue ⟨x,y⟩) :
    pairValue q * complement.toNat = pairValue ⟨x,y⟩ +
      wordRadix^2 * (redQuotientHigh q.hi y).toNat := by
  let p := wordProduct q.hi complement
  let n := q.lo.toNat * complement.toNat
  let b := yes (y < p.lo)
  have hw : p.lo.toNat + wordRadix*p.hi.toNat = q.hi.toNat * complement.toNat :=
    wordProduct_value q.hi complement
  have hk : n / wordRadix < complement.toNat := by
    apply Nat.div_lt_of_lt_mul
    exact Nat.mul_lt_mul_of_pos_right q.lo.toNat_lt (by decide)
  have hn := Nat.mod_add_div n wordRadix
  have hp0 := p.lo.toNat_lt
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hmodel :
      pairValue q * complement.toNat = n + wordRadix*(p.lo.toNat + wordRadix*p.hi.toNat) := by
    rw [hw]
    simp only [pairValue, Nat.add_mul, Nat.mul_assoc, n]
  rw [hmodel] at hq
  have hm : (n / wordRadix + p.lo.toNat) % wordRadix = y.toNat := by
    simp only [pairValue, wordRadix] at hq hn ⊢
    omega
  have hsmall : n / wordRadix + p.lo.toNat = y.toNat + wordRadix * b.toNat := by
    have hc : complement.toNat = 4294968273 := by decide
    rw [hc] at hk
    by_cases h : y < p.lo
    · have hlt : y.toNat < p.lo.toNat := h
      have hb : b = 1 := by simp [b, h, yes, Bool.toUInt64]
      rw [hb, UInt64.toNat_one, Nat.mul_one]
      simp only [wordRadix] at hm hk ⊢
      omega
    · have hle : p.lo.toNat ≤ y.toNat := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
      have hb : b = 0 := by simp [b, h, yes, Bool.toUInt64]
      rw [hb, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
      simp only [wordRadix] at hm hk ⊢
      omega
  have hhi : p.hi.toNat < complement.toNat := by
    rw [show p.hi.toNat = q.hi.toNat*complement.toNat / wordRadix from mulHigh_spec q.hi complement]
    apply Nat.div_lt_of_lt_mul
    exact Nat.mul_lt_mul_of_pos_right q.hi.toNat_lt (by decide)
  have hb : b.toNat ≤ 1 := by
    dsimp only [b]
    cases decide (y < p.lo) <;> decide
  have he : (p.hi + b).toNat = p.hi.toNat + b.toNat := by
    have hc : complement.toNat = 4294968273 := by decide
    exact add_exact (by omega)
  change _ = _ + wordRadix^2 * (p.hi + b).toNat
  rw [hmodel, he]
  simp only [pairValue, wordRadix] at hq hsmall hn ⊢
  omega

private theorem redQuotientFinish_spec (low high : Words64) (q0 q1 q2 q3 d : UInt64)
    (hq : lowValue ⟨q0,q1,q2,q3,0⟩ * complement.toNat =
      lowValue low + wordRadix^4*d.toNat)
    (h : lowValue low + wordRadix^4 * lowValue high < Fp.modulus^2) :
    value (redQuotientFinish low high q0 q1 q2 q3 d) < 2 * Fp.modulus ∧
      (wordRadix^4 * value (redQuotientFinish low high q0 q1 q2 q3 d)) % Fp.modulus =
        (lowValue low + wordRadix^4 * lowValue high) % Fp.modulus := by
  let s0 := mac 1 high.w0 q0 0
  let s1 := mac 1 high.w1 q1 s0.hi
  let s2 := mac 1 high.w2 q2 s1.hi
  let s3 := mac 1 high.w3 q3 s2.hi
  let t : Words64 := ⟨s0.lo - d, s1.lo, s2.lo, s3.lo, s3.hi⟩
  let q : Words64 := ⟨q0,q1,q2,q3,0⟩
  have hv : lowValue q < wordRadix^4 := lowValue_lt q
  change value (if d ≤ s0.lo then t else reduceWideProduct low high) < 2 * Fp.modulus ∧
    (wordRadix^4 * value (if d ≤ s0.lo then t else reduceWideProduct low high)) % Fp.modulus = _
  split
  · rename_i hl
    have he0 := mac_spec 1 high.w0 q0 0
    have he1 := mac_spec 1 high.w1 q1 s0.hi
    have he2 := mac_spec 1 high.w2 q2 s1.hi
    have he3 := mac_spec 1 high.w3 q3 s2.hi
    change s0.lo.toNat + 2^64*s0.hi.toNat = 1*high.w0.toNat+q0.toNat+0 at he0
    change s1.lo.toNat + 2^64*s1.hi.toNat = 1*high.w1.toNat+q1.toNat+s0.hi.toNat at he1
    change s2.lo.toNat + 2^64*s2.hi.toNat = 1*high.w2.toNat+q2.toNat+s1.hi.toNat at he2
    change s3.lo.toNat + 2^64*s3.hi.toNat = 1*high.w3.toNat+q3.toNat+s2.hi.toNat at he3
    have hs : value t + d.toNat = lowValue high + lowValue q := by
      have hh := UInt64.toNat_sub_of_le s0.lo d hl
      have hln := UInt64.le_iff_toNat_le.mp hl
      simp only [t, q, value, lowValue, hh, wordRadix]
      omega
    have hfull : wordRadix^4*value t = lowValue low + wordRadix^4*lowValue high +
        lowValue q * Fp.modulus := by
      change lowValue q * complement.toNat = _ at hq
      simp only [wordRadix, Fp.modulus, show complement.toNat = 4294968273 by decide] at hq hs ⊢
      omega
    have hp := Nat.mul_le_mul_right Fp.modulus (Nat.le_of_lt hv)
    refine ⟨?_, by rw [hfull, Nat.add_mul_mod_self_right]⟩
    simp only [wordRadix, Fp.modulus] at h hfull hp ⊢
    omega
  · exact reduceWideProduct_spec low high h

private theorem fourValue_eq_pairs (q r : Pair) :
    lowValue ⟨q.lo,q.hi,r.lo,r.hi,0⟩ = pairValue q + wordRadix^2*pairValue r := by
  simp only [lowValue, pairValue, Nat.mul_add, wordRadix]
  omega

private theorem assemblePairCancellation (q01 q23 lo hi d carry : Nat) (hb : d ≤ hi)
    (h01 : q01 * complement.toNat = lo + wordRadix^2*d)
    (h23 : q23 * complement.toNat = hi - d + wordRadix^2*carry) :
    (q01 + wordRadix^2*q23) * complement.toNat = lo + wordRadix^2*hi + wordRadix^4*carry := by
  calc
    _ = lo + wordRadix^2*d + wordRadix^2*(hi-d+wordRadix^2*carry) := by
      rw [Nat.add_mul, Nat.mul_assoc, h01, h23]
    _ = lo + wordRadix^2*(d+(hi-d+wordRadix^2*carry)) := by
      rw [Nat.add_assoc, ← Nat.mul_add]
    _ = _ := by
      rw [← Nat.add_assoc d, Nat.add_sub_of_le hb, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add,
        ← Nat.add_assoc]

/-- Paired cancellation gives a bounded residue with the original Montgomery congruence. -/
theorem reduceWideInverse_spec (low high : Words64)
    (h : lowValue low + wordRadix^4 * lowValue high < Fp.modulus^2) :
    value (reduceWideInverse low high) < 2 * Fp.modulus ∧
      (wordRadix^4 * value (reduceWideInverse low high)) % Fp.modulus =
        (lowValue low + wordRadix^4 * lowValue high) % Fp.modulus := by
  let q01 := inverseQuotientPair low.w0 low.w1
  let d := redQuotientHigh q01.hi low.w1
  let l2 := low.w2 - d
  let q23 := inverseQuotientPair l2 low.w3
  let highCarry := redQuotientHigh q23.hi low.w3
  have h01 : pairValue q01 * complement.toNat = pairValue ⟨low.w0,low.w1⟩ + wordRadix^2*d.toNat :=
    redQuotientHigh_spec q01 low.w0 low.w1 (inverseQuotientPair_mod low.w0 low.w1)
  have h23 : pairValue q23 * complement.toNat = pairValue ⟨l2,low.w3⟩ +
      wordRadix^2*highCarry.toNat :=
    redQuotientHigh_spec q23 l2 low.w3 (inverseQuotientPair_mod l2 low.w3)
  let t := redQuotientFinish low high q01.lo q01.hi q23.lo q23.hi highCarry
  change value (if d ≤ low.w2 then t else reduceWideProduct low high) < _ ∧
    (_ * value (if d ≤ low.w2 then t else reduceWideProduct low high)) % _ = _
  split
  · rename_i hl
    apply redQuotientFinish_spec _ _ _ _ _ _ _ _ h
    have hl2 : l2.toNat = low.w2.toNat - d.toNat := UInt64.toNat_sub_of_le low.w2 d hl
    have hln := UInt64.le_iff_toNat_le.mp hl
    let lowPair : Pair := ⟨low.w0,low.w1⟩
    let highPair : Pair := ⟨low.w2,low.w3⟩
    have hpair : pairValue ⟨l2,low.w3⟩ = pairValue highPair - d.toNat := by
      simp only [pairValue, highPair, hl2]
      omega
    rw [hpair] at h23
    have hb : d.toNat ≤ pairValue highPair := by
      change d.toNat ≤ low.w2.toNat + wordRadix * low.w3.toNat
      omega
    have hlow : lowValue low = pairValue lowPair + wordRadix^2*pairValue highPair :=
      fourValue_eq_pairs lowPair highPair
    rw [fourValue_eq_pairs q01 q23, hlow]
    exact assemblePairCancellation _ _ _ _ _ _ hb h01 h23
  · exact reduceWideProduct_spec low high h

/-- Scan the wide product one column at a time.

Sum the three middle columns independently. -/
@[inline] def multiplyColumns (a b : Words64) : Words64 × Words64 :=
  let zero : ProductColumn := ⟨0, 0, 0⟩
  let p2 := (zero.add (wordProduct a.w0 b.w2)).add (wordProduct a.w1 b.w1)
    |>.add (wordProduct a.w2 b.w0)
  let p3 := (zero.add (wordProduct a.w0 b.w3)).add (wordProduct a.w1 b.w2)
    |>.add (wordProduct a.w2 b.w1)
    |>.add (wordProduct a.w3 b.w0)
  let p4 := (zero.add (wordProduct a.w1 b.w3)).add (wordProduct a.w2 b.w2)
    |>.add (wordProduct a.w3 b.w1)
  let c0 := zero.add (wordProduct a.w0 b.w0)
  let c1 := (c0.next.add (wordProduct a.w0 b.w1)).add (wordProduct a.w1 b.w0)
  let c2 := c1.next.addColumn p2
  let c3 := c2.next.addColumn p3
  let c4 := c3.next.addColumn p4
  let c5 := (c4.next.add (wordProduct a.w2 b.w3)).add (wordProduct a.w3 b.w2)
  let c6 := c5.next.add (wordProduct a.w3 b.w3)
  (⟨c0.lo, c1.lo, c2.lo, c3.lo, 0⟩, ⟨c4.lo, c5.lo, c6.lo, c6.mid, 0⟩)

private theorem multiplyColumns_spec (a b : Words64) :
    lowValue (multiplyColumns a b).1 + wordRadix^4 * lowValue (multiplyColumns a b).2 =
      lowValue a * lowValue b := by
  let zero : ProductColumn := ⟨0, 0, 0⟩
  have hz : zero.val = 0 := rfl
  have hh : zero.hi.toNat = 0 := rfl
  have nextBound (c : ProductColumn) : c.next.hi.toNat < 16 := by
    change (0 : UInt64).toNat < 16
    decide
  let b0 := zero
  have hb0 : b0.hi.toNat = 0 := rfl
  let c0 := b0.add (wordProduct a.w0 b.w0)
  obtain ⟨hv0_0, hh0_0⟩ :=
    ProductColumn.product_spec b0 a.w0 b.w0 (by omega)
  change c0.val = b0.val + a.w0.toNat*b.w0.toNat at hv0_0
  change c0.hi.toNat ≤ b0.hi.toNat + 2 at hh0_0
  have hc0 : c0.val = b0.val + (a.w0.toNat*b.w0.toNat) := by omega
  let b1 := c0.next
  have hb1 : b1.hi.toNat = 0 := rfl
  let p1_0 := b1.add (wordProduct a.w0 b.w1)
  obtain ⟨hv1_0, hh1_0⟩ :=
    ProductColumn.product_spec b1 a.w0 b.w1 (nextBound c0)
  change p1_0.val = b1.val + a.w0.toNat*b.w1.toNat at hv1_0
  change p1_0.hi.toNat ≤ b1.hi.toNat + 2 at hh1_0
  let c1 := p1_0.add (wordProduct a.w1 b.w0)
  obtain ⟨hv1_1, hh1_1⟩ :=
    ProductColumn.product_spec p1_0 a.w1 b.w0 (by omega)
  change c1.val = p1_0.val + a.w1.toNat*b.w0.toNat at hv1_1
  change c1.hi.toNat ≤ p1_0.hi.toNat + 2 at hh1_1
  have hc1 : c1.val = b1.val + (a.w0.toNat*b.w1.toNat + a.w1.toNat*b.w0.toNat) := by omega
  let b2 := c1.next
  have hb2 : b2.hi.toNat = 0 := rfl
  let p2_0 := zero.add (wordProduct a.w0 b.w2)
  obtain ⟨hv2_0, hh2_0⟩ :=
    ProductColumn.product_spec zero a.w0 b.w2 (by omega)
  change p2_0.val = zero.val + a.w0.toNat*b.w2.toNat at hv2_0
  change p2_0.hi.toNat ≤ zero.hi.toNat + 2 at hh2_0
  let p2_1 := p2_0.add (wordProduct a.w1 b.w1)
  obtain ⟨hv2_1, hh2_1⟩ :=
    ProductColumn.product_spec p2_0 a.w1 b.w1 (by omega)
  change p2_1.val = p2_0.val + a.w1.toNat*b.w1.toNat at hv2_1
  change p2_1.hi.toNat ≤ p2_0.hi.toNat + 2 at hh2_1
  let p2 := p2_1.add (wordProduct a.w2 b.w0)
  obtain ⟨hv2_2, hh2_2⟩ :=
    ProductColumn.product_spec p2_1 a.w2 b.w0 (by omega)
  change p2.val = p2_1.val + a.w2.toNat*b.w0.toNat at hv2_2
  change p2.hi.toNat ≤ p2_1.hi.toNat + 2 at hh2_2
  let c2 := b2.addColumn p2
  have hm2 := ProductColumn.addColumn_spec b2 p2 (nextBound c1) (by omega)
  change c2.val = b2.val + p2.val at hm2
  have hc2 : c2.val = b2.val + (a.w0.toNat*b.w2.toNat + a.w1.toNat*b.w1.toNat +
      a.w2.toNat*b.w0.toNat) := by omega
  let b3 := c2.next
  have hb3 : b3.hi.toNat = 0 := rfl
  let p3_0 := zero.add (wordProduct a.w0 b.w3)
  obtain ⟨hv3_0, hh3_0⟩ :=
    ProductColumn.product_spec zero a.w0 b.w3 (by omega)
  change p3_0.val = zero.val + a.w0.toNat*b.w3.toNat at hv3_0
  change p3_0.hi.toNat ≤ zero.hi.toNat + 2 at hh3_0
  let p3_1 := p3_0.add (wordProduct a.w1 b.w2)
  obtain ⟨hv3_1, hh3_1⟩ :=
    ProductColumn.product_spec p3_0 a.w1 b.w2 (by omega)
  change p3_1.val = p3_0.val + a.w1.toNat*b.w2.toNat at hv3_1
  change p3_1.hi.toNat ≤ p3_0.hi.toNat + 2 at hh3_1
  let p3_2 := p3_1.add (wordProduct a.w2 b.w1)
  obtain ⟨hv3_2, hh3_2⟩ :=
    ProductColumn.product_spec p3_1 a.w2 b.w1 (by omega)
  change p3_2.val = p3_1.val + a.w2.toNat*b.w1.toNat at hv3_2
  change p3_2.hi.toNat ≤ p3_1.hi.toNat + 2 at hh3_2
  let p3 := p3_2.add (wordProduct a.w3 b.w0)
  obtain ⟨hv3_3, hh3_3⟩ :=
    ProductColumn.product_spec p3_2 a.w3 b.w0 (by omega)
  change p3.val = p3_2.val + a.w3.toNat*b.w0.toNat at hv3_3
  change p3.hi.toNat ≤ p3_2.hi.toNat + 2 at hh3_3
  let c3 := b3.addColumn p3
  have hm3 := ProductColumn.addColumn_spec b3 p3 (nextBound c2) (by omega)
  change c3.val = b3.val + p3.val at hm3
  have hc3 : c3.val = b3.val + (a.w0.toNat*b.w3.toNat + a.w1.toNat*b.w2.toNat +
      a.w2.toNat*b.w1.toNat + a.w3.toNat*b.w0.toNat) := by omega
  let b4 := c3.next
  have hb4 : b4.hi.toNat = 0 := rfl
  let p4_0 := zero.add (wordProduct a.w1 b.w3)
  obtain ⟨hv4_0, hh4_0⟩ :=
    ProductColumn.product_spec zero a.w1 b.w3 (by omega)
  change p4_0.val = zero.val + a.w1.toNat*b.w3.toNat at hv4_0
  change p4_0.hi.toNat ≤ zero.hi.toNat + 2 at hh4_0
  let p4_1 := p4_0.add (wordProduct a.w2 b.w2)
  obtain ⟨hv4_1, hh4_1⟩ :=
    ProductColumn.product_spec p4_0 a.w2 b.w2 (by omega)
  change p4_1.val = p4_0.val + a.w2.toNat*b.w2.toNat at hv4_1
  change p4_1.hi.toNat ≤ p4_0.hi.toNat + 2 at hh4_1
  let p4 := p4_1.add (wordProduct a.w3 b.w1)
  obtain ⟨hv4_2, hh4_2⟩ :=
    ProductColumn.product_spec p4_1 a.w3 b.w1 (by omega)
  change p4.val = p4_1.val + a.w3.toNat*b.w1.toNat at hv4_2
  change p4.hi.toNat ≤ p4_1.hi.toNat + 2 at hh4_2
  let c4 := b4.addColumn p4
  have hm4 := ProductColumn.addColumn_spec b4 p4 (nextBound c3) (by omega)
  change c4.val = b4.val + p4.val at hm4
  have hc4 : c4.val = b4.val + (a.w1.toNat*b.w3.toNat + a.w2.toNat*b.w2.toNat +
      a.w3.toNat*b.w1.toNat) := by omega
  let b5 := c4.next
  have hb5 : b5.hi.toNat = 0 := rfl
  let p5_0 := b5.add (wordProduct a.w2 b.w3)
  obtain ⟨hv5_0, hh5_0⟩ :=
    ProductColumn.product_spec b5 a.w2 b.w3 (nextBound c4)
  change p5_0.val = b5.val + a.w2.toNat*b.w3.toNat at hv5_0
  change p5_0.hi.toNat ≤ b5.hi.toNat + 2 at hh5_0
  let c5 := p5_0.add (wordProduct a.w3 b.w2)
  obtain ⟨hv5_1, hh5_1⟩ :=
    ProductColumn.product_spec p5_0 a.w3 b.w2 (by omega)
  change c5.val = p5_0.val + a.w3.toNat*b.w2.toNat at hv5_1
  change c5.hi.toNat ≤ p5_0.hi.toNat + 2 at hh5_1
  have hc5 : c5.val = b5.val + (a.w2.toNat*b.w3.toNat + a.w3.toNat*b.w2.toNat) := by omega
  let b6 := c5.next
  have hb6 : b6.hi.toNat = 0 := rfl
  let c6 := b6.add (wordProduct a.w3 b.w3)
  obtain ⟨hv6_0, hh6_0⟩ :=
    ProductColumn.product_spec b6 a.w3 b.w3 (nextBound c5)
  change c6.val = b6.val + a.w3.toNat*b.w3.toNat at hv6_0
  change c6.hi.toNat ≤ b6.hi.toNat + 2 at hh6_0
  have hc6 : c6.val = b6.val + (a.w3.toNat*b.w3.toNat) := by omega
  have hn0 : c0.val = c0.lo.toNat + wordRadix*b1.val := c0.next_spec
  have hn1 : c1.val = c1.lo.toNat + wordRadix*b2.val := c1.next_spec
  have hn2 : c2.val = c2.lo.toNat + wordRadix*b3.val := c2.next_spec
  have hn3 : c3.val = c3.lo.toNat + wordRadix*b4.val := c3.next_spec
  have hn4 : c4.val = c4.lo.toNat + wordRadix*b5.val := c4.next_spec
  have hn5 : c5.val = c5.lo.toNat + wordRadix*b6.val := c5.next_spec
  have hb0 : b0.val = 0 := hz
  have hn6 : c6.val = c6.lo.toNat + wordRadix*c6.mid.toNat + wordRadix^2*c6.hi.toNat := rfl
  have hp : lowValue a * lowValue b =
      a.w0.toNat*b.w0.toNat +
      wordRadix^1 * (a.w0.toNat*b.w1.toNat + a.w1.toNat*b.w0.toNat) +
      wordRadix^2 * (a.w0.toNat*b.w2.toNat + a.w1.toNat*b.w1.toNat + a.w2.toNat*b.w0.toNat) +
      wordRadix^3 * (a.w0.toNat*b.w3.toNat + a.w1.toNat*b.w2.toNat +
        a.w2.toNat*b.w1.toNat + a.w3.toNat*b.w0.toNat) +
      wordRadix^4 * (a.w1.toNat*b.w3.toNat + a.w2.toNat*b.w2.toNat + a.w3.toNat*b.w1.toNat) +
      wordRadix^5 * (a.w2.toNat*b.w3.toNat + a.w3.toNat*b.w2.toNat) +
      wordRadix^6 * (a.w3.toNat*b.w3.toNat) := by
    unfold lowValue
    generalize wordRadix = radix
    simp only [Nat.mul_add, Nat.add_mul, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    ac_rfl
  have hprod : lowValue a * lowValue b < wordRadix^8 := by
    have h := Nat.mul_lt_mul'' (lowValue_lt a) (lowValue_lt b)
    exact h
  change lowValue ⟨c0.lo, c1.lo, c2.lo, c3.lo, 0⟩ +
    wordRadix^4 * lowValue ⟨c4.lo, c5.lo, c6.lo, c6.mid, 0⟩ =
      lowValue a * lowValue b
  rw [hp] at hprod ⊢
  simp only [lowValue, Nat.mul_add, wordRadix] at *
  omega

theorem multiplyColumns_bound (a b : Words64) (ha : lowValue a < Fp.modulus)
    (hb : lowValue b < Fp.modulus) :
    lowValue (multiplyColumns a b).1 + wordRadix^4 * lowValue (multiplyColumns a b).2 <
      Fp.modulus^2 := by
  rw [multiplyColumns_spec]
  exact Nat.mul_lt_mul'' ha hb

/-- The Montgomery product on four 64-bit words. -/
@[inline] def mul (a b : @& Montgomery) : Montgomery :=
  let w := multiplyColumns a.raw.words b.raw.words
  let h := reduceWideInverse_spec w.1 w.2 (multiplyColumns_bound a.raw.words b.raw.words a.lt b.lt)
  finish (reduceWideInverse w.1 w.2) h.1

instance : Mul Montgomery := ⟨mul⟩

/-- Square a Montgomery residue using one product for each pair of words. -/
@[inline] def square (a : @& Montgomery) : Montgomery :=
  let w := squareColumns a.raw.words
  let h := reduceWideInverse_spec w.1 w.2 (squareColumns_bound a.raw.words a.lt)
  finish (reduceWideInverse w.1 w.2) h.1


/-- Read the low 256 bits in four words. -/
@[inline] def rawOfNat (n : Nat) : Raw :=
  ⟨n.toUInt64, (n >>> 64).toUInt64, (n >>> 128).toUInt64, (n >>> 192).toUInt64⟩

private theorem rawOfNat_val (n : Nat) (hn : n < 2^256) : (rawOfNat n).val = n := by
  simp only [rawOfNat, Raw.val, Raw.words, lowValue, wordRadix,
    Nat.shiftRight_eq_div_pow]
  change n % 2^64 + 2^64 * ((n / 2^64) % 2^64) + 2^128 * ((n / 2^128) % 2^64) +
    2^192 * ((n / 2^192) % 2^64) = n
  omega

/-- Join the four words with shifts by 64 bits. -/
@[inline] def rawToNat (a : Raw) : Nat :=
  let high := (a.w3.toNat <<< 64) + a.w2.toNat
  let middle := (high <<< 64) + a.w1.toNat
  (middle <<< 64) + a.w0.toNat

theorem rawToNat_eq (a : Raw) : rawToNat a = a.val := by
  simp only [rawToNat, Nat.shiftLeft_eq, Raw.val, Raw.words, lowValue, wordRadix]
  omega

/-- Read the canonical integer before applying the Montgomery scale. -/
@[inline] def readRaw (a : Fp) : Montgomery :=
  ⟨rawOfNat a.val, by
    rw [rawOfNat_val _ (Nat.lt_trans a.isLt (by decide))]
    exact a.isLt⟩

/-- The raw integer `R^2 mod p`, where `R = 2^256`. -/
def montgomerySquare : Montgomery := ⟨⟨0x7a2000e90a1, 1, 0, 0⟩, by decide⟩

/-- The raw integer one used to remove the Montgomery scale. -/
def rawOne : Montgomery := ⟨⟨1, 0, 0, 0⟩, by decide⟩

/-- Enter the Montgomery representation with a product by the square of the radix. -/
@[inline] def ofFin (a : Fp) : Montgomery := montgomerySquare * readRaw a

/-- Leave the Montgomery representation with a product by the word one. -/
@[inline] def toFin (a : Montgomery) : Fp :=
  let x := a * rawOne
  ⟨rawToNat x.raw, by rw [rawToNat_eq]; exact x.lt⟩

/-- `a + b + carry`, and the carry out. -/
@[inline] def plus (a b carry : UInt64) : Pair :=
  let s := a+b
  let t := s+carry
  ⟨t, yes (s < a) + yes (t < s)⟩

/-- `a - b - borrow`, and the borrow out. -/
@[inline] def minus (a b borrow : UInt64) : Pair :=
  let s := a-b
  ⟨s-borrow, yes (a < b) + yes (s < borrow)⟩

private theorem yes_le_one (b : Bool) : (yes b).toNat ≤ 1 := by
  cases b <;> decide

private theorem yes_sum (a b : Bool) : (yes a + yes b).toNat = (yes a).toNat + (yes b).toNat := by
  cases a <;> cases b <;> decide

/-- An addition word and its carry give the integer sum. -/
theorem plus_spec (a b carry : UInt64) (hc : carry.toNat ≤ 1) :
    (plus a b carry).lo.toNat + wordRadix * (plus a b carry).hi.toNat =
      a.toNat + b.toNat + carry.toNat ∧ (plus a b carry).hi.toNat ≤ 1 := by
  have h0 := add_with_carry a b
  have h1 := add_with_carry (a + b) carry
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [plus, yes_sum, wordRadix] at h0 h1 ⊢
  omega

/-- A subtraction word plus the subtrahends equals the minuend and the borrow. -/
theorem minus_spec (a b borrow : UInt64) (hc : borrow.toNat ≤ 1) :
    (minus a b borrow).lo.toNat + b.toNat + borrow.toNat =
      a.toNat + wordRadix * (minus a b borrow).hi.toNat ∧ (minus a b borrow).hi.toNat ≤ 1 := by
  have h0 := sub_split a b
  have h1 := sub_split (a - b) borrow
  have hb := b.toNat_lt
  have hl := (a - b - borrow).toNat_lt
  simp only [minus, yes_sum, wordRadix] at h0 h1 ⊢
  omega

/-- The sum of two values of four words, then the given reduction of the five-word result. -/
@[inline] def add64 (reduce : Words64 → Words64) (a b : Words64) : Words64 :=
  let s0 := plus a.w0 b.w0 0
  let s1 := plus a.w1 b.w1 s0.hi
  let s2 := plus a.w2 b.w2 s1.hi
  let s3 := plus a.w3 b.w3 s2.hi
  reduce ⟨s0.lo,s1.lo,s2.lo,s3.lo,s3.hi⟩

/-- Addition of reduced words gives the sum mod p. -/
theorem add64_spec (reduce : Words64 → Words64)
    (reduce_spec : ∀ r : Words64, value r < 2 * Fp.modulus →
      (reduce r).top = 0 ∧ value (reduce r) = value r % Fp.modulus)
    (a b : Words64) (ha : a.top = 0) (hb : b.top = 0)
    (hpa : value a < Fp.modulus) (hpb : value b < Fp.modulus) :
    (add64 reduce a b).top = 0 ∧ value (add64 reduce a b) = (value a + value b) % Fp.modulus := by
  unfold add64
  let s0 := plus a.w0 b.w0 0
  let s1 := plus a.w1 b.w1 s0.hi
  let s2 := plus a.w2 b.w2 s1.hi
  let s3 := plus a.w3 b.w3 s2.hi
  have h0 := plus_spec a.w0 b.w0 0 (by decide)
  have h1 := plus_spec a.w1 b.w1 s0.hi h0.2
  have h2 := plus_spec a.w2 b.w2 s1.hi h1.2
  have h3 := plus_spec a.w3 b.w3 s2.hi h2.2
  let s := (⟨s0.lo,s1.lo,s2.lo,s3.lo,s3.hi⟩ : Words64)
  change (reduce s).top = 0 ∧ value (reduce s) = _
  have he : value s = value a + value b := by
    change s0.lo.toNat + wordRadix*s1.lo.toNat + wordRadix^2*s2.lo.toNat +
      wordRadix^3*s3.lo.toNat + wordRadix^4*s3.hi.toNat =
      value a + value b
    have h0e := h0.1
    have h1e := h1.1
    have h2e := h2.1
    have h3e := h3.1
    change s0.lo.toNat + wordRadix*s0.hi.toNat = _ at h0e
    change s1.lo.toNat + wordRadix*s1.hi.toNat = _ at h1e
    change s2.lo.toNat + wordRadix*s2.hi.toNat = _ at h2e
    change s3.lo.toNat + wordRadix*s3.hi.toNat = _ at h3e
    simp only [value, lowValue, ha, hb, UInt64.toNat_zero, Nat.mul_zero,
      Nat.add_zero, wordRadix] at *
    omega
  rw [← he]
  exact reduce_spec s (by rw [he]; omega)

private theorem yes_lt_one (w : UInt64) : yes (w < 1) = yes (w = 0) := by
  have hx : w < 1 ↔ w = 0 := by
    rw [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, UInt64.toNat_zero, UInt64.toNat_one]
    omega
  simp only [hx]

private theorem yes_lt_yes_zero (a b : UInt64) :
    yes (a < yes (b = 0)) = yes (a = 0) &&& yes (b = 0) := by
  by_cases h : b = 0
  · simp only [h, decide_true, yes, Bool.toUInt64, ite_true]
    by_cases h' : a = 0
    · simp [h']
    · have hlt : ¬ a < 1 := by
        intro hlt
        apply h'
        apply UInt64.toNat_inj.mp
        have hlt' : a.toNat < (1 : UInt64).toNat := hlt
        rw [UInt64.toNat_one] at hlt'
        exact Nat.lt_one_iff.mp hlt'
      simp [h', hlt]
  · simp [h, yes, Bool.toUInt64]

/-- Subtract the difference between the radix and p from a wrapped difference. -/
private def correctBorrow (w0 w1 w2 w3 : UInt64) : Words64 :=
  let t0 := w0 - complement
  let borrow := yes (w0 < complement)
  if borrow = 0 then ⟨t0,w1,w2,w3,0⟩
  else
    let t1 := w1 - 1
    let t2 := w2 - yes (w1 = 0)
    let t3 := w3 - (yes (w2 = 0) &&& yes (w1 = 0))
    ⟨t0,t1,t2,t3,0⟩

private theorem correctBorrow_value (w0 w1 w2 w3 : UInt64)
    (hl : complement.toNat ≤ value ⟨w0,w1,w2,w3,0⟩) :
    value (correctBorrow w0 w1 w2 w3) + complement.toNat = value ⟨w0,w1,w2,w3,0⟩ := by
  unfold correctBorrow
  dsimp only
  have e0 := sub_split w0 complement
  split
  · rename_i h
    simp only [h, value_mk_zero, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero, wordRadix] at e0 ⊢
    omega
  · rename_i h
    have hc : yes (w0 < complement) = 1 := by
      by_cases h' : w0 < complement
      · simp [yes, Bool.toUInt64, h']
      · exact absurd (by simp [yes, Bool.toUInt64, h']) h
    have e1 := sub_split w1 1
    have e2 := sub_split w2 (yes (w1 = 0))
    have e3 := sub_split w3 (yes (w2 = 0) &&& yes (w1 = 0))
    rw [hc] at e0
    rw [yes_lt_one] at e1
    rw [yes_lt_yes_zero] at e2
    have hOut := lowValue_lt ⟨w0-complement,w1-1,w2-yes (w1=0),w3-(yes (w2=0) &&& yes (w1=0)),0⟩
    simp only [lowValue, value_mk_zero, UInt64.toNat_one, Nat.mul_one, wordRadix]
      at hl hOut e0 e1 e2 e3 ⊢
    omega

/-- The subtraction that the masked one is proved against. -/
private def sub64 (a b : Words64) : Words64 :=
  let d0 := minus a.w0 b.w0 0
  let d1 := minus a.w1 b.w1 d0.hi
  let d2 := minus a.w2 b.w2 d1.hi
  let d3 := minus a.w3 b.w3 d2.hi
  if d3.hi = 0 then ⟨d0.lo,d1.lo,d2.lo,d3.lo,0⟩
  else correctBorrow d0.lo d1.lo d2.lo d3.lo

/-- Subtraction of reduced words gives the difference mod p. -/
private theorem sub64_spec (a b : Words64) (ha : a.top = 0) (hb : b.top = 0)
    (hpa : value a < Fp.modulus) (hpb : value b < Fp.modulus) :
    (sub64 a b).top = 0 ∧ value (sub64 a b) = (value a + Fp.modulus - value b) % Fp.modulus := by
  let d0 := minus a.w0 b.w0 0
  let d1 := minus a.w1 b.w1 d0.hi
  let d2 := minus a.w2 b.w2 d1.hi
  let d3 := minus a.w3 b.w3 d2.hi
  have h0 := minus_spec a.w0 b.w0 0 (by decide)
  have h1 := minus_spec a.w1 b.w1 d0.hi h0.2
  have h2 := minus_spec a.w2 b.w2 d1.hi h1.2
  have h3 := minus_spec a.w3 b.w3 d2.hi h2.2
  let d := (⟨d0.lo,d1.lo,d2.lo,d3.lo,0⟩ : Words64)
  have he : value d + value b = value a + 2^256 * d3.hi.toNat := by
    rw [show value d = _ from value_mk_zero d0.lo d1.lo d2.lo d3.lo]
    have h0e := h0.1
    have h1e := h1.1
    have h2e := h2.1
    have h3e := h3.1
    change d0.lo.toNat + b.w0.toNat + 0 = a.w0.toNat + wordRadix*d0.hi.toNat at h0e
    change d1.lo.toNat + b.w1.toNat + d0.hi.toNat = a.w1.toNat + wordRadix*d1.hi.toNat at h1e
    change d2.lo.toNat + b.w2.toNat + d1.hi.toNat = a.w2.toNat + wordRadix*d2.hi.toNat at h2e
    change d3.lo.toNat + b.w3.toNat + d2.hi.toNat = a.w3.toNat + wordRadix*d3.hi.toNat at h3e
    simp only [value, lowValue, ha, hb, UInt64.toNat_zero, Nat.mul_zero,
      Nat.add_zero, wordRadix] at *
    omega
  change (if d3.hi = 0 then d else correctBorrow d0.lo d1.lo d2.lo d3.lo).top = 0 ∧
    value (if d3.hi = 0 then d else correctBorrow d0.lo d1.lo d2.lo d3.lo) = _
  have hradix : Fp.modulus + complement.toNat = 2^256 := by decide
  have hbase : value d < 2^256 := by
    simpa only [value, show d.top = 0 from rfl, UInt64.toNat_zero, Nat.mul_zero,
      Nat.add_zero, wordRadix]
      using lowValue_lt d
  by_cases h : d3.hi = 0
  · rw [ite_eq_left h]
    refine ⟨rfl, ?_⟩
    rw [h, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at he
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [ite_eq_right h]
    have h1 : d3.hi.toNat = 1 := by
      have hl := h3.2
      have hn : d3.hi.toNat ≠ 0 := fun hx => h (UInt64.toNat_inj.mp hx)
      omega
    rw [h1, Nat.mul_one] at he
    have hcor := correctBorrow_value d0.lo d1.lo d2.lo d3.lo
      (by change complement.toNat ≤ value d; omega)
    change value (correctBorrow d0.lo d1.lo d2.lo d3.lo) + complement.toNat = value d at hcor
    have hzero : (correctBorrow d0.lo d1.lo d2.lo d3.lo).top = 0 := by
      unfold correctBorrow
      dsimp only
      split <;> rfl
    refine ⟨hzero, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega



/-- Apply the modular correction to the wrapped difference, according to its borrow. -/
@[inline] def correctMasked (w0 w1 w2 w3 borrow : UInt64) : Words64 :=
  let subtrahend := complement &&& ((0 : UInt64) - borrow)
  let t0 := w0 - subtrahend
  let b0 := yes (w0 < subtrahend)
  let t1 := w1 - b0
  let b1 := yes (w1 < b0)
  let t2 := w2 - b1
  let b2 := yes (w2 < b1)
  let t3 := w3 - b2
  ⟨t0,t1,t2,t3,0⟩

private theorem correctMasked_eq (w0 w1 w2 w3 borrow : UInt64) (hb : borrow.toNat ≤ 1) :
    correctMasked w0 w1 w2 w3 borrow =
      if borrow = 0 then ⟨w0,w1,w2,w3,0⟩ else correctBorrow w0 w1 w2 w3 := by
  have hbor : borrow = 0 ∨ borrow = 1 := by
    have h : borrow.toNat = 0 ∨ borrow.toNat = 1 := by omega
    rcases h with h | h
    · exact Or.inl (UInt64.toNat_inj.mp h)
    · exact Or.inr (UInt64.toNat_inj.mp h)
  rcases hbor with rfl | rfl
  · simp [correctMasked, yes, Bool.toUInt64]
  · unfold correctMasked correctBorrow
    dsimp only
    rw [show complement &&& ((0 : UInt64) - 1) = complement by decide,
      ite_eq_right (show (1 : UInt64) ≠ 0 by decide)]
    by_cases h : w0 < complement
    · have hb : yes (w0 < complement) = 1 := by simp [yes, Bool.toUInt64, h]
      rw [hb, ite_eq_right (show (1 : UInt64) ≠ 0 by decide), yes_lt_one, yes_lt_yes_zero]
    · simp [h, yes, Bool.toUInt64]

/-- Apply the correction with borrow propagation across the four words. -/
@[noinline] def correctCold (w0 w1 w2 w3 borrow : UInt64) : Words64 :=
  correctMasked w0 w1 w2 w3 borrow

/-- Correct only the low word when the subtraction cannot borrow. -/
@[inline] def correctFast (w0 w1 w2 w3 borrow : UInt64) : Words64 :=
  let subtrahend := complement &&& ((0 : UInt64) - borrow)
  if w0 ≥ subtrahend then ⟨w0 - subtrahend, w1, w2, w3, 0⟩
  else correctCold w0 w1 w2 w3 borrow

private theorem correctFast_eq_correctMasked (w0 w1 w2 w3 borrow : UInt64) :
    correctFast w0 w1 w2 w3 borrow = correctMasked w0 w1 w2 w3 borrow := by
  unfold correctFast
  dsimp only
  split
  · rename_i h
    unfold correctMasked
    dsimp only
    generalize h' : complement &&& ((0 : UInt64) - borrow) = adjustment at *
    have hn : ¬ w0 < adjustment := UInt64.not_lt.mpr h
    simp [hn, yes, Bool.toUInt64]
  · rfl

/-- A smaller minuend generates a borrow.

Equal words pass on the low bit of the incoming borrow.
-/
@[inline] def subtractBorrow (a b borrow : UInt64) : UInt64 :=
  yes (a < b) ||| (yes (a == b) &&& borrow)

private theorem subtractBorrow_eq (a b borrow : UInt64) (h : borrow.toNat ≤ 1) :
    subtractBorrow a b borrow = (minus a b borrow).hi := by
  have hbor : borrow = 0 ∨ borrow = 1 := by
    have hh : borrow.toNat = 0 ∨ borrow.toNat = 1 := by omega
    rcases hh with hh | hh
    · exact Or.inl (UInt64.toNat_inj.mp hh)
    · exact Or.inr (UInt64.toNat_inj.mp hh)
  rcases hbor with rfl | rfl
  · simp [subtractBorrow, minus, yes, Bool.toUInt64]
  · by_cases hab : a = b
    · subst b
      simp [subtractBorrow, minus, yes, Bool.toUInt64]
    · have hne : a - b ≠ 0 := by
        intro hzero
        have he := congrArg UInt64.toNat hzero
        rw [UInt64.toNat_sub, UInt64.toNat_zero] at he
        have hnat : a.toNat ≠ b.toNat := fun h => hab (UInt64.toNat_inj.mp h)
        have ha := a.toNat_lt
        have hb := b.toNat_lt
        omega
      simp only [minus, yes_lt_one]
      simp [subtractBorrow, hab, hne, yes, Bool.toUInt64]

/-- Subtract two reduced words and conditionally apply the correction. -/
@[inline] def subMasked (a b : Words64) : Words64 :=
  let s0 := a.w0 - b.w0
  let s1 := a.w1 - b.w1
  let s2 := a.w2 - b.w2
  let s3 := a.w3 - b.w3
  let c0 := yes (a.w0 < b.w0)
  let c1 := subtractBorrow a.w1 b.w1 c0
  let c2 := subtractBorrow a.w2 b.w2 c1
  let c3 := subtractBorrow a.w3 b.w3 c2
  correctFast s0 (s1 - c0) (s2 - c1) (s3 - c2) c3

/-- Both subtraction implementations give the same words for all inputs. -/
private theorem subMasked_eq_sub64 (a b : Words64) : subMasked a b = sub64 a b := by
  let d0 := minus a.w0 b.w0 0
  let d1 := minus a.w1 b.w1 d0.hi
  let d2 := minus a.w2 b.w2 d1.hi
  let d3 := minus a.w3 b.w3 d2.hi
  let c0 := yes (a.w0 < b.w0)
  let c1 := subtractBorrow a.w1 b.w1 c0
  let c2 := subtractBorrow a.w2 b.w2 c1
  let c3 := subtractBorrow a.w3 b.w3 c2
  have h0 : d0.hi.toNat ≤ 1 := (minus_spec a.w0 b.w0 0 (by decide)).2
  have h1 : d1.hi.toNat ≤ 1 := (minus_spec a.w1 b.w1 d0.hi h0).2
  have h2 : d2.hi.toNat ≤ 1 := (minus_spec a.w2 b.w2 d1.hi h1).2
  have h3 : d3.hi.toNat ≤ 1 := (minus_spec a.w3 b.w3 d2.hi h2).2
  have e0 : c0 = d0.hi := by simp [c0, d0, minus, yes, Bool.toUInt64]
  have e1 : c1 = d1.hi := by
    change subtractBorrow a.w1 b.w1 c0 = d1.hi
    rw [e0]
    exact subtractBorrow_eq a.w1 b.w1 d0.hi h0
  have e2 : c2 = d2.hi := by
    change subtractBorrow a.w2 b.w2 c1 = d2.hi
    rw [e1]
    exact subtractBorrow_eq a.w2 b.w2 d1.hi h1
  have e3 : c3 = d3.hi := by
    change subtractBorrow a.w3 b.w3 c2 = d3.hi
    rw [e2]
    exact subtractBorrow_eq a.w3 b.w3 d2.hi h2
  have e4 : a.w0 - b.w0 = d0.lo := by simp [d0, minus]
  change correctFast (a.w0 - b.w0) (a.w1 - b.w1 - c0) (a.w2 - b.w2 - c1)
    (a.w3 - b.w3 - c2) c3 =
      if d3.hi = 0 then ⟨d0.lo,d1.lo,d2.lo,d3.lo,0⟩ else correctBorrow d0.lo d1.lo d2.lo d3.lo
  rw [e4, e0, e1, e2, e3, correctFast_eq_correctMasked]
  exact correctMasked_eq _ _ _ _ _ h3



theorem subMasked_spec (a b : Words64) (ha : a.top = 0) (hb : b.top = 0)
    (hpa : value a < Fp.modulus) (hpb : value b < Fp.modulus) :
    (subMasked a b).top = 0 ∧
      value (subMasked a b) = (value a + Fp.modulus - value b) % Fp.modulus := by
  rw [subMasked_eq_sub64]
  exact sub64_spec a b ha hb hpa hpb

/-- Add two canonical residues. -/
@[inline] def add (a b : @& Montgomery) : Montgomery :=
  let u := add64 reduceFast a.raw.words b.raw.words
  have hu := add64_spec reduceFast reduceFast_spec a.raw.words b.raw.words rfl rfl
    (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
  ⟨Raw.fromWords u, by
    rw [Raw.fromWords_val u hu.1, hu.2]
    exact Nat.mod_lt _ (by decide)⟩

/-- Subtract two canonical residues. -/
@[inline] def sub (a b : @& Montgomery) : Montgomery :=
  let u := subMasked a.raw.words b.raw.words
  have hu := subMasked_spec a.raw.words b.raw.words rfl rfl
    (a.raw.val_eq ▸ a.lt) (b.raw.val_eq ▸ b.lt)
  ⟨Raw.fromWords u, by
    rw [Raw.fromWords_val u hu.1, hu.2]
    exact Nat.mod_lt _ (by decide)⟩

instance : Add Montgomery := ⟨add⟩
instance : Sub Montgomery := ⟨sub⟩

/-- The four low words. -/
@[inline] def Words64.rawWords (x : Words64) : Raw := Raw.fromWords x
/-- The integer of all five words. -/
abbrev Words64.val (x : Words64) : Nat := value x

private theorem raw_val_add (x : Raw) :
    x.val = x.w0.toNat + x.w1.toNat*wordRadix + x.w2.toNat*wordRadix^2 +
      x.w3.toNat*wordRadix^3 := by
  simp only [Raw.val, lowValue, Raw.words, Nat.mul_comm]

private theorem word_value_for_scale (w : Words64) :
    w.val = w.rawWords.val + w.top.toNat*2^256 := by
  change value w = w.rawWords.val + w.top.toNat*2^256
  have h : w.rawWords.val = lowValue w := rfl
  rw [h, value_as_nat, Nat.mul_comm w.top.toNat]
/-- The four words shifted left by `s` bits, with the bits shifted out in the carry word. -/
@[inline] def shift (s : UInt64) (w : Raw) : Words64 :=
  let d := 64 - s
  ⟨w.w0 <<< s,
    (w.w1 <<< s) ||| (w.w0 >>> d),
    (w.w2 <<< s) ||| (w.w1 >>> d),
    (w.w3 <<< s) ||| (w.w2 >>> d),
    w.w3 >>> d⟩

/-- One word added to four words, with the carry in the fifth. -/
@[inline] def addLow (w : Raw) (f : UInt64) : Words64 :=
  let t0 := w.w0 + f
  let t1 := w.w1 + yes (t0 < w.w0)
  let t2 := w.w2 + yes (t1 < w.w1)
  let t3 := w.w3 + yes (t2 < w.w2)
  ⟨t0, t1, t2, t3, yes (t3 < w.w3)⟩

/-- `2^s w`, with the carry word folded back by `2^256 = 2^32 + 977 mod p`. -/
@[inline] def scaleInput (s : UInt64) (w : Raw) : Words64 :=
  let shifted := shift s w
  addLow shifted.rawWords (shifted.top * complement)

private theorem read_lt (w : Raw) : w.val < (2^256) := by
  have hc0 := UInt64.toNat_lt_size w.w0
  have hc1 := UInt64.toNat_lt_size w.w1
  have hc2 := UInt64.toNat_lt_size w.w2
  have hc3 := UInt64.toNat_lt_size w.w3
  change w.w0.toNat < wordRadix at hc0
  change w.w1.toNat < wordRadix at hc1
  change w.w2.toNat < wordRadix at hc2
  change w.w3.toNat < wordRadix at hc3
  simp only [raw_val_add, wordRadix] at *
  omega

private theorem radix_split (s : UInt64) (hs : s.toNat ≤ 3) :
    wordRadix = 2^(64-s.toNat) * 2^s.toNat := by
  change 2^64 = _
  rw [← Nat.pow_add, Nat.sub_add_cancel (show s.toNat ≤ 64 by omega)]

private theorem shifted_right (s x : UInt64) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    (x >>> (64-s)).toNat = x.toNat / 2^(64-s.toNat) := by
  have hle : s ≤ 64 := UInt64.le_iff_toNat_le.mpr (by change s.toNat ≤ 64; omega)
  rw [UInt64.toNat_shiftRight, UInt64.toNat_sub_of_le _ _ hle]
  change x.toNat >>> ((64 - s.toNat) % 64) = _
  rw [Nat.mod_eq_of_lt (by omega : 64 - s.toNat < 64), Nat.shiftRight_eq_div_pow]

private theorem shifted_right_lt (s x : UInt64) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    (x >>> (64-s)).toNat < 2^s.toNat := by
  have hb : x.toNat < wordRadix := UInt64.toNat_lt_size x
  rw [shifted_right s x hpos hs]
  apply Nat.div_lt_of_lt_mul
  rw [← radix_split s hs]
  exact hb

private theorem addLow_val (w : Raw) (f : UInt64) :
    (addLow w f).val = w.val + f.toNat := by
  let t0 := w.w0 + f
  let t1 := w.w1 + yes (t0 < w.w0)
  let t2 := w.w2 + yes (t1 < w.w1)
  let t3 := w.w3 + yes (t2 < w.w2)
  have h0 := add_with_carry w.w0 f
  have h1 := add_with_carry w.w1 (yes (t0 < w.w0))
  have h2 := add_with_carry w.w2 (yes (t1 < w.w1))
  have h3 := add_with_carry w.w3 (yes (t2 < w.w2))
  rw [word_value_for_scale, raw_val_add (addLow w f).rawWords]
  change t0.toNat + t1.toNat * wordRadix + t2.toNat * wordRadix^2 + t3.toNat * wordRadix^3 +
    (yes (t3 < w.w3)).toNat * (2^256) = w.val + f.toNat
  rw [raw_val_add]
  change t0.toNat + wordRadix * (yes (t0 < w.w0)).toNat = w.w0.toNat + f.toNat at h0
  change t1.toNat + wordRadix * (yes (t1 < w.w1)).toNat =
    w.w1.toNat + (yes (t0 < w.w0)).toNat at h1
  change t2.toNat + wordRadix * (yes (t2 < w.w2)).toNat =
    w.w2.toNat + (yes (t1 < w.w1)).toNat at h2
  change t3.toNat + wordRadix * (yes (t3 < w.w3)).toNat =
    w.w3.toNat + (yes (t2 < w.w2)).toNat at h3
  simp only [wordRadix] at *
  omega

theorem scaleInput_lt (s : UInt64) (w : Raw) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    (scaleInput s w).val < 2 * Fp.modulus := by
  let shifted := shift s w
  have htop : shifted.top.toNat < 2^s.toNat := shifted_right_lt s w.w3 hpos hs
  have h8 : 2^s.toNat ≤ 8 := Nat.pow_le_pow_right (by decide) hs
  have hlow := read_lt shifted.rawWords
  change (addLow shifted.rawWords (shifted.top * complement)).val < 2 * Fp.modulus
  rw [addLow_val, UInt64.toNat_mul]
  change shifted.rawWords.val + shifted.top.toNat * 4294968273 % wordRadix < 2 * Fp.modulus
  have hmod := Nat.mod_le (shifted.top.toNat * 4294968273) wordRadix
  simp only [Fp.modulus] at *
  omega


/-- Multiplication by `2^s` for shifts of one, two or three bits. -/
@[inline] def scale (s : UInt64) (w : Montgomery) (hpos : 0 < s.toNat) (hs : s.toNat ≤ 3) :
    Montgomery :=
  let t := scaleInput s w.raw
  let u := reduceMasked t
  have hr := reduceMasked_spec t (scaleInput_lt s w.raw hpos hs)
  ⟨Raw.fromWords u, by
    rw [Raw.fromWords_val u hr.1, hr.2]
    exact Nat.mod_lt _ (by decide)⟩

/-- One word of a value shifted right by one bit.

It holds the high bits of `a`, with the low bit of `b` on top. -/
@[inline] def halfLane (a b : UInt64) : UInt64 := (a >>> 1) + (b <<< 63)

/-- Four words shifted right by one bit, with `t` as the bit above them. -/
@[inline] def shiftHalf (a b c d t : UInt64) : Raw :=
  ⟨halfLane a b, halfLane b c, halfLane c d, halfLane d t⟩

/-- Half of a residue mod `p`.

An odd residue gets `p` added first, so that the sum is even. -/
@[inline] def halveRaw (x : Raw) : Raw :=
  let bit := x.w0 &&& 1
  -- For an odd input, adding the modulus is a high bit minus the complement.
  let subtrahend := complement * bit
  let a := x.w0 - subtrahend
  if x.w0 ≥ subtrahend then shiftHalf a x.w1 x.w2 x.w3 bit
  else
    let b := x.w1 - 1
    let c := x.w2 - yes (x.w1 == 0)
    let d := x.w3 - yes (x.w1 == 0 && x.w2 == 0)
    let t := bit - yes (x.w1 == 0 && x.w2 == 0 && x.w3 == 0)
    shiftHalf a b c d t

private theorem halfLane_val (a b : UInt64) :
    (halfLane a b).toNat = a.toNat / 2 + (b.toNat % 2) * 2^63 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  rw [halfLane, UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
  change ((a.toNat >>> 1) + (b.toNat <<< 63) % 2^64) % 2^64 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

private theorem shiftHalf_val (a : Words64) (ht : a.top.toNat ≤ 1) :
    (shiftHalf a.w0 a.w1 a.w2 a.w3 a.top).val = a.val / 2 := by
  simp only [shiftHalf, Raw.val, Raw.words, value, lowValue, halfLane_val, wordRadix]
  omega

private theorem oddBit_val (x : UInt64) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [UInt64.toNat_and]
  change x.toNat &&& (2^1 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem borrow_bit (a : UInt64) (b : Bool) :
    yes (a < yes b) = yes ((a == 0) && b) := by
  have h : (a == 0) = decide (a = 0) := Bool.eq_iff_iff.mpr (by simp)
  cases b
  · have ha : ¬ a < 0 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
      omega
    simp [yes, Bool.toUInt64, ha]
  · change yes (a < 1) = yes ((a == 0) && true)
    rw [Bool.and_true, yes_lt_one, h]

private theorem halveRaw_val (x : Raw) :
    (halveRaw x).val = (x.val + (x.val % 2) * Fp.modulus) / 2 := by
  let bit := x.w0 &&& 1
  -- For an odd input, adding the modulus is a high bit minus the complement.
  let subtrahend := complement * bit
  let a := x.w0 - subtrahend
  have hbit : bit.toNat = x.val % 2 := by
    rw [oddBit_val]
    simp only [Raw.val, Raw.words, lowValue, wordRadix]
    omega
  have hbitBound : bit.toNat ≤ 1 := by omega
  have hsub : subtrahend.toNat = bit.toNat * 4294968273 := by
    rw [UInt64.toNat_mul]
    change 4294968273 * bit.toNat % 2^64 = _
    omega
  by_cases h : subtrahend ≤ x.w0
  · let w : Words64 := ⟨a, x.w1, x.w2, x.w3, bit⟩
    have ha : a.toNat = x.w0.toNat - subtrahend.toNat := UInt64.toNat_sub_of_le _ _ h
    have hge : subtrahend.toNat ≤ x.w0.toNat := h
    have he : w.val = x.val + (x.val % 2) * Fp.modulus := by
      rw [← hbit]
      simp only [w, value, lowValue, Raw.val, Raw.words, Fp.modulus, wordRadix]
      omega
    change Raw.val (if subtrahend ≤ x.w0 then _ else _) = _
    simp only [h, ite_true]
    exact (shiftHalf_val w hbitBound).trans (congrArg (· / 2) he)
  · let b0 := yes (x.w1 == 0)
    let b1 := yes (x.w1 == 0 && x.w2 == 0)
    let b2 := yes (x.w1 == 0 && x.w2 == 0 && x.w3 == 0)
    let w : Words64 := ⟨a, x.w1-1, x.w2-b0, x.w3-b1, bit-b2⟩
    have hlt : x.w0 < subtrahend := UInt64.lt_iff_toNat_lt.mpr (by
      have hh : ¬ subtrahend.toNat ≤ x.w0.toNat := h
      omega)
    have hbitOne : bit.toNat = 1 := by
      have hh : x.w0.toNat < subtrahend.toNat := hlt
      omega
    have hb2 : b2.toNat ≤ bit.toNat := by
      rw [hbitOne]
      exact yes_le_one _
    have ht : (bit-b2).toNat = bit.toNat - b2.toNat := UInt64.toNat_sub_of_le _ _ hb2
    have htop : w.top.toNat ≤ 1 := by
      change (bit-b2).toNat ≤ 1
      rw [ht]
      omega
    have e0 := sub_split x.w0 subtrahend
    have e1 := sub_split x.w1 1
    have e2 := sub_split x.w2 b0
    have e3 := sub_split x.w3 b1
    have h1 : yes (x.w1 < 1) = b0 := by
      change yes (x.w1 < yes true) = _
      rw [borrow_bit, Bool.and_true]
    have h2 : yes (x.w2 < b0) = b1 := by
      rw [borrow_bit]
      exact congrArg yes (Bool.and_comm _ _)
    have h3 : yes (x.w3 < b1) = b2 := by
      rw [borrow_bit]
      exact congrArg yes (Bool.and_comm _ _)
    rw [h1] at e1
    rw [h2] at e2
    rw [h3] at e3
    have hcarry : yes (x.w0 < subtrahend) = 1 := by simp [hlt, yes, Bool.toUInt64]
    rw [hcarry] at e0
    have he : w.val = x.val + (x.val % 2) * Fp.modulus := by
      rw [← hbit]
      change a.toNat + wordRadix*(x.w1-1).toNat + wordRadix^2*(x.w2-b0).toNat +
        wordRadix^3*(x.w3-b1).toNat + wordRadix^4*(bit-b2).toNat =
        x.val + bit.toNat * Fp.modulus
      rw [ht]
      change a.toNat + subtrahend.toNat = _ at e0
      simp only [Raw.val, Raw.words, lowValue, UInt64.toNat_one, Nat.mul_one,
        Fp.modulus, wordRadix] at *
      omega
    change Raw.val (if subtrahend ≤ x.w0 then _ else _) = _
    simp only [h, ite_false]
    exact (shiftHalf_val w htop).trans (congrArg (· / 2) he)

/-- Halve a canonical Montgomery residue by making its representative even first. -/
@[inline] def halve (a : @& Montgomery) : Montgomery :=
  ⟨halveRaw a.raw, by
    rw [halveRaw_val]
    have ha := a.lt
    have h : a.raw.val % 2 = 0 ∨ a.raw.val % 2 = 1 := by omega
    rcases h with h | h <;> rw [h] <;> omega⟩

/-- Subtract a one-word product and the incoming borrow. -/
@[inline] def subtractWordProduct (p : Pair) (w cin : UInt64) : Pair :=
  let sum := p.lo + cin
  let hi := p.hi + yes (sum < p.lo)
  ⟨w - sum, hi + yes (w < sum)⟩

@[inline] private def productBorrow (a b w cin : UInt64) : Pair :=
  subtractWordProduct (wordProduct a b) w cin

private theorem productBorrow_spec (a b w cin : UInt64) :
    (productBorrow a b w cin).lo.toNat + a.toNat*b.toNat + cin.toNat =
      w.toNat + wordRadix * (productBorrow a b w cin).hi.toNat := by
  let lo := a*b
  let sum := lo + cin
  let hi := mulHigh a b
  let ca := yes (sum < lo)
  let cb := yes (w < sum)
  have hp : lo.toNat + 2^64 * hi.toNat = a.toNat*b.toNat := by
    dsimp only [lo, hi]
    rw [UInt64.toNat_mul, mulHigh_spec, Nat.mod_add_div]
  have ha := add_with_carry lo cin
  have hb := sub_split w sum
  change sum.toNat + 2^64 * ca.toNat = _ at ha
  change (w-sum).toNat + sum.toNat = w.toNat + 2^64 * cb.toNat at hb
  have hlim : a.toNat*b.toNat ≤ (2^64-1)*(2^64-1) := Nat.mul_le_mul
    (by have := a.toNat_lt; omega) (by have := b.toNat_lt; omega)
  have hc := cin.toNat_lt
  have hw := w.toNat_lt
  have hl := (w-sum).toNat_lt
  have hs : hi.toNat + ca.toNat + cb.toNat < 2^64 := by omega
  change (w-sum).toNat + a.toNat*b.toNat + cin.toNat =
    w.toNat + 2^64 * (hi+ca+cb).toNat
  have he := add_exact (a := hi) (b := ca) (by omega)
  rw [add_exact (by rw [he]; exact hs), he]
  omega

/-- Cancel the low word of a signed difference of partial products.

The top word of the accumulator uses two's complement.
-/
@[inline] def fusedStageProducts (a : Raw) (b : UInt64) (p0 p1 p2 p3 : Pair)
    (t : Words64) : Words64 :=
  let m0 := mac a.w0 b t.w0 0
  let m1 := mac a.w1 b t.w1 m0.hi
  let m2 := mac a.w2 b t.w2 m1.hi
  let m3 := mac a.w3 b t.w3 m2.hi
  let s4 := m3.hi + t.top
  let s5 := ((0 : UInt64) - (t.top >>> 63)) + yes (s4 < m3.hi)
  let n0 := subtractWordProduct p0 m0.lo 0
  let n1 := subtractWordProduct p1 m1.lo n0.hi
  let n2 := subtractWordProduct p2 m2.lo n1.hi
  let n3 := subtractWordProduct p3 m3.lo n2.hi
  let n4 := s4 - n3.hi
  let n5 := s5 - yes (s4 < n3.hi)
  red (fun q _ => mulHighComplement q) n0.lo n1.lo n2.lo n3.lo n4 n5

/-- One step of a fused difference: add `a b`, subtract `c d`, and reduce once. -/
@[inline] def fusedStage (a c : Raw) (b d : UInt64) (t : Words64) : Words64 :=
  fusedStageProducts a b (wordProduct c.w0 d) (wordProduct c.w1 d)
    (wordProduct c.w2 d) (wordProduct c.w3 d) t

private theorem fusedStageProducts_eq_stage (a c : Raw) (b d : UInt64) (t : Words64) :
    fusedStageProducts a b (wordProduct c.w0 d) (wordProduct c.w1 d)
      (wordProduct c.w2 d) (wordProduct c.w3 d) t = fusedStage a c b d t := rfl

/-- Add the radix to the signed accumulator so its bounds use natural numbers. -/
def bias (w : Words64) : Words64 := { w with top := w.top + 1 }

private theorem biasTop_choices (t : UInt64) (ht : (t+1).toNat < 3) :
    t = 0xffffffffffffffff ∨ t = 0 ∨ t = 1 := by
  have he := UInt64.toNat_add t 1
  have hb := t.toNat_lt
  rw [UInt64.toNat_one] at he
  have hs : t.toNat = 2^64-1 ∨ t.toNat = 0 ∨ t.toNat = 1 := by omega
  rcases hs with h | h | h
  · exact .inl (UInt64.toNat_inj.mp h)
  · exact .inr (.inl (UInt64.toNat_inj.mp h))
  · exact .inr (.inr (UInt64.toNat_inj.mp h))

private theorem add_swap64 (a b c : UInt64) : a+b+c = a+c+b := by
  rw [UInt64.add_assoc, UInt64.add_assoc, UInt64.add_comm b c]

private theorem addBiased_val (x t : UInt64) (ht : (t+1).toNat < 3) :
    let s := x+t
    let carry := yes (s < x)
    let h := (0 : UInt64) - (t >>> 63) + carry
    s.toNat + wordRadix*(h+1).toNat = x.toNat + (t+1).toNat + (wordRadix-1) ∧
      (h+1).toNat ≤ 2 := by
  let s := x+t
  let carry := yes (s < x)
  have hc : carry.toNat ≤ 1 := yes_le_one (s < x)
  have hs := add_with_carry x t
  change s.toNat + 2^64*carry.toNat = x.toNat + t.toNat at hs
  have ec : (carry+1).toNat = carry.toNat + 1 := by
    rw [add_exact (by rw [UInt64.toNat_one]; omega), UInt64.toNat_one]
  rcases biasTop_choices t ht with rfl | rfl | rfl
  · let k : UInt64 := 0xffffffffffffffff
    change s.toNat + wordRadix*((0 : UInt64) - (k >>> 63) + carry + 1).toNat =
      x.toNat + (k+1).toNat + (wordRadix-1) ∧ _
    have e : (0 : UInt64) - (k >>> 63) + carry + 1 = carry := by
      rw [show k >>> 63 = 1 by decide, add_swap64, UInt64.sub_add_cancel, UInt64.zero_add]
    rw [e, show (k+1).toNat = 0 by decide]
    change s.toNat + 2^64*carry.toNat = x.toNat + 0 + (2^64-1) ∧ carry.toNat ≤ 2
    rw [show (0xffffffffffffffff : UInt64).toNat = 2^64-1 by decide] at hs
    omega
  · change s.toNat + wordRadix*((0 : UInt64) - ((0 : UInt64) >>> 63) + carry + 1).toNat =
      x.toNat + ((0 : UInt64)+1).toNat + (wordRadix-1) ∧ _
    have e : (0 : UInt64) - ((0 : UInt64) >>> 63) + carry + 1 = carry + 1 := by
      rw [show (0 : UInt64) - ((0 : UInt64) >>> 63) = 0 by decide, UInt64.zero_add]
    rw [e, ec]
    change s.toNat + 2^64*(carry.toNat+1) = x.toNat + 1 + (2^64-1) ∧ carry.toNat+1 ≤ 2
    simp only [UInt64.toNat_zero, Nat.add_zero] at hs
    omega
  · change s.toNat + wordRadix*((0 : UInt64) - ((1 : UInt64) >>> 63) + carry + 1).toNat =
      x.toNat + ((1 : UInt64)+1).toNat + (wordRadix-1) ∧ _
    have e : (0 : UInt64) - ((1 : UInt64) >>> 63) + carry + 1 = carry + 1 := by
      rw [show (0 : UInt64) - ((1 : UInt64) >>> 63) = 0 by decide, UInt64.zero_add]
    rw [e, ec]
    change s.toNat + 2^64*(carry.toNat+1) = x.toNat + 2 + (2^64-1) ∧ carry.toNat+1 ≤ 2
    rw [UInt64.toNat_one] at hs
    omega

private theorem red_bias (mulHi : UInt64 → UInt64 → UInt64) (s0 s1 s2 s3 s4 s5 : UInt64) :
    bias (red mulHi s0 s1 s2 s3 s4 s5) = red mulHi s0 s1 s2 s3 s4 (s5+1) := by
  have swap (a b : UInt64) : a - b + 1 = a + 1 - b := by
    apply UInt64.eq_sub_iff_add_eq.mpr
    rw [add_swap64, UInt64.sub_add_cancel]
  unfold red bias
  dsimp only
  split <;> simp only [add_swap64 (c := 1), swap]

private theorem fusedStage_spec (a c : Raw) (b d : UInt64) (t : Words64)
    (ha : a.val < Fp.modulus) (hc : c.val < Fp.modulus)
    (htlo : 2^256 - Fp.modulus ≤ value (bias t))
    (hthi : value (bias t) < 2 * Fp.modulus + 2^256) :
    (2^256 - Fp.modulus ≤ value (bias (fusedStage a c b d t)) ∧
      value (bias (fusedStage a c b d t)) < 2 * Fp.modulus + 2^256) ∧
    ∃ q, wordRadix * value (bias (fusedStage a c b d t)) + c.val * d.toNat =
      value (bias t) + a.val * b.toNat + q * Fp.modulus + 2^256 * (wordRadix-1) := by
  let m0 := mac a.w0 b t.w0 0
  let m1 := mac a.w1 b t.w1 m0.hi
  let m2 := mac a.w2 b t.w2 m1.hi
  let m3 := mac a.w3 b t.w3 m2.hi
  let s4 := m3.hi + t.top
  let s5 := ((0 : UInt64) - (t.top >>> 63)) + yes (s4 < m3.hi)
  let n0 := productBorrow c.w0 d m0.lo 0
  let n1 := productBorrow c.w1 d m1.lo n0.hi
  let n2 := productBorrow c.w2 d m2.lo n1.hi
  let n3 := productBorrow c.w3 d m3.lo n2.hi
  let n4 := s4 - n3.hi
  let borrow := yes (s4 < n3.hi)
  let n5 := s5 - borrow
  have ht : (t.top + 1).toNat < 3 := by
    simp only [bias, value, wordRadix, Fp.modulus] at hthi
    omega
  have ⟨hs, hstop⟩ := addBiased_val m3.hi t.top ht
  change s4.toNat + wordRadix*(s5+1).toNat =
    m3.hi.toNat + (t.top+1).toNat + (wordRadix-1) at hs
  change (s5+1).toNat ≤ 2 at hstop
  have hn : borrow ≤ s5 + 1 := by
    apply UInt64.le_iff_toNat_le.mpr
    have hb : borrow.toNat ≤ 1 := yes_le_one (s4 < n3.hi)
    by_cases h : borrow.toNat ≤ (s5+1).toNat
    · exact h
    · have hbs : (s5+1).toNat = 0 ∧ borrow.toNat = 1 := by omega
      have hm := s4.toNat_lt
      have hn3 := n3.hi.toNat_lt
      have hh : s4.toNat = 2^64-1 := by
        rw [hbs.1] at hs
        simp only [wordRadix] at hs
        omega
      have he : ¬ s4 < n3.hi := by change ¬ s4.toNat < n3.hi.toNat; omega
      have hb0 : borrow.toNat = 0 := by simp [borrow, he, yes, Bool.toUInt64]
      omega
  have hn5 : (n5+1).toNat + borrow.toNat = (s5+1).toNat := by
    have hswap : n5 + 1 = s5 + 1 - borrow := by
      apply UInt64.eq_sub_iff_add_eq.mpr
      change (s5-borrow)+1+borrow = s5+1
      rw [add_swap64, UInt64.sub_add_cancel]
    rw [hswap, UInt64.toNat_sub_of_le _ _ hn]
    have hh : borrow.toNat ≤ (s5+1).toNat := hn
    omega
  have hn4 := sub_split s4 n3.hi
  change n4.toNat + n3.hi.toNat = s4.toNat + wordRadix*borrow.toNat at hn4
  have e0 := mac_spec a.w0 b t.w0 0
  have e1 := mac_spec a.w1 b t.w1 m0.hi
  have e2 := mac_spec a.w2 b t.w2 m1.hi
  have e3 := mac_spec a.w3 b t.w3 m2.hi
  have f0 := productBorrow_spec c.w0 d m0.lo 0
  have f1 := productBorrow_spec c.w1 d m1.lo n0.hi
  have f2 := productBorrow_spec c.w2 d m2.lo n1.hi
  have f3 := productBorrow_spec c.w3 d m3.lo n2.hi
  change m0.lo.toNat + 2^64*m0.hi.toNat = _ at e0
  change m1.lo.toNat + 2^64*m1.hi.toNat = _ at e1
  change m2.lo.toNat + 2^64*m2.hi.toNat = _ at e2
  change m3.lo.toNat + 2^64*m3.hi.toNat = _ at e3
  change n0.lo.toNat + c.w0.toNat*d.toNat + 0 = m0.lo.toNat + wordRadix*n0.hi.toNat at f0
  change n1.lo.toNat + c.w1.toNat*d.toNat + n0.hi.toNat =
    m1.lo.toNat + wordRadix*n1.hi.toNat at f1
  change n2.lo.toNat + c.w2.toNat*d.toNat + n1.hi.toNat =
    m2.lo.toNat + wordRadix*n2.hi.toNat at f2
  change n3.lo.toNat + c.w3.toNat*d.toNat + n2.hi.toNat =
    m3.lo.toNat + wordRadix*n3.hi.toNat at f3
  let row : Words64 := ⟨n1.lo, n2.lo, n3.lo, n4, n5⟩
  have he : n0.lo.toNat + wordRadix * value (bias row) + c.val*d.toNat =
      value (bias t) + a.val*b.toNat + 2^256 * (wordRadix-1) := by
    simp only [row,bias,Raw.val,Raw.words,value,lowValue,wordRadix,Nat.add_mul,Nat.mul_assoc,
      UInt64.toNat_zero,Nat.add_zero] at *
    omega
  let q := (n0.lo * inverseComplement).toNat
  have out := red_spec (fun q _ => mulHighComplement q) mulHighComplement_spec
    n0.lo n1.lo n2.lo n3.lo n4 (n5+1) (by omega)
  rw [← red_bias] at out
  change wordRadix*value (bias (fusedStage a c b d t)) =
    n0.lo.toNat + wordRadix*value (bias row) + q*Fp.modulus at out
  have hsum : wordRadix * value (bias (fusedStage a c b d t)) + c.val*d.toNat =
      value (bias t) + a.val*b.toNat + q*Fp.modulus + 2^256*(wordRadix-1) := by omega
  have amax : a.val*b.toNat ≤ Fp.modulus*(wordRadix-1) :=
    Nat.mul_le_mul (by omega) (by have := b.toNat_lt; simp only [wordRadix]; omega)
  have cmax : c.val*d.toNat ≤ Fp.modulus*(wordRadix-1) :=
    Nat.mul_le_mul (by omega) (by have := d.toNat_lt; simp only [wordRadix]; omega)
  have qmax : q*Fp.modulus ≤ Fp.modulus*(wordRadix-1) := by
    rw [Nat.mul_comm q]
    apply Nat.mul_le_mul_left
    have := (n0.lo * inverseComplement).toNat_lt
    simp only [wordRadix]
    omega
  exact ⟨by simp only [wordRadix, Fp.modulus] at *; omega, q, hsum⟩

/-- Accumulate the difference of two products through the four Montgomery steps.

It is the reference that the fused square is proved against. -/
@[inline] def fusedAccum (a b c d : Raw) : Words64 :=
  fusedStage a c b.w3 d.w3 (fusedStage a c b.w2 d.w2
    (fusedStage a c b.w1 d.w1 (fusedStage a c b.w0 d.w0 ⟨0,0,0,0,0⟩)))

theorem fusedAccum_spec (a b c d : Raw) (ha : a.val < Fp.modulus) (hc : c.val < Fp.modulus) :
    (2^256 - Fp.modulus ≤ value (bias (fusedAccum a b c d)) ∧
      value (bias (fusedAccum a b c d)) < 2 * Fp.modulus + 2^256) ∧
    ∃ q, 2^256 * value (bias (fusedAccum a b c d)) + c.val*d.val =
      a.val*b.val + q*Fp.modulus + (2^256)*(2^256) := by
  let zero : Words64 := ⟨0,0,0,0,0⟩
  let r0 := fusedStage a c b.w0 d.w0 zero
  let r1 := fusedStage a c b.w1 d.w1 r0
  let r2 := fusedStage a c b.w2 d.w2 r1
  let r3 := fusedStage a c b.w3 d.w3 r2
  obtain ⟨hb0, q0, e0⟩ := fusedStage_spec a c b.w0 d.w0 zero ha hc (by decide) (by decide)
  obtain ⟨hb1, q1, e1⟩ := fusedStage_spec a c b.w1 d.w1 r0 ha hc hb0.1 hb0.2
  obtain ⟨hb2, q2, e2⟩ := fusedStage_spec a c b.w2 d.w2 r1 ha hc hb1.1 hb1.2
  obtain ⟨hb3, q3, e3⟩ := fusedStage_spec a c b.w3 d.w3 r2 ha hc hb2.1 hb2.2
  change 2^256-Fp.modulus ≤ value (bias r3) ∧ value (bias r3) < 2*Fp.modulus+2^256 at hb3
  refine ⟨hb3, q0+wordRadix*q1+wordRadix^2*q2+wordRadix^3*q3, ?_⟩
  change wordRadix * value (bias r0) + c.val*d.w0.toNat =
    _+a.val*b.w0.toNat+q0*Fp.modulus+_ at e0
  change wordRadix * value (bias r1) + c.val*d.w1.toNat =
    value (bias r0)+a.val*b.w1.toNat+q1*Fp.modulus+_ at e1
  change wordRadix * value (bias r2) + c.val*d.w2.toNat =
    value (bias r1)+a.val*b.w2.toNat+q2*Fp.modulus+_ at e2
  change wordRadix * value (bias r3) + c.val*d.w3.toNat =
    value (bias r2)+a.val*b.w3.toNat+q3*Fp.modulus+_ at e3
  rw [show value (bias zero) = 2^256 by decide] at e0
  change 2^256 * value (bias r3) + c.val*d.val =
    a.val*b.val + (q0+wordRadix*q1+wordRadix^2*q2+wordRadix^3*q3)*Fp.modulus+_
  rw [show d.val = d.w0.toNat+wordRadix*d.w1.toNat+wordRadix^2*d.w2.toNat+
      wordRadix^3*d.w3.toNat from rfl,
    show b.val = b.w0.toNat+wordRadix*b.w1.toNat+wordRadix^2*b.w2.toNat+
      wordRadix^3*b.w3.toNat from rfl]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_left_comm a.val, Nat.mul_left_comm c.val,
    Nat.mul_assoc, Fp.modulus, wordRadix] at *
  omega

private theorem biasTop_bound (t : Words64) (hhi : value (bias t) < 2*Fp.modulus+2^256) :
    (t.top+1).toNat < 3 := by
  simp only [value, bias, wordRadix, Fp.modulus] at hhi
  omega

theorem fusedFinish_negative (t : Words64) (h : t.top >>> 63 ≠ 0)
    (hlo : 2^256-Fp.modulus ≤ value (bias t)) (hhi : value (bias t) < 2*Fp.modulus+2^256) :
    (Raw.fromWords (correctMasked t.w0 t.w1 t.w2 t.w3 1)).val < Fp.modulus ∧
      (Raw.fromWords (correctMasked t.w0 t.w1 t.w2 t.w3 1)).val + 2^256 =
        value (bias t) + Fp.modulus := by
  rcases biasTop_choices t.top (biasTop_bound t hhi) with ht | ht | ht
  · have he : (t.top+1) = 0 := ht ▸ (by decide)
    have hb : bias t = ⟨t.w0,t.w1,t.w2,t.w3,0⟩ := by
      cases t with
      | mk w0 w1 w2 w3 tp => simp only [bias, he]
    have hlim : complement.toNat ≤ value ⟨t.w0,t.w1,t.w2,t.w3,0⟩ := by
      rw [← hb]
      exact (show complement.toNat = 2^256-Fp.modulus by decide) ▸ hlo
    have hf := correctBorrow_value t.w0 t.w1 t.w2 t.w3 hlim
    rw [← hb] at hf
    have hc := correctMasked_eq t.w0 t.w1 t.w2 t.w3 1 (by decide)
    rw [ite_eq_right (show (1 : UInt64) ≠ 0 by decide)] at hc
    have ht0 : (correctMasked t.w0 t.w1 t.w2 t.w3 1).top = 0 := rfl
    have hval := lowValue_lt t
    have hbas : value (bias t) < 2^256 := by
      rw [hb, value_mk_zero]
      simpa [lowValue, wordRadix] using hval
    rw [Raw.fromWords_val _ ht0, hc]
    simp only [Fp.modulus, complement, UInt64.toNat_ofNat] at *
    omega
  · exact absurd (ht ▸ (by decide : (0 : UInt64) >>> 63 = 0)) h
  · exact absurd (ht ▸ (by decide : (1 : UInt64) >>> 63 = 0)) h

theorem fusedFinish_positive (t : Words64) (h : ¬ t.top >>> 63 ≠ 0)
    (hhi : value (bias t) < 2*Fp.modulus+2^256) :
    value t < 2*Fp.modulus ∧ value (bias t) = value t + 2^256 := by
  have ht : t.top.toNat ≤ 1 := by
    rcases biasTop_choices t.top (biasTop_bound t hhi) with ht | ht | ht
    · exact False.elim (h (ht ▸ (by decide : (0xffffffffffffffff : UInt64) >>> 63 ≠ 0)))
    · rw [ht, UInt64.toNat_zero]; decide
    · rw [ht, UInt64.toNat_one]; decide
  have hs : (t.top+1).toNat = t.top.toNat + 1 := by
    rw [add_exact (by rw [UInt64.toNat_one]; omega), UInt64.toNat_one]
  have he : value (bias t) = value t + 2^256 := by
    change lowValue t + wordRadix^4*(t.top+1).toNat =
      (lowValue t + wordRadix^4*t.top.toNat) + 2^256
    rw [hs, Nat.mul_add, Nat.mul_one, Nat.add_assoc, show wordRadix^4 = 2^256 by decide]
  exact ⟨by rw [he] at hhi; omega, he⟩

/-- Convert the signed accumulator to a canonical field residue. -/
@[inline] def fusedFinishFallback (t : Words64)
    (hlo : 2^256-Fp.modulus ≤ value (bias t)) (hhi : value (bias t) < 2*Fp.modulus+2^256) :
    Montgomery :=
  if h : t.top >>> 63 ≠ 0 then
    ⟨Raw.fromWords (correctMasked t.w0 t.w1 t.w2 t.w3 1),
      (fusedFinish_negative t h hlo hhi).1⟩
  else finish t (fusedFinish_positive t h hhi).1

/-- Add the modulus complement multiplied by the signed top word. -/
@[inline] def signedFastRaw (t : Words64) : Raw :=
  ⟨t.w0 + t.top * complement, t.w1, t.w2, t.w3⟩

private theorem fusedFinish_raw_eq_signedFast (t : Words64)
    (hlo : 2^256-Fp.modulus ≤ value (bias t)) (hhi : value (bias t) < 2*Fp.modulus+2^256)
    (h : t.w0 - complement < 0xfffffffdfffff85e) :
    (fusedFinishFallback t hlo hhi).raw = signedFastRaw t := by
  have hc : complement.toNat = 4294968273 := by decide
  have ht0 := t.w0.toNat_lt
  have hh : (t.w0 - complement).toNat < 0xfffffffdfffff85e := h
  rw [UInt64.toNat_sub, hc] at hh
  have hpre : complement ≤ t.w0 := by
    change complement.toNat ≤ t.w0.toNat
    rw [hc]
    omega
  have hlt : t.w0 < 0xfffffffefffffc2f := by
    change t.w0.toNat < 0xfffffffefffffc2f
    omega
  rcases biasTop_choices t.top (biasTop_bound t hhi) with ht | ht | ht
  · have hneg : t.top >>> 63 ≠ 0 := by rw [ht]; decide
    have hsub : ¬ t.w0 < complement := UInt64.not_lt.mpr hpre
    have hfac : t.top * complement = -complement := by rw [ht]; decide
    unfold fusedFinishFallback
    rw [dite_eq_left hneg]
    change Raw.fromWords (correctMasked t.w0 t.w1 t.w2 t.w3 1) = signedFastRaw t
    simp [correctMasked, hsub, signedFastRaw, hfac, yes, Bool.toUInt64,
      UInt64.sub_eq_add_neg, Raw.fromWords]
  · have hneg : ¬ t.top >>> 63 ≠ 0 := by rw [ht]; decide
    unfold fusedFinishFallback
    rw [dite_eq_right hneg]
    change Raw.fromWords (reduceFast t) = signedFastRaw t
    simp [reduceFast, hlt, ht, signedFastRaw, Raw.fromWords]
  · have hneg : ¬ t.top >>> 63 ≠ 0 := by rw [ht]; decide
    unfold fusedFinishFallback
    rw [dite_eq_right hneg]
    change Raw.fromWords (reduceFast t) = signedFastRaw t
    simp [reduceFast, hlt, ht, signedFastRaw, Raw.fromWords]

/-- Correct the low word of a signed product difference when the carry stays in that word. -/
@[inline] def fusedFinish (t : Words64)
    (hlo : 2^256-Fp.modulus ≤ value (bias t)) (hhi : value (bias t) < 2*Fp.modulus+2^256) :
    Montgomery :=
  -- The low word can absorb a correction of either sign within this interval.
  if h : t.w0 - complement < 0xfffffffdfffff85e then
    ⟨signedFastRaw t, by
      rw [← fusedFinish_raw_eq_signedFast t hlo hhi h]
      exact (fusedFinishFallback t hlo hhi).lt⟩
  else fusedFinishFallback t hlo hhi

/-- Subtract the negative column and incoming borrow from one word. -/
@[inline] def subtractColumnCarry (pos neg carry : UInt64) : Pair :=
  let a := pos - neg
  ⟨a - carry, yes (pos < neg) + yes (a < carry)⟩

/-- Cancel one low difference word and compute the borrow for the next word. -/
@[inline] def cancelDifferenceColumn (pos neg carry : UInt64) : Pair :=
  let d := subtractColumnCarry pos neg carry
  let q := d.lo * cancellationConstants.inverse
  ⟨q, mulHighComplement q + d.hi⟩

/-- Add one word of the Montgomery quotient to a high product column. -/
@[inline] def addColumnQuotient (c : ProductColumn) (word : UInt64) : ProductColumn :=
  c.add ⟨word, 0⟩

private theorem subtractColumnCarry_spec (pos neg carry : UInt64) :
    (subtractColumnCarry pos neg carry).lo.toNat + neg.toNat + carry.toNat =
      pos.toNat + wordRadix * (subtractColumnCarry pos neg carry).hi.toNat := by
  let a := pos - neg
  let b0 := yes (pos < neg)
  let b1 := yes (a < carry)
  have h0 : a.toNat + neg.toNat = pos.toNat + wordRadix*b0.toNat := sub_split pos neg
  have h1 : (a-carry).toNat + carry.toNat = a.toNat + wordRadix*b1.toNat := sub_split a carry
  have hb0 : b0.toNat ≤ 1 := yes_le_one (pos < neg)
  have hb1 : b1.toNat ≤ 1 := yes_le_one (a < carry)
  have he : (b0+b1).toNat = b0.toNat+b1.toNat := add_exact (by omega)
  change (a-carry).toNat + neg.toNat + carry.toNat = pos.toNat + wordRadix * (b0+b1).toNat
  rw [he]
  simp only [wordRadix] at *
  omega

private theorem subtractColumnCarry_hi (pos neg carry : UInt64) :
    (subtractColumnCarry pos neg carry).hi.toNat ≤ 2 := by
  change (yes (pos < neg) + yes (pos-neg < carry)).toNat ≤ _
  have h0 := yes_le_one (pos < neg)
  have h1 := yes_le_one (pos-neg < carry)
  rw [add_exact (by omega)]
  omega

private theorem cancelDifferenceColumn_spec (pos neg carry : UInt64) :
    (cancelDifferenceColumn pos neg carry).lo.toNat * complement.toNat + neg.toNat +
        carry.toNat = pos.toNat + wordRadix * (cancelDifferenceColumn pos neg carry).hi.toNat := by
  let d := subtractColumnCarry pos neg carry
  let q := d.lo * cancellationConstants.inverse
  let high := mulHighComplement q
  have hd := subtractColumnCarry_spec pos neg carry
  have hb : d.hi.toNat ≤ 2 := subtractColumnCarry_hi pos neg carry
  change d.lo.toNat + neg.toNat + carry.toNat = pos.toNat + wordRadix*d.hi.toNat at hd
  have hq : (q * complement).toNat = d.lo.toNat := congrArg UInt64.toNat (radix_q d.lo)
  have hh : high.toNat < complement.toNat := by
    rw [mulHighComplement_spec]
    apply Nat.div_lt_of_lt_mul
    exact Nat.mul_lt_mul_of_pos_right q.toNat_lt (by decide)
  have hC : complement.toNat = 4294968273 := by decide
  have he : (high + d.hi).toNat = high.toNat+d.hi.toNat := add_exact (by omega)
  have hs := Nat.mod_add_div (q.toNat * complement.toNat) wordRadix
  rw [UInt64.toNat_mul] at hq
  rw [hq, ← mulHighComplement_spec] at hs
  change d.lo.toNat + wordRadix*high.toNat = q.toNat * complement.toNat at hs
  change q.toNat * complement.toNat + neg.toNat + carry.toNat =
    pos.toNat + wordRadix * (high+d.hi).toNat
  rw [he]
  simp only [wordRadix] at *
  omega

private theorem addColumnQuotient_spec (c : ProductColumn) (q : UInt64) (h : c.hi.toNat < 16) :
    (addColumnQuotient c q).val = c.val + q.toNat ∧
      (addColumnQuotient c q).hi.toNat ≤ c.hi.toNat + 2 := by
  simpa only [addColumnQuotient, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] using
    c.add_spec ⟨q, 0⟩ h

private def columnLow (c0 c1 c2 c3 : ProductColumn) : Nat :=
  lowValue ⟨c0.lo, c1.lo, c2.lo, c3.lo, 0⟩

private theorem columnScan_balance
    (c0 c1 c2 c3 c4 c5 c6 c7 : ProductColumn)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (h0 : c0.val = s0)
    (h1 : c1.val = c0.next.val + s1)
    (h2 : c2.val = c1.next.val + s2)
    (h3 : c3.val = c2.next.val + s3)
    (h4 : c4.val = c3.next.val + s4)
    (h5 : c5.val = c4.next.val + s5)
    (h6 : c6.val = c5.next.val + s6)
    (h7 : c7.val = c6.next.val + s7) :
    columnLow c0 c1 c2 c3 + wordRadix^4 *
      (columnLow c4 c5 c6 c7 + wordRadix^4 * (c7.mid.toNat + wordRadix*c7.hi.toNat)) =
        s0 + wordRadix*s1 + wordRadix^2*s2 + wordRadix^3*s3 +
          wordRadix^4*s4 + wordRadix^5*s5 + wordRadix^6*s6 + wordRadix^7*s7 := by
  have e0 := c0.next_spec
  have e1 := c1.next_spec
  have e2 := c2.next_spec
  have e3 := c3.next_spec
  have e4 := c4.next_spec
  have e5 := c5.next_spec
  have e6 := c6.next_spec
  have e7 : c7.val = c7.lo.toNat + wordRadix*c7.mid.toNat + wordRadix^2*c7.hi.toNat := rfl
  simp only [columnLow, lowValue, Nat.mul_add, wordRadix] at *
  omega

private theorem combineCancel
    (p0 p1 p2 p3 n0 n1 n2 n3 : ProductColumn) :
    let q0 := cancelDifferenceColumn p0.lo n0.lo 0
    let q1 := cancelDifferenceColumn p1.lo n1.lo q0.hi
    let q2 := cancelDifferenceColumn p2.lo n2.lo q1.hi
    let q3 := cancelDifferenceColumn p3.lo n3.lo q2.hi
    columnLow p0 p1 p2 p3 + wordRadix^4*q3.hi.toNat =
      columnLow n0 n1 n2 n3 +
        complement.toNat * lowValue ⟨q0.lo, q1.lo, q2.lo, q3.lo, 0⟩ := by
  dsimp only
  let q0 := cancelDifferenceColumn p0.lo n0.lo 0
  let q1 := cancelDifferenceColumn p1.lo n1.lo q0.hi
  let q2 := cancelDifferenceColumn p2.lo n2.lo q1.hi
  let q3 := cancelDifferenceColumn p3.lo n3.lo q2.hi
  have e0 : q0.lo.toNat * complement.toNat + n0.lo.toNat + 0 =
      p0.lo.toNat + wordRadix*q0.hi.toNat := cancelDifferenceColumn_spec p0.lo n0.lo 0
  have e1 : q1.lo.toNat * complement.toNat + n1.lo.toNat + q0.hi.toNat =
      p1.lo.toNat + wordRadix*q1.hi.toNat := cancelDifferenceColumn_spec p1.lo n1.lo q0.hi
  have e2 : q2.lo.toNat * complement.toNat + n2.lo.toNat + q1.hi.toNat =
      p2.lo.toNat + wordRadix*q2.hi.toNat := cancelDifferenceColumn_spec p2.lo n2.lo q1.hi
  have e3 : q3.lo.toNat * complement.toNat + n3.lo.toNat + q2.hi.toNat =
      p3.lo.toNat + wordRadix*q3.hi.toNat := cancelDifferenceColumn_spec p3.lo n3.lo q2.hi
  change columnLow p0 p1 p2 p3 + wordRadix^4*q3.hi.toNat =
    columnLow n0 n1 n2 n3 + complement.toNat*lowValue ⟨q0.lo, q1.lo, q2.lo, q3.lo, 0⟩
  -- Keep the coefficient symbolic until the four cancellations are combined.
  generalize complement.toNat = C at *
  have factor : C*lowValue ⟨q0.lo, q1.lo, q2.lo, q3.lo, 0⟩ =
      q0.lo.toNat*C + wordRadix*(q1.lo.toNat*C) + wordRadix^2*(q2.lo.toNat*C) +
        wordRadix^3*(q3.lo.toNat*C) := by
    simp only [lowValue, Nat.mul_add]
    ac_rfl
  rw [factor]
  simp only [columnLow, lowValue, wordRadix] at *
  omega

private theorem combineDifference
    (p4 p5 p6 p7 n4 n5 n6 n7 : ProductColumn) (carry : UInt64) :
    let z0 := subtractColumnCarry p4.lo n4.lo carry
    let z1 := subtractColumnCarry p5.lo n5.lo z0.hi
    let z2 := subtractColumnCarry p6.lo n6.lo z1.hi
    let z3 := subtractColumnCarry p7.lo n7.lo z2.hi
    lowValue ⟨z0.lo, z1.lo, z2.lo, z3.lo, 0⟩ +
      columnLow n4 n5 n6 n7 + carry.toNat =
      columnLow p4 p5 p6 p7 + wordRadix^4*z3.hi.toNat := by
  dsimp only
  let z0 := subtractColumnCarry p4.lo n4.lo carry
  let z1 := subtractColumnCarry p5.lo n5.lo z0.hi
  let z2 := subtractColumnCarry p6.lo n6.lo z1.hi
  let z3 := subtractColumnCarry p7.lo n7.lo z2.hi
  have e0 : z0.lo.toNat + n4.lo.toNat + carry.toNat =
      p4.lo.toNat + wordRadix*z0.hi.toNat := subtractColumnCarry_spec p4.lo n4.lo carry
  have e1 : z1.lo.toNat + n5.lo.toNat + z0.hi.toNat =
      p5.lo.toNat + wordRadix*z1.hi.toNat := subtractColumnCarry_spec p5.lo n5.lo z0.hi
  have e2 : z2.lo.toNat + n6.lo.toNat + z1.hi.toNat =
      p6.lo.toNat + wordRadix*z2.hi.toNat := subtractColumnCarry_spec p6.lo n6.lo z1.hi
  have e3 : z3.lo.toNat + n7.lo.toNat + z2.hi.toNat =
      p7.lo.toNat + wordRadix*z3.hi.toNat := subtractColumnCarry_spec p7.lo n7.lo z2.hi
  change lowValue ⟨z0.lo, z1.lo, z2.lo, z3.lo, 0⟩ +
    columnLow n4 n5 n6 n7 + carry.toNat =
    columnLow p4 p5 p6 p7 + wordRadix^4*z3.hi.toNat
  simp only [columnLow, lowValue, wordRadix] at *
  omega

private theorem balanceWordTop (pTop nTop borrow : UInt64)
    (hp : pTop.toNat < 2) (h : nTop.toNat + borrow.toNat ≤ pTop.toNat + 1) :
    (pTop - nTop - borrow + 1).toNat = pTop.toNat + 1 - (nTop.toNat + borrow.toNat) := by
  have hp0 := pTop.toNat_lt
  have hn0 := nTop.toNat_lt
  have hb0 := borrow.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_one]
  omega

private theorem finishColumns_balance
    (pLo pHi nLo nHi q carry AB CD : Nat)
    (pTop pExtra nTop nExtra borrow z0 z1 z2 z3 : UInt64)
    (hAB : AB < Fp.modulus^2) (hCD : CD < Fp.modulus^2)
    (hq : q < 2^256)
    (hp : pLo + 2^256 * (pHi + 2^256*(pTop.toNat + wordRadix*pExtra.toNat)) = AB + 2^256*q)
    (hn : nLo + 2^256 * (nHi + 2^256*(nTop.toNat + wordRadix*nExtra.toNat)) = CD)
    (hl : pLo + 2^256*carry = nLo + complement.toNat*q)
    (hh : lowValue ⟨z0,z1,z2,z3,0⟩ + nHi + carry = pHi + 2^256*borrow.toNat) :
    let t : Words64 := bias ⟨z0,z1,z2,z3,pTop-nTop-borrow⟩
    (2^256-Fp.modulus ≤ value t ∧ value t < 2*Fp.modulus+2^256) ∧
      ∃ Q, 2^256*value t + CD = AB + Q*Fp.modulus + (2^256)*(2^256) := by
  have hlim := lowValue_lt ⟨z0,z1,z2,z3,0⟩
  have pq := Nat.mul_lt_mul_of_pos_right hq (by decide : 0 < Fp.modulus)
  have hc : complement.toNat = 4294968273 := by decide
  have ht : pTop.toNat < 2 ∧ pExtra.toNat = 0 ∧ nTop.toNat = 0 ∧ nExtra.toNat = 0 := by
    simp only [wordRadix, Fp.modulus] at hp hn hAB hCD hq ⊢
    omega
  rcases ht with ⟨hpt, hpEx, hnTop, hnEx⟩
  rw [hpEx, Nat.mul_zero, Nat.add_zero] at hp
  rw [hnEx, Nat.mul_zero, Nat.add_zero] at hn
  have hb : nTop.toNat+borrow.toNat ≤ pTop.toNat+1 := by
    simp only [hc, Fp.modulus, wordRadix] at hp hn hl hh hlim hCD ⊢
    omega
  have he := balanceWordTop pTop nTop borrow hpt hb
  change (2^256-Fp.modulus ≤ value ⟨z0,z1,z2,z3,pTop-nTop-borrow+1⟩ ∧
      value ⟨z0,z1,z2,z3,pTop-nTop-borrow+1⟩ < 2*Fp.modulus+2^256) ∧
        ∃ Q, 2^256*value ⟨z0,z1,z2,z3,pTop-nTop-borrow+1⟩ + CD =
          AB + Q*Fp.modulus + (2^256)*(2^256)
  simp only [value, he]
  have reg : 2^256 * (lowValue ⟨z0,z1,z2,z3,0⟩ +
      wordRadix^4*(pTop.toNat+1-(nTop.toNat+borrow.toNat))) + CD =
        AB + q*Fp.modulus + (2^256)*(2^256) := by
    simp only [hc, Fp.modulus, wordRadix] at hp hn hl hh hlim ⊢
    omega
  refine ⟨?_, q, reg⟩
  change (2^256-Fp.modulus ≤ lowValue ⟨z0,z1,z2,z3,0⟩ +
      wordRadix^4*(pTop.toNat+1-(nTop.toNat+borrow.toNat))) ∧
    (lowValue ⟨z0,z1,z2,z3,0⟩ + wordRadix^4*(pTop.toNat+1-(nTop.toNat+borrow.toNat)) <
      2*Fp.modulus+2^256)
  generalize lowValue ⟨z0,z1,z2,z3,0⟩ + wordRadix^4 *
    (pTop.toNat + 1 - (nTop.toNat + borrow.toNat)) = z at reg ⊢
  simp only [Fp.modulus] at reg pq hAB hCD ⊢
  omega


private def rawCoefficient0 (a b : Raw) : Nat :=
  a.w0.toNat * b.w0.toNat

private def rawCoefficient1 (a b : Raw) : Nat :=
  a.w0.toNat * b.w1.toNat + a.w1.toNat * b.w0.toNat

private def rawCoefficient2 (a b : Raw) : Nat :=
  a.w0.toNat * b.w2.toNat + a.w1.toNat * b.w1.toNat + a.w2.toNat * b.w0.toNat

private def rawCoefficient3 (a b : Raw) : Nat :=
  a.w0.toNat * b.w3.toNat + a.w1.toNat * b.w2.toNat + a.w2.toNat * b.w1.toNat + a.w3.toNat *
    b.w0.toNat

private def rawCoefficient4 (a b : Raw) : Nat :=
  a.w1.toNat * b.w3.toNat + a.w2.toNat * b.w2.toNat + a.w3.toNat * b.w1.toNat

private def rawCoefficient5 (a b : Raw) : Nat :=
  a.w2.toNat * b.w3.toNat + a.w3.toNat * b.w2.toNat

private def rawCoefficient6 (a b : Raw) : Nat :=
  a.w3.toNat * b.w3.toNat

private theorem rawCoefficients_balance (a b : Raw) :
    a.val * b.val = rawCoefficient0 a b + wordRadix * rawCoefficient1 a b +
      wordRadix^2 * rawCoefficient2 a b + wordRadix^3 * rawCoefficient3 a b +
      wordRadix^4 * rawCoefficient4 a b + wordRadix^5 * rawCoefficient5 a b +
      wordRadix^6 * rawCoefficient6 a b := by
  simp only [Raw.val, Raw.words, lowValue, rawCoefficient0, rawCoefficient1, rawCoefficient2,
    rawCoefficient3, rawCoefficient4, rawCoefficient5, rawCoefficient6]
  generalize wordRadix = r
  simp only [Nat.add_mul, Nat.mul_add, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  ac_rfl

private def addProducts (col : ProductColumn) : List (UInt64 × UInt64) → ProductColumn
  | [] => col
  | (a, b) :: products => addProducts (col.add (wordProduct a b)) products

private def sumProducts : List (UInt64 × UInt64) → Nat
  | [] => 0
  | (a, b) :: products => a.toNat*b.toNat + sumProducts products

private theorem addProducts_spec (col : ProductColumn) (products : List (UInt64 × UInt64))
    (h : col.hi.toNat + 2*products.length < 16) :
    (addProducts col products).val = col.val + sumProducts products ∧
      (addProducts col products).hi.toNat ≤ col.hi.toNat + 2*products.length := by
  induction products generalizing col with
  | nil => simp [addProducts, sumProducts]
  | cons prod rest ih =>
    obtain ⟨a, b⟩ := prod
    simp only [List.length_cons] at h
    let next := col.add (wordProduct a b)
    have hc := ProductColumn.product_spec col a b (by omega)
    change next.val = col.val + a.toNat*b.toNat ∧ next.hi.toNat ≤ col.hi.toNat + 2 at hc
    have hr := ih next (by omega)
    change (addProducts next rest).val = col.val + (a.toNat*b.toNat + sumProducts rest) ∧
      (addProducts next rest).hi.toNat ≤ col.hi.toNat + 2*(rest.length+1)
    rw [hr.1, hc.1, Nat.add_assoc]
    exact ⟨rfl, by have := hr.2; omega⟩

private theorem addProducts_quotient_spec
    (col : ProductColumn) (products : List (UInt64 × UInt64)) (q : UInt64)
    (h : col.hi.toNat + 2*products.length < 16) :
    (addColumnQuotient (addProducts col products) q).val =
      col.val + (sumProducts products + q.toNat) := by
  obtain ⟨hv, hh⟩ := addProducts_spec col products h
  rw [(addColumnQuotient_spec _ q (by omega)).1, hv, Nat.add_assoc]

private theorem addColumnQuotient_zero (col : ProductColumn) : addColumnQuotient col 0 = col := by
  cases col with
  | mk lo mid hi =>
    simp [addColumnQuotient, ProductColumn.add, yes, Bool.toUInt64]


private theorem productWithQuotient_columns (a b : Raw) (q : Words64) :
    let c0 := ((⟨0,0,0⟩ : ProductColumn)).add (wordProduct a.w0 b.w0)
    let c1 := (c0.next.add (wordProduct a.w0 b.w1)).add (wordProduct a.w1 b.w0)
    let c2 :=
      (((c1.next).add (wordProduct a.w0 b.w2)).add (wordProduct a.w1 b.w1)).add (wordProduct
        a.w2 b.w0)
    let c3 :=
      ((((c2.next).add (wordProduct a.w0 b.w3)).add (wordProduct a.w1 b.w2)).add (wordProduct
        a.w2 b.w1)).add (wordProduct a.w3 b.w0)
    let c4 :=
      addColumnQuotient ((((c3.next).add (wordProduct a.w1 b.w3)).add (wordProduct a.w2
        b.w2)).add (wordProduct a.w3 b.w1)) q.w0
    let c5 :=
      addColumnQuotient ((c4.next.add (wordProduct a.w2 b.w3)).add (wordProduct a.w3 b.w2))
        q.w1
    let c6 := addColumnQuotient (c5.next.add (wordProduct a.w3 b.w3)) q.w2
    let c7 := addColumnQuotient (c6.next) q.w3
    columnLow c0 c1 c2 c3 + wordRadix^4 *
      (columnLow c4 c5 c6 c7 + wordRadix^4 * (c7.mid.toNat + wordRadix*c7.hi.toNat)) =
      a.val * b.val + wordRadix^4 * lowValue q := by
  let c0 := ((⟨0,0,0⟩ : ProductColumn)).add (wordProduct a.w0 b.w0)
  let c1 := (c0.next.add (wordProduct a.w0 b.w1)).add (wordProduct a.w1 b.w0)
  let c2 :=
    (((c1.next).add (wordProduct a.w0 b.w2)).add (wordProduct a.w1 b.w1)).add (wordProduct a.w2
      b.w0)
  let c3 :=
    ((((c2.next).add (wordProduct a.w0 b.w3)).add (wordProduct a.w1 b.w2)).add (wordProduct a.w2
      b.w1)).add (wordProduct a.w3 b.w0)
  let c4 :=
    addColumnQuotient ((((c3.next).add (wordProduct a.w1 b.w3)).add (wordProduct a.w2 b.w2)).add
      (wordProduct a.w3 b.w1)) q.w0
  let c5 :=
    addColumnQuotient ((c4.next.add (wordProduct a.w2 b.w3)).add (wordProduct a.w3 b.w2)) q.w1
  let c6 := addColumnQuotient (c5.next.add (wordProduct a.w3 b.w3)) q.w2
  let c7 := addColumnQuotient (c6.next) q.w3
  have h0 : c0.val = rawCoefficient0 a b := by
    have h := (addProducts_spec (⟨0,0,0⟩ : ProductColumn) [(a.w0, b.w0)]
      (by change 0 + 2*1 < 16; decide)).1
    change c0.val = 0 + (a.w0.toNat*b.w0.toNat + 0) at h
    simpa only [addProducts, sumProducts, Nat.add_zero, rawCoefficient0, Nat.zero_add] using h
  have h1 : c1.val = c0.next.val + rawCoefficient1 a b := by
    have h := (addProducts_spec c0.next [(a.w0, b.w1), (a.w1, b.w0)]
      (by change 0 + 2*2 < 16; decide)).1
    simpa only [addProducts, sumProducts, Nat.add_zero, rawCoefficient1] using h
  have h2 : c2.val = c1.next.val + rawCoefficient2 a b := by
    have h := (addProducts_spec c1.next [(a.w0, b.w2), (a.w1, b.w1), (a.w2, b.w0)]
      (by change 0 + 2*3 < 16; decide)).1
    simpa only [addProducts, sumProducts, Nat.add_zero, rawCoefficient2, Nat.add_assoc] using h
  have h3 : c3.val = c2.next.val + rawCoefficient3 a b := by
    have h := (addProducts_spec c2.next [(a.w0, b.w3), (a.w1, b.w2), (a.w2, b.w1), (a.w3, b.w0)]
      (by change 0 + 2*4 < 16; decide)).1
    simpa only [addProducts, sumProducts, Nat.add_zero, rawCoefficient3, Nat.add_assoc] using h
  have h4 : c4.val = c3.next.val + (rawCoefficient4 a b + q.w0.toNat) := by
    have h := addProducts_quotient_spec c3.next [(a.w1, b.w3), (a.w2, b.w2), (a.w3, b.w1)] q.w0
      (by change 0 + 2*3 < 16; decide)
    simpa only [addProducts, sumProducts, Nat.add_zero, rawCoefficient4, Nat.add_assoc] using h
  have h5 : c5.val = c4.next.val + (rawCoefficient5 a b + q.w1.toNat) := by
    have h := addProducts_quotient_spec c4.next [(a.w2, b.w3), (a.w3, b.w2)] q.w1
      (by change 0 + 2*2 < 16; decide)
    simpa only [addProducts, sumProducts, Nat.add_zero, rawCoefficient5] using h
  have h6 : c6.val = c5.next.val + (rawCoefficient6 a b + q.w2.toNat) := by
    have h := addProducts_quotient_spec c5.next [(a.w3, b.w3)] q.w2 (by change 0 + 2*1 < 16; decide)
    simpa only [addProducts, sumProducts, Nat.add_zero, rawCoefficient6] using h
  have h7 : c7.val = c6.next.val + q.w3.toNat := by
    have h := addProducts_quotient_spec c6.next [] q.w3 (by change 0 + 2*0 < 16; decide)
    simpa only [addProducts, sumProducts, Nat.zero_add] using h
  have h := columnScan_balance c0 c1 c2 c3 c4 c5 c6 c7 _ _ _ _ _ _ _ _
    h0 h1 h2 h3 h4 h5 h6 h7
  change columnLow c0 c1 c2 c3 + wordRadix^4 *
    (columnLow c4 c5 c6 c7 + wordRadix^4*(c7.mid.toNat + wordRadix*c7.hi.toNat)) =
      a.val*b.val + wordRadix^4*lowValue q
  rw [h, rawCoefficients_balance]
  simp only [lowValue, Nat.mul_add, wordRadix]
  omega

/-- Compute the signed Montgomery accumulator by scanning product columns.

The first four columns determine the quotient that cancels the low words.

The high columns absorb the quotient words and the remaining borrow.

The top word holds the signed carry in two's complement.
-/
@[inline] def scanProductDiff (a b c d : Raw) : Words64 :=
  let p0 := ((⟨0,0,0⟩ : ProductColumn)).add (wordProduct a.w0 b.w0)
  let n0 := ((⟨0,0,0⟩ : ProductColumn)).add (wordProduct c.w0 d.w0)
  let q0 := cancelDifferenceColumn p0.lo n0.lo 0
  let p1 := ((p0.next).add (wordProduct a.w0 b.w1)).add (wordProduct a.w1 b.w0)
  let n1 := ((n0.next).add (wordProduct c.w0 d.w1)).add (wordProduct c.w1 d.w0)
  let q1 := cancelDifferenceColumn p1.lo n1.lo q0.hi
  let p2 :=
    (((p1.next).add (wordProduct a.w0 b.w2)).add (wordProduct a.w1 b.w1)).add (wordProduct a.w2
      b.w0)
  let n2 :=
    (((n1.next).add (wordProduct c.w0 d.w2)).add (wordProduct c.w1 d.w1)).add (wordProduct c.w2
      d.w0)
  let q2 := cancelDifferenceColumn p2.lo n2.lo q1.hi
  let p3 :=
    ((((p2.next).add (wordProduct a.w0 b.w3)).add (wordProduct a.w1 b.w2)).add (wordProduct a.w2
      b.w1)).add (wordProduct a.w3 b.w0)
  let n3 :=
    ((((n2.next).add (wordProduct c.w0 d.w3)).add (wordProduct c.w1 d.w2)).add (wordProduct c.w2
      d.w1)).add (wordProduct c.w3 d.w0)
  let q3 := cancelDifferenceColumn p3.lo n3.lo q2.hi
  let p4 :=
    addColumnQuotient ((((p3.next).add (wordProduct a.w1 b.w3)).add (wordProduct a.w2 b.w2)).add
      (wordProduct a.w3 b.w1)) q0.lo
  let n4 :=
    (((n3.next).add (wordProduct c.w1 d.w3)).add (wordProduct c.w2 d.w2)).add (wordProduct c.w3
      d.w1)
  let z0 := subtractColumnCarry p4.lo n4.lo q3.hi
  let p5 :=
    addColumnQuotient (((p4.next).add (wordProduct a.w2 b.w3)).add (wordProduct a.w3 b.w2))
      q1.lo
  let n5 := ((n4.next).add (wordProduct c.w2 d.w3)).add (wordProduct c.w3 d.w2)
  let z1 := subtractColumnCarry p5.lo n5.lo z0.hi
  let p6 := addColumnQuotient ((p5.next).add (wordProduct a.w3 b.w3)) q2.lo
  let n6 := (n5.next).add (wordProduct c.w3 d.w3)
  let z2 := subtractColumnCarry p6.lo n6.lo z1.hi
  let p7 := addColumnQuotient (p6.next) q3.lo
  let n7 := n6.next
  let z3 := subtractColumnCarry p7.lo n7.lo z2.hi
  ⟨z0.lo, z1.lo, z2.lo, z3.lo, p7.mid - n7.mid - z3.hi⟩

/-- The scan gives a bounded signed accumulator and a witness for its Montgomery congruence. -/
theorem scanProductDiff_spec (a b c d : Montgomery) :
    (2^256 - Fp.modulus ≤ value (bias (scanProductDiff a.raw b.raw c.raw d.raw)) ∧
      value (bias (scanProductDiff a.raw b.raw c.raw d.raw)) < 2 * Fp.modulus + 2^256) ∧
    ∃ q, 2^256 * value (bias (scanProductDiff a.raw b.raw c.raw d.raw)) + c.raw.val*d.raw.val =
      a.raw.val*b.raw.val + q*Fp.modulus + (2^256)*(2^256) := by
  let A := a.raw
  let B := b.raw
  let C := c.raw
  let D := d.raw
  let p0 := ((⟨0,0,0⟩ : ProductColumn)).add (wordProduct A.w0 B.w0)
  let n0 := ((⟨0,0,0⟩ : ProductColumn)).add (wordProduct C.w0 D.w0)
  let q0 := cancelDifferenceColumn p0.lo n0.lo 0
  let p1 := ((p0.next).add (wordProduct A.w0 B.w1)).add (wordProduct A.w1 B.w0)
  let n1 := ((n0.next).add (wordProduct C.w0 D.w1)).add (wordProduct C.w1 D.w0)
  let q1 := cancelDifferenceColumn p1.lo n1.lo q0.hi
  let p2 :=
    (((p1.next).add (wordProduct A.w0 B.w2)).add (wordProduct A.w1 B.w1)).add (wordProduct A.w2
      B.w0)
  let n2 :=
    (((n1.next).add (wordProduct C.w0 D.w2)).add (wordProduct C.w1 D.w1)).add (wordProduct C.w2
      D.w0)
  let q2 := cancelDifferenceColumn p2.lo n2.lo q1.hi
  let p3 :=
    ((((p2.next).add (wordProduct A.w0 B.w3)).add (wordProduct A.w1 B.w2)).add (wordProduct A.w2
      B.w1)).add (wordProduct A.w3 B.w0)
  let n3 :=
    ((((n2.next).add (wordProduct C.w0 D.w3)).add (wordProduct C.w1 D.w2)).add (wordProduct C.w2
      D.w1)).add (wordProduct C.w3 D.w0)
  let q3 := cancelDifferenceColumn p3.lo n3.lo q2.hi
  let p4 :=
    addColumnQuotient ((((p3.next).add (wordProduct A.w1 B.w3)).add (wordProduct A.w2 B.w2)).add
      (wordProduct A.w3 B.w1)) q0.lo
  let n4 :=
    (((n3.next).add (wordProduct C.w1 D.w3)).add (wordProduct C.w2 D.w2)).add (wordProduct C.w3
      D.w1)
  let z0 := subtractColumnCarry p4.lo n4.lo q3.hi
  let p5 :=
    addColumnQuotient (((p4.next).add (wordProduct A.w2 B.w3)).add (wordProduct A.w3 B.w2))
      q1.lo
  let n5 := ((n4.next).add (wordProduct C.w2 D.w3)).add (wordProduct C.w3 D.w2)
  let z1 := subtractColumnCarry p5.lo n5.lo z0.hi
  let p6 := addColumnQuotient ((p5.next).add (wordProduct A.w3 B.w3)) q2.lo
  let n6 := (n5.next).add (wordProduct C.w3 D.w3)
  let z2 := subtractColumnCarry p6.lo n6.lo z1.hi
  let p7 := addColumnQuotient (p6.next) q3.lo
  let n7 := n6.next
  let z3 := subtractColumnCarry p7.lo n7.lo z2.hi
  let Q : Words64 := ⟨q0.lo,q1.lo,q2.lo,q3.lo,0⟩
  have hp := productWithQuotient_columns A B Q
  have hn : columnLow n0 n1 n2 n3 + wordRadix^4 *
      (columnLow n4 n5 n6 n7 + wordRadix^4 * (n7.mid.toNat + wordRadix*n7.hi.toNat)) =
      C.val * D.val := by
    have h := productWithQuotient_columns C D ⟨0,0,0,0,0⟩
    dsimp only at h
    rw [addColumnQuotient_zero, addColumnQuotient_zero, addColumnQuotient_zero,
      addColumnQuotient_zero] at h
    have hz : lowValue ⟨0,0,0,0,0⟩ = 0 := by decide
    rw [hz, Nat.mul_zero, Nat.add_zero] at h
    exact h
  have hAB := Nat.mul_lt_mul'' a.lt b.lt
  have hCD := Nat.mul_lt_mul'' c.lt d.lt
  have hc := combineCancel p0 p1 p2 p3 n0 n1 n2 n3
  have hd := combineDifference p4 p5 p6 p7 n4 n5 n6 n7 q3.hi
  let t : Words64 := ⟨z0.lo,z1.lo,z2.lo,z3.lo,p7.mid-n7.mid-z3.hi⟩
  change (2^256 - Fp.modulus ≤ value (bias t) ∧
      value (bias t) < 2 * Fp.modulus + 2^256) ∧
    ∃ q, 2^256 * value (bias t) + c.raw.val*d.raw.val =
      a.raw.val*b.raw.val + q*Fp.modulus + (2^256)*(2^256)
  exact finishColumns_balance _ _ _ _ (lowValue Q) q3.hi.toNat _ _
    p7.mid p7.hi n7.mid n7.hi z3.hi z0.lo z1.lo z2.lo z3.lo
    hAB hCD (lowValue_lt Q) hp hn hc hd

/-- Compute the difference of two products with one shared Montgomery reduction. -/
@[inline] def productDiff (a b c d : @& Montgomery) : Montgomery :=
  let t := scanProductDiff a.raw b.raw c.raw d.raw
  let h := (scanProductDiff_spec a b c d).1
  fusedFinish t h.1 h.2

/-- Subtract a square in the same Montgomery stages as the positive product. -/
@[inline] def fusedSquareAccum (a b c : Raw) : Words64 :=
  let p00 := wordProduct c.w0 c.w0
  let p01 := wordProduct c.w0 c.w1
  let p02 := wordProduct c.w0 c.w2
  let p03 := wordProduct c.w0 c.w3
  let p11 := wordProduct c.w1 c.w1
  let p12 := wordProduct c.w1 c.w2
  let p13 := wordProduct c.w1 c.w3
  let p22 := wordProduct c.w2 c.w2
  let p23 := wordProduct c.w2 c.w3
  let p33 := wordProduct c.w3 c.w3
  fusedStageProducts a b.w3 p03 p13 p23 p33
    (fusedStageProducts a b.w2 p02 p12 p22 p23 (fusedStageProducts a b.w1 p01 p11 p12 p13
      (fusedStageProducts a b.w0 p00 p01 p02 p03 ⟨0,0,0,0,0⟩)))

private theorem fusedSquareAccum_eq (a b c : Raw) :
    fusedSquareAccum a b c = fusedAccum a b c c := by
  simp only [fusedSquareAccum, fusedAccum, ← fusedStageProducts_eq_stage]
  rw [← wordProduct_comm c.w0 c.w1, ← wordProduct_comm c.w0 c.w2,
    ← wordProduct_comm c.w0 c.w3, ← wordProduct_comm c.w1 c.w2,
    ← wordProduct_comm c.w1 c.w3, ← wordProduct_comm c.w2 c.w3]

/-- Compute a product minus a square with one shared Montgomery reduction. -/
@[inline] def productSubSquare (a b c : @& Montgomery) : Montgomery :=
  let t := fusedSquareAccum a.raw b.raw c.raw
  let h := (fusedAccum_spec a.raw b.raw c.raw c.raw a.lt c.lt).1
  fusedFinish t (by simpa only [t, fusedSquareAccum_eq] using h.1)
    (by simpa only [t, fusedSquareAccum_eq] using h.2)

end Montgomery



end EthLib.Cryptography.Secp256k1
