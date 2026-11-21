module

public import EthLib.Cryptography.Secp256r1.Field
public import EthLib.Cryptography.Word64

/-!
# `Secp256r1.Montgomery`

The base field of secp256r1 in Montgomery form, on four 64-bit words, with `R = 2^256`.

An element holds `a R mod p`, below `p`, so equality of words is equality in the field.

A product interleaves each row of word products with one step of Montgomery reduction.

That is the CIOS method of [Koç, Acar and Kaliski][cios], after [Montgomery (1985)][redc].

Since `-p^(-1) mod 2^64` is `1`, the multiple of `p` that a step adds is the low word itself.

The words of `p` turn that multiple into shifts and sums, so the reduction is specific to `p`.

That is why this form sits beside the Montgomery field on 32-bit limbs that other curves share.

A sum, a difference and a product each end with at most one correction by `p`.

The inverse goes through `Fp`, since it runs once for each scalar multiplication.

[redc]: <https://doi.org/10.1090/S0025-5718-1985-0777282-X>

[cios]: <https://doi.org/10.1109/40.502403>
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

open Word64

namespace Montgomery

-- The integers of four and five words, written with their powers of two.

private theorem raw_val (t : Raw) :
    t.val = t.w0.toNat + 2^64 * t.w1.toNat + 2^128 * t.w2.toNat + 2^192 * t.w3.toNat := by
  simp only [Raw.val, Raw.words, lowValue, wordRadix]

private theorem words_value (t : Words64) :
    value t = t.w0.toNat + 2^64 * t.w1.toNat + 2^128 * t.w2.toNat + 2^192 * t.w3.toNat +
      2^256 * t.top.toNat := by
  simp only [value, lowValue, wordRadix]

/-! ## One correction by `p` -/

/-- `p` in four words, least significant first.

They are `2^64 - 1`, `2^32 - 1`, `0` and `2^64 - 2^32 + 1`. -/
@[inline] def modulusWords : Raw := ⟨0xffffffffffffffff, 0xffffffff, 0, 0xffffffff00000001⟩

private theorem modulusWords_low : lowValue modulusWords.words = Fp.modulus := by decide

/-- `t mod p`, for `t < 2 p`: `t` itself, or `t - p`. -/
@[inline] def reduceOnce (t : Words64) : Raw :=
  let d := sub4 t modulusWords.words
  -- `t < p` exactly when no carry sits above bit 255 and the subtraction borrows.
  if t.top < d.top then Raw.fromWords t else Raw.fromWords d

/-- The correction gives the remainder mod `p`. -/
theorem reduceOnce_val (t : Words64) (h : value t < 2 * Fp.modulus) :
    (reduceOnce t).val = value t % Fp.modulus := by
  have hs := sub4_spec t modulusWords.words
  rw [modulusWords_low] at hs
  have hl := lowValue_lt t
  have hd := lowValue_lt (sub4 t modulusWords.words)
  have hp : Fp.modulus < 2^256 ∧ 2^256 ≤ 2 * Fp.modulus := by decide
  simp only [reduceOnce]
  generalize sub4 t modulusWords.words = d at *
  simp only [value, wordRadix] at h ⊢
  simp only [wordRadix] at hl hd
  split
  · rename_i hc
    have hc' : t.top.toNat < d.top.toNat := hc
    rw [Raw.fromWords_val_low, Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i hc
    have hc' : ¬ t.top.toNat < d.top.toNat := hc
    rw [Raw.fromWords_val_low, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## Sum and difference -/

/-- `a + b mod p`, for `a, b < p`. -/
@[inline] def addRaw (a b : Raw) : Raw := reduceOnce (add4 a.words b.words)

/-- The words of a sum hold the sum mod `p`. -/
theorem addRaw_val (a b : Raw) (ha : a.val < Fp.modulus) (hb : b.val < Fp.modulus) :
    (addRaw a b).val = (a.val + b.val) % Fp.modulus := by
  have hs := (add4_spec a.words b.words).1
  rw [show lowValue a.words = a.val from rfl, show lowValue b.words = b.val from rfl] at hs
  unfold addRaw
  rw [reduceOnce_val _ (by rw [hs]; omega), hs]

/-- `a - b mod p`, for `a, b < p`. -/
@[inline] def subRaw (a b : Raw) : Raw :=
  let d := sub4 a.words b.words
  -- `a < b`: the words hold `a - b + 2^256`, and adding `p` wraps to `a - b + p`.
  if d.top = 0 then Raw.fromWords d else Raw.fromWords (add4 d modulusWords.words)

/-- The words of a difference hold the difference mod `p`. -/
theorem subRaw_val (a b : Raw) (ha : a.val < Fp.modulus) (hb : b.val < Fp.modulus) :
    (subRaw a b).val = (a.val + (Fp.modulus - b.val)) % Fp.modulus := by
  have hs := sub4_spec a.words b.words
  rw [show lowValue a.words = a.val from rfl, show lowValue b.words = b.val from rfl] at hs
  have hd := lowValue_lt (sub4 a.words b.words)
  have he := add4_spec (sub4 a.words b.words) modulusWords.words
  have hel := lowValue_lt (add4 (sub4 a.words b.words) modulusWords.words)
  rw [modulusWords_low] at he
  have hp : Fp.modulus < 2^256 := by decide
  simp only [subRaw]
  generalize add4 (sub4 a.words b.words) modulusWords.words = e at *
  generalize sub4 a.words b.words = d at *
  simp only [value, wordRadix] at he
  simp only [wordRadix] at hd hel
  split
  · rename_i hc
    have hc' : d.top.toNat = 0 := by rw [hc]; rfl
    rw [Raw.fromWords_val_low, show a.val + (Fp.modulus - b.val) = a.val - b.val + Fp.modulus by
      omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i hc
    have hc' : d.top.toNat ≠ 0 := fun h => hc (UInt64.toNat_inj.mp (by rw [h]; rfl))
    rw [Raw.fromWords_val_low, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## Product -/

/-- One row of a product: add `a x`, then add the multiple of `p` that clears the low word.

The low word is then dropped, which divides by `2^64`. -/
@[inline] def row (a : Raw) (x : UInt64) (t : Words64) : Words64 :=
  let u0 := mac a.w0 x t.w0 0
  let u1 := mac a.w1 x t.w1 u0.hi
  let u2 := mac a.w2 x t.w2 u1.hi
  let u3 := mac a.w3 x t.w3 u2.hi
  let u4 := plus t.top u3.hi 0
  -- The multiple is `m p`, with `m` the low word, since `-p^(-1) = 1 mod 2^64`.
  --
  -- The low word of `p` is `2^64 - 1`, so the low word plus `m (2^64 - 1)` is `m 2^64`.
  --
  -- It clears, and carries `m` into the next word.
  let m := u0.lo
  -- That carry and `m (2^32 - 1)` make `m 2^32`, split into `lo` and `hi` at bit 64.
  let lo := m <<< 32
  let hi := m >>> 32
  let v1 := plus u1.lo lo 0
  let v2 := plus u2.lo hi v1.hi
  -- The top word of `p` is `2^64 - 2^32 + 1`, and `m` times it is `2^64 (m - hi) + m - lo`.
  --
  -- When `m < lo`, the low part borrows one from the high part.
  let d := minus m lo 0
  let v3 := plus u3.lo d.lo v2.hi
  let v4 := plus u4.lo (m - hi - d.hi) v3.hi
  ⟨v1.lo, v2.lo, v3.lo, v4.lo, u4.hi + v4.hi⟩

/-- A row adds `a x` and a multiple of `p`, then divides by `2^64`, and stays below `2 p`. -/
theorem row_spec (a : Raw) (x : UInt64) (t : Words64) (ha : a.val < Fp.modulus)
    (ht : value t < 2 * Fp.modulus) :
    value (row a x t) < 2 * Fp.modulus ∧
      ∃ m : Nat, 2^64 * value (row a x t) = value t + a.val * x.toNat + m * Fp.modulus := by
  have e0 := mac_spec a.w0 x t.w0 0
  have e1 := mac_spec a.w1 x t.w1 (mac a.w0 x t.w0 0).hi
  have e2 := mac_spec a.w2 x t.w2 (mac a.w1 x t.w1 (mac a.w0 x t.w0 0).hi).hi
  have e3 := mac_spec a.w3 x t.w3 (mac a.w2 x t.w2 (mac a.w1 x t.w1 (mac a.w0 x t.w0 0).hi).hi).hi
  simp only [row]
  generalize mac a.w0 x t.w0 0 = u0 at *
  generalize mac a.w1 x t.w1 u0.hi = u1 at *
  generalize mac a.w2 x t.w2 u1.hi = u2 at *
  generalize mac a.w3 x t.w3 u2.hi = u3 at *
  have e4 := plus_spec t.top u3.hi 0 (by decide)
  generalize plus t.top u3.hi 0 = u4 at *
  have hm := u0.lo.toNat_lt
  have hlo : (u0.lo <<< 32).toNat = u0.lo.toNat * 2^32 % 2^64 := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    rfl
  have hhi : (u0.lo >>> 32).toNat = u0.lo.toNat / 2^32 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  -- `m 2^32` in two words.
  have hsplit : (u0.lo <<< 32).toNat + 2^64 * (u0.lo >>> 32).toNat = u0.lo.toNat * 2^32 := by
    rw [hlo, hhi]
    omega
  have hhm : (u0.lo >>> 32).toNat ≤ u0.lo.toNat := by
    rw [hhi]
    exact Nat.div_le_self _ _
  clear hlo hhi
  generalize u0.lo <<< 32 = lo at *
  generalize u0.lo >>> 32 = hi at *
  have f1 := plus_spec u1.lo lo 0 (by decide)
  generalize plus u1.lo lo 0 = v1 at *
  have f2 := plus_spec u2.lo hi v1.hi f1.2
  generalize plus u2.lo hi v1.hi = v2 at *
  have fd := minus_spec u0.lo lo 0 (by decide)
  generalize minus u0.lo lo 0 = d at *
  have f3 := plus_spec u3.lo d.lo v2.hi f2.2
  generalize plus u3.lo d.lo v2.hi = v3 at *
  -- The high part of `m` times the top word of `p` does not wrap.
  have hdl := d.lo.toNat_lt
  have hll := lo.toNat_lt
  have hhigh : (u0.lo - hi - d.hi).toNat = u0.lo.toNat - hi.toNat - d.hi.toNat := by
    simp only [UInt64.toNat_zero, wordRadix, Nat.add_zero] at fd
    have hb : hi.toNat + d.hi.toNat ≤ u0.lo.toNat := by omega
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr hhm)]; omega), UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr hhm)]
  have f4 := plus_spec u4.lo (u0.lo - hi - d.hi) v3.hi f3.2
  generalize plus u4.lo (u0.lo - hi - d.hi) v3.hi = v4 at *
  have htop : (u4.hi + v4.hi).toNat = u4.hi.toNat + v4.hi.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hx := x.toNat_lt
  -- The row as an equation of integers, with `m` the low word.
  have key : 2^64 * value (Words64.mk v1.lo v2.lo v3.lo v4.lo (u4.hi + v4.hi)) =
      value t + a.val * x.toNat + u0.lo.toNat * Fp.modulus := by
    have hax : a.val * x.toNat = a.w0.toNat * x.toNat + 2^64 * (a.w1.toNat * x.toNat) +
        2^128 * (a.w2.toNat * x.toNat) + 2^192 * (a.w3.toNat * x.toNat) := by
      simp only [raw_val, Nat.add_mul, Nat.mul_assoc]
    rw [hax]
    simp only [words_value, htop, Fp.modulus, wordRadix, UInt64.toNat_zero] at *
    omega
  refine ⟨?_, u0.lo.toNat, key⟩
  -- `2^64 t' = t + a x + m p < 2 p + p (2^64 - 1) + (2^64 - 1) p = 2^65 p`.
  have hax : a.val * x.toNat ≤ (Fp.modulus - 1) * (2^64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hmp : u0.lo.toNat * Fp.modulus ≤ (2^64 - 1) * Fp.modulus :=
    Nat.mul_le_mul_right _ (by omega)
  have hp : 0 < Fp.modulus := by decide
  omega

/-- The rows of `a b`, before the last correction: one row for each word of `b`. -/
@[inline] def mulAcc (a b : Raw) : Words64 :=
  row a b.w3 (row a b.w2 (row a b.w1 (row a b.w0 ⟨0, 0, 0, 0, 0⟩)))

/-- The rows give `a b` plus a multiple of `p`, divided by `2^256`, and stay below `2 p`. -/
theorem mulAcc_spec (a b : Raw) (ha : a.val < Fp.modulus) :
    value (mulAcc a b) < 2 * Fp.modulus ∧
      ∃ m : Nat, 2^256 * value (mulAcc a b) = a.val * b.val + m * Fp.modulus := by
  have h0 : value (Words64.mk 0 0 0 0 0) < 2 * Fp.modulus := by decide
  obtain ⟨b1, m0, e0⟩ := row_spec a b.w0 _ ha h0
  obtain ⟨b2, m1, e1⟩ := row_spec a b.w1 _ ha b1
  obtain ⟨b3, m2, e2⟩ := row_spec a b.w2 _ ha b2
  obtain ⟨b4, m3, e3⟩ := row_spec a b.w3 _ ha b3
  refine ⟨b4, m0 + 2^64 * m1 + 2^128 * m2 + 2^192 * m3, ?_⟩
  have hz : value (Words64.mk 0 0 0 0 0) = 0 := by decide
  have hb : a.val * b.val = a.val * b.w0.toNat + 2^64 * (a.val * b.w1.toNat) +
      2^128 * (a.val * b.w2.toNat) + 2^192 * (a.val * b.w3.toNat) := by
    rw [show b.val = b.w0.toNat + 2^64 * b.w1.toNat + 2^128 * b.w2.toNat +
      2^192 * b.w3.toNat from rfl]
    simp only [Nat.mul_add, Nat.mul_left_comm a.val]
  have hm : (m0 + 2^64 * m1 + 2^128 * m2 + 2^192 * m3) * Fp.modulus =
      m0 * Fp.modulus + 2^64 * (m1 * Fp.modulus) + 2^128 * (m2 * Fp.modulus) +
        2^192 * (m3 * Fp.modulus) := by
    simp only [Nat.add_mul, Nat.mul_assoc]
  rw [hb, hm]
  simp only [mulAcc]
  rw [hz] at e0
  omega

end Montgomery

/-- An element of the base field in Montgomery form, with `R = 2^256`.

The words hold `a R mod p`, below `p`, so each element has one encoding. -/
abbrev Montgomery := Word64.Montgomery Fp.modulus

namespace Montgomery

/-- The Montgomery constants of `p`: `R mod p` and `R^2 mod p`. -/
instance : Word64.Montgomery.Constants Fp.modulus where
  -- `R mod p = 2^224 - 2^192 - 2^96 + 1`.
  one := ⟨1, 0xffffffff00000000, 0xffffffffffffffff, 0xfffffffe⟩
  square := ⟨3, 0xfffffffbffffffff, 0xfffffffffffffffe, 0x4fffffffd⟩
  bounds := by decide
  one_val := by decide
  square_val := by decide

/-- The sum of two elements. -/
@[inline] def add (a b : @& Montgomery) : Montgomery :=
  ⟨addRaw a.raw b.raw, by
    rw [addRaw_val _ _ a.lt b.lt]
    exact Nat.mod_lt _ (by decide)⟩

/-- The difference of two elements. -/
@[inline] def sub (a b : @& Montgomery) : Montgomery :=
  ⟨subRaw a.raw b.raw, by
    rw [subRaw_val _ _ a.lt b.lt]
    exact Nat.mod_lt _ (by decide)⟩

/-- The Montgomery product `a b / R mod p`, which is the product of the elements. -/
@[inline] def mul (a b : @& Montgomery) : Montgomery :=
  ⟨reduceOnce (mulAcc a.raw b.raw), by
    rw [reduceOnce_val _ (mulAcc_spec a.raw b.raw a.lt).1]
    exact Nat.mod_lt _ (by decide)⟩

instance : Add Montgomery := ⟨add⟩
instance : Sub Montgomery := ⟨sub⟩
instance : Mul Montgomery := ⟨mul⟩

/-- Enter the Montgomery form with a product by `R^2 mod p`. -/
abbrev ofFin (a : Fp) : Montgomery := Word64.Montgomery.ofFin a

/-- Leave the Montgomery form with a product by the integer one. -/
abbrev toFin (a : Montgomery) : Fp := Word64.Montgomery.toFin a

/-- The inverse, through the extended Euclidean algorithm on `Fp`, and 0 for 0. -/
def inv (a : Montgomery) : Montgomery := ofFin (Fin.inverse (toFin a))

end Montgomery

end EthLib.Cryptography.Secp256r1
