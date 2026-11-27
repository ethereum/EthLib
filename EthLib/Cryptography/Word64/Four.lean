module

public import EthLib.Cryptography.Word64

/-!
# Arithmetic mod `p` on four 64-bit words

The sum, the difference and the Montgomery product `a b R⁻¹ mod p`, with `R = 2^256`.

The modulus is odd and below `2^255`.

The product is the CIOS method of [Koç, Acar and Kaliski][cios], with words of 64 bits.

[cios]: https://doi.org/10.1109/40.502403
-/

@[expose] public section

namespace EthLib.Cryptography.Word64

/--
One row of the CIOS product: `(t + a x + m p) / 2^64`.

The multiple `m` of `p` is the one that clears the low word of the sum.

`pinv` is `-p⁻¹ mod 2^64`.
-/
@[inline] def row4 (p : Raw) (pinv : UInt64) (a : Raw) (x : UInt64) (t : Words64) : Words64 :=
  -- The multiplication loop: `(C, S) := t[j] + a[j] x + C`, for `j` from 0 to 3.
  let u0 := mac a.w0 x t.w0 0
  let u1 := mac a.w1 x t.w1 u0.hi
  let u2 := mac a.w2 x t.w2 u1.hi
  let u3 := mac a.w3 x t.w3 u2.hi
  -- `(C, S) := t[4] + C`, then `t[4] := S` and `t[5] := C`.
  let u4 := plus t.top u3.hi 0
  -- `m := t[0] pinv mod 2^64`.
  let m := u0.lo * pinv
  -- The reduction loop: `(C, S) := t[j] + m p[j] + C`, and the low word of `j = 0` is zero.
  let v0 := mac m p.w0 u0.lo 0
  let v1 := mac m p.w1 u1.lo v0.hi
  let v2 := mac m p.w2 u2.lo v1.hi
  let v3 := mac m p.w3 u3.lo v2.hi
  -- The words move down by one: `t[j - 1] := S`, and the top takes both carries.
  let v4 := plus u4.lo v3.hi 0
  ⟨v1.lo, v2.lo, v3.lo, v4.lo, u4.hi + v4.hi⟩

/-- `t - p` when `t ≥ p`, else `t`, for a state below `2 p`. -/
@[inline] def reduce4 (p : Raw) (t : Words64) : Raw :=
  -- Step 3 of CIOS: the result is `t - p` when `t ≥ p`, and `t` otherwise.
  let d := sub4 t p.words
  -- `t < p` exactly when the subtraction borrows more than the top word holds.
  if t.top < d.top then Raw.fromWords t else Raw.fromWords d

/-- The Montgomery product `a b 2^(-256) mod p`, for `a` below `p`. -/
@[inline] def mul4 (p : Raw) (pinv : UInt64) (a b : Raw) : Raw :=
  -- One row for each word of `b`, from the lowest, starting from zero.
  let t : Words64 := ⟨0, 0, 0, 0, 0⟩
  let t := row4 p pinv a b.w0 t
  let t := row4 p pinv a b.w1 t
  let t := row4 p pinv a b.w2 t
  let t := row4 p pinv a b.w3 t
  reduce4 p t

/-- The words of `t` where the mask `m` is set. -/
@[inline] def Raw.mask (t : Raw) (m : UInt64) : Raw :=
  ⟨t.w0 &&& m, t.w1 &&& m, t.w2 &&& m, t.w3 &&& m⟩

/-- The low words of `d`, plus `p` mod `2^256` when the top word of `d` is a borrow of one. -/
@[inline] def addBack4 (p : Raw) (d : Words64) : Raw :=
  -- All ones on a borrow, and zero otherwise, so `p` is added with no branch.
  let m := 0 - d.top
  -- The carry of this sum cancels the borrow.
  Raw.fromWords (add4 d (p.mask m).words)

/-- `a + b mod p`, for `a` and `b` below `p` and `2 p < 2^256`. -/
@[inline] def addMod4 (p a b : Raw) : Raw :=
  -- The sum is below `2^256`, so it has no carry.
  let s := add4 a.words b.words
  -- `s - p`, with `p` added back when `s < p`.
  addBack4 p (sub4 s p.words)

/-- `a - b mod p`, for `a` and `b` below `p`. -/
@[inline] def subMod4 (p a b : Raw) : Raw :=
  addBack4 p (sub4 a.words b.words)

/-- Limb `k` of 32 bits: the low half of word `k / 2` for an even `k`, its high half for an odd one.

Past the last limb, it is `0`. -/
@[inline] def Raw.limb (a : Raw) : Nat → UInt64
  | 0 => a.w0 &&& 0xFFFFFFFF
  | 1 => a.w0 >>> 32
  | 2 => a.w1 &&& 0xFFFFFFFF
  | 3 => a.w1 >>> 32
  | 4 => a.w2 &&& 0xFFFFFFFF
  | 5 => a.w2 >>> 32
  | 6 => a.w3 &&& 0xFFFFFFFF
  | 7 => a.w3 >>> 32
  | _ => 0

/-! ## Proofs -/

/-- The integer of four words, as a sum of powers of `2^64`. -/
theorem Raw.val_eq_sum (t : Raw) :
    t.val = t.w0.toNat + 2^64 * t.w1.toNat + 2^128 * t.w2.toNat + 2^192 * t.w3.toNat := by
  simp only [Raw.val, Raw.words, lowValue, wordRadix]

/-- Four words are below `2^256`. -/
theorem Raw.val_lt (t : Raw) : t.val < 2^256 := lowValue_lt t.words

/-- Each limb is below `2^32`. -/
theorem Raw.limb_lt (a : Raw) (k : Nat) : (a.limb k).toNat < 2^32 := by
  have := a.w0.toNat_lt
  have := a.w1.toNat_lt
  have := a.w2.toNat_lt
  have := a.w3.toNat_lt
  unfold Raw.limb
  split <;> simp only [low_toNat, high_toNat, UInt64.toNat_zero] <;> omega

/-- A row adds `a x` and a multiple of `p`, divides by `2^64`, and stays below `2 p`. -/
theorem row4_spec {p : Raw} {pinv : UInt64} (hpinv : (p.val * pinv.toNat + 1) % 2^64 = 0)
    {a : Raw} (ha : a.val < p.val) (x : UInt64) {t : Words64} (ht : value t < 2 * p.val) :
    value (row4 p pinv a x t) < 2 * p.val ∧
      ∃ m : Nat, 2^64 * value (row4 p pinv a x t) = value t + a.val * x.toNat + m * p.val := by
  simp only [row4]
  -- The multiplication loop.
  have e0 := mac_spec a.w0 x t.w0 0
  generalize mac a.w0 x t.w0 0 = u0 at *
  have e1 := mac_spec a.w1 x t.w1 u0.hi
  generalize mac a.w1 x t.w1 u0.hi = u1 at *
  have e2 := mac_spec a.w2 x t.w2 u1.hi
  generalize mac a.w2 x t.w2 u1.hi = u2 at *
  have e3 := mac_spec a.w3 x t.w3 u2.hi
  generalize mac a.w3 x t.w3 u2.hi = u3 at *
  have e4 := plus_spec t.top u3.hi 0 (by decide)
  generalize plus t.top u3.hi 0 = u4 at *
  -- The multiple `m` of `p` clears the low word.
  have hclear : ((u0.lo * pinv).toNat * p.w0.toNat + u0.lo.toNat) % 2^64 = 0 := by
    rw [UInt64.toNat_mul]
    refine low_clear (r := p.w1.toNat + 2^64 * p.w2.toNat + 2^128 * p.w3.toNat) ?_ hpinv
    rw [Raw.val_eq_sum]
    omega
  generalize u0.lo * pinv = m at *
  -- The reduction loop.
  have f0 := mac_spec m p.w0 u0.lo 0
  generalize mac m p.w0 u0.lo 0 = v0 at *
  have f1 := mac_spec m p.w1 u1.lo v0.hi
  generalize mac m p.w1 u1.lo v0.hi = v1 at *
  have f2 := mac_spec m p.w2 u2.lo v1.hi
  generalize mac m p.w2 u2.lo v1.hi = v2 at *
  have f3 := mac_spec m p.w3 u3.lo v2.hi
  generalize mac m p.w3 u3.lo v2.hi = v3 at *
  have f4 := plus_spec u4.lo v3.hi 0 (by decide)
  generalize plus u4.lo v3.hi 0 = v4 at *
  have hv0 : v0.lo.toNat = 0 := by
    have := v0.lo.toNat_lt
    simp only [UInt64.toNat_zero] at f0
    omega
  -- The two carries into the top word are at most one each, so they add without wrapping.
  have htop : (u4.hi + v4.hi).toNat = u4.hi.toNat + v4.hi.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by simp only [wordRadix] at e4 f4; omega)
  -- The row as an equation of integers.
  have key : 2^64 * value ⟨v1.lo, v2.lo, v3.lo, v4.lo, u4.hi + v4.hi⟩ =
      value t + a.val * x.toNat + m.toNat * p.val := by
    have hax : a.val * x.toNat = a.w0.toNat * x.toNat + 2^64 * (a.w1.toNat * x.toNat) +
        2^128 * (a.w2.toNat * x.toNat) + 2^192 * (a.w3.toNat * x.toNat) := by
      simp only [Raw.val_eq_sum, Nat.add_mul, Nat.mul_assoc]
    have hmp : m.toNat * p.val = m.toNat * p.w0.toNat + 2^64 * (m.toNat * p.w1.toNat) +
        2^128 * (m.toNat * p.w2.toNat) + 2^192 * (m.toNat * p.w3.toNat) := by
      simp only [Raw.val_eq_sum, Nat.mul_add, Nat.mul_left_comm m.toNat]
    rw [hax, hmp]
    simp only [wordRadix, UInt64.toNat_zero] at e0 e4 f0 f4
    simp only [value, lowValue, wordRadix, htop]
    omega
  refine ⟨?_, m.toNat, key⟩
  -- `2^64 t' = t + a x + m p < 2 p + p (2^64 - 1) + (2^64 - 1) p = 2^65 p`.
  have hax : a.val * x.toNat ≤ p.val * (2^64 - 1) :=
    Nat.mul_le_mul (by omega) (by have := x.toNat_lt; omega)
  have hmp : m.toNat * p.val ≤ (2^64 - 1) * p.val :=
    Nat.mul_le_mul_right _ (by have := m.toNat_lt; omega)
  omega

/-- The final subtraction gives the remainder mod `p`, for a state below `2 p` and `2 p < 2^256`. -/
theorem reduce4_val {p : Raw} (hp : 2 * p.val < 2^256) {t : Words64} (ht : value t < 2 * p.val) :
    (reduce4 p t).val = value t % p.val := by
  -- The four words of the difference, with the final borrow: `d + p = t + 2^256 borrow`.
  obtain ⟨hd, hb⟩ := sub4_spec t p.words
  have hD := lowValue_lt (sub4 t p.words)
  have hT := lowValue_lt t
  rw [show lowValue p.words = p.val from rfl] at hd
  simp only [reduce4]
  simp only [value, wordRadix] at ht hd ⊢
  simp only [wordRadix] at hD hT
  split
  · rename_i hc
    have hc' : t.top.toNat < (sub4 t p.words).top.toNat := hc
    rw [Raw.fromWords_val_low]
    generalize lowValue (sub4 t p.words) = D at *
    generalize lowValue t = T at *
    generalize p.val = P at *
    -- The subtraction borrows, so `t < p`.
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i hc
    have hc' : ¬ t.top.toNat < (sub4 t p.words).top.toNat := hc
    rw [Raw.fromWords_val_low]
    generalize lowValue (sub4 t p.words) = D at *
    generalize lowValue t = T at *
    generalize p.val = P at *
    -- No borrow: `p ≤ t < 2 p`, and the words hold `t - p`.
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The product is below `p`, and it is `a b` divided by `2^256` mod `p`. -/
theorem mul4_spec {p : Raw} {pinv : UInt64} (hp : 2 * p.val < 2^256)
    (hpinv : (p.val * pinv.toNat + 1) % 2^64 = 0) {a : Raw} (ha : a.val < p.val) (b : Raw) :
    (mul4 p pinv a b).val < p.val ∧
      2^256 * (mul4 p pinv a b).val % p.val = a.val * b.val % p.val := by
  -- `p` is odd, so it is not zero.
  have hp0 : 0 < p.val := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, Nat.zero_mul] at hpinv
    exact absurd hpinv (by decide)
  have h0 : value ⟨0, 0, 0, 0, 0⟩ = 0 := by
    simp only [value, lowValue, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
  obtain ⟨b1, m0, e0⟩ := row4_spec hpinv ha b.w0 (t := ⟨0, 0, 0, 0, 0⟩) (by rw [h0]; omega)
  obtain ⟨b2, m1, e1⟩ := row4_spec hpinv ha b.w1 b1
  obtain ⟨b3, m2, e2⟩ := row4_spec hpinv ha b.w2 b2
  obtain ⟨b4, m3, e3⟩ := row4_spec hpinv ha b.w3 b3
  simp only [mul4]
  rw [reduce4_val hp b4]
  refine ⟨Nat.mod_lt _ hp0, ?_⟩
  -- The rows give `2^256 t = a b + M p`.
  have hb : a.val * b.val = a.val * b.w0.toNat + 2^64 * (a.val * b.w1.toNat) +
      2^128 * (a.val * b.w2.toNat) + 2^192 * (a.val * b.w3.toNat) := by
    rw [Raw.val_eq_sum b]
    simp only [Nat.mul_add, Nat.mul_left_comm a.val]
  have hm : (m0 + 2^64 * m1 + 2^128 * m2 + 2^192 * m3) * p.val =
      m0 * p.val + 2^64 * (m1 * p.val) + 2^128 * (m2 * p.val) + 2^192 * (m3 * p.val) := by
    simp only [Nat.add_mul, Nat.mul_assoc]
  have key : 2^256 * value (row4 p pinv a b.w3 (row4 p pinv a b.w2 (row4 p pinv a b.w1
      (row4 p pinv a b.w0 ⟨0, 0, 0, 0, 0⟩)))) =
      a.val * b.val + (m0 + 2^64 * m1 + 2^128 * m2 + 2^192 * m3) * p.val := by
    rw [h0] at e0
    omega
  -- `2^256` as an atom, so that no step tries to evaluate it.
  generalize (2:Nat)^256 = R at key ⊢
  rw [Nat.mul_mod_mod, key, Nat.add_mul_mod_self_right]

/-- The mask of a borrow keeps `t` on a borrow and clears it otherwise. -/
theorem Raw.val_mask (t : Raw) {c : UInt64} (hc : c.toNat ≤ 1) :
    (t.mask (0 - c)).val = t.val * c.toNat := by
  have h : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact Or.inl (UInt64.toNat_inj.mp h)
    · exact Or.inr (UInt64.toNat_inj.mp h)
  rcases h with rfl | rfl
  · have e (x : UInt64) : x &&& (0 - 0) = 0 := by rw [UInt64.sub_self, UInt64.and_zero]
    simp only [Raw.mask, Raw.val_eq_sum, e, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
  · -- `0 - 1` is the word of all ones.
    have hm : ((0 : UInt64) - 1).toNat = 2^64 - 1 := by decide
    have e (x : UInt64) : x &&& (0 - 1) = x := UInt64.toNat_inj.mp (by
      rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt])
    simp only [Raw.mask, e, UInt64.toNat_one, Nat.mul_one]

/-- Adding back gives `d + p` on a borrow and `d` otherwise, mod `2^256`. -/
theorem addBack4_val (p : Raw) {d : Words64} (hc : d.top.toNat ≤ 1) :
    (addBack4 p d).val = (lowValue d + p.val * d.top.toNat) % 2^256 := by
  obtain ⟨hs, -⟩ := add4_spec d (p.mask (0 - d.top)).words
  rw [show lowValue (p.mask (0 - d.top)).words = (p.mask (0 - d.top)).val from rfl,
    Raw.val_mask p hc, value] at hs
  have hl := lowValue_lt (add4 d (p.mask (0 - d.top)).words)
  simp only [addBack4, Raw.fromWords_val_low]
  generalize add4 d (p.mask (0 - d.top)).words = s at *
  simp only [wordRadix] at hs hl
  generalize (2:Nat)^256 = K at *
  rw [← hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The sum is `a + b` mod `p`. -/
theorem addMod4_spec {p : Raw} (hp : 2 * p.val < 2^256) {a b : Raw} (ha : a.val < p.val)
    (hb : b.val < p.val) : (addMod4 p a b).val = (a.val + b.val) % p.val := by
  -- The sum is below `2 p < 2^256`, so it has no carry.
  obtain ⟨hs, -⟩ := add4_spec a.words b.words
  have hS : lowValue (add4 a.words b.words) = a.val + b.val := by
    have hl := lowValue_lt (add4 a.words b.words)
    have hab : a.val + b.val < 2^256 := by omega
    rw [value, show lowValue a.words = a.val from rfl, show lowValue b.words = b.val from rfl]
      at hs
    generalize add4 a.words b.words = s at *
    simp only [wordRadix] at hs hl
    generalize (2:Nat)^256 = K at *
    rw [← Nat.mod_eq_of_lt hl, ← Nat.add_mul_mod_self_left, hs, Nat.mod_eq_of_lt hab]
  obtain ⟨hd, hbor⟩ := sub4_spec (add4 a.words b.words) p.words
  have hD := lowValue_lt (sub4 (add4 a.words b.words) p.words)
  rw [addMod4, addBack4_val p hbor]
  rw [hS, show lowValue p.words = p.val from rfl] at hd
  simp only [wordRadix] at hD
  generalize lowValue (sub4 (add4 a.words b.words) p.words) = D at *
  generalize (2:Nat)^256 = K at *
  -- With no borrow, `p ≤ a + b` and the result is `a + b - p`, and with a borrow it is `a + b`.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbor with h | h <;> rw [h] at hd ⊢
  · rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hD, Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mul_one, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (a := a.val + b.val) (by omega)]
    omega

/-- The difference is `a - b` mod `p`. -/
theorem subMod4_spec {p a b : Raw} (ha : a.val < p.val) (hb : b.val < p.val) :
    (subMod4 p a b).val = (a.val + p.val - b.val) % p.val := by
  obtain ⟨hd, hbor⟩ := sub4_spec a.words b.words
  have hD := lowValue_lt (sub4 a.words b.words)
  have hP := p.val_lt
  rw [subMod4, addBack4_val p hbor]
  rw [show lowValue a.words = a.val from rfl, show lowValue b.words = b.val from rfl] at hd
  simp only [wordRadix] at hD
  generalize lowValue (sub4 a.words b.words) = D at *
  generalize (2:Nat)^256 = K at *
  -- With no borrow, `b ≤ a` and the result is `a - b`, and with a borrow it is `a + p - b`.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbor with h | h <;> rw [h] at hd ⊢
  · rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hD, Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mul_one, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (a := a.val + p.val - b.val) (by omega)]
    omega

end EthLib.Cryptography.Word64
