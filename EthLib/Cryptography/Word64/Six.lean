module

public import EthLib.Cryptography.Word64

/-!
# Arithmetic mod `p` on six 64-bit words

The sum, the difference and the Montgomery product `a b R⁻¹ mod p`, with `R = 2^384`.

The modulus is odd and below `2^383`.

The product is the CIOS method of [Koç, Acar and Kaliski][cios], with words of 64 bits.

[cios]: https://doi.org/10.1109/40.502403
-/

@[expose] public section

namespace EthLib.Cryptography.Word64

/-- Six words, least significant first. -/
structure Words6 where
  /-- Bits 0 through 63. -/
  w0 : UInt64
  /-- Bits 64 through 127. -/
  w1 : UInt64
  /-- Bits 128 through 191. -/
  w2 : UInt64
  /-- Bits 192 through 255. -/
  w3 : UInt64
  /-- Bits 256 through 319. -/
  w4 : UInt64
  /-- Bits 320 through 383. -/
  w5 : UInt64
deriving DecidableEq, Inhabited

/-- The integer of six words. -/
def Words6.val (t : Words6) : Nat :=
  t.w0.toNat + 2^64 * t.w1.toNat + 2^128 * t.w2.toNat + 2^192 * t.w3.toNat +
    2^256 * t.w4.toNat + 2^320 * t.w5.toNat

/-- Limb `k` of 32 bits: the low half of word `k / 2` for an even `k`, its high half for an odd one.

Past the last limb, it is `0`. -/
@[inline] def Words6.limb (a : Words6) : Nat → UInt64
  | 0 => a.w0 &&& 0xFFFFFFFF
  | 1 => a.w0 >>> 32
  | 2 => a.w1 &&& 0xFFFFFFFF
  | 3 => a.w1 >>> 32
  | 4 => a.w2 &&& 0xFFFFFFFF
  | 5 => a.w2 >>> 32
  | 6 => a.w3 &&& 0xFFFFFFFF
  | 7 => a.w3 >>> 32
  | 8 => a.w4 &&& 0xFFFFFFFF
  | 9 => a.w4 >>> 32
  | 10 => a.w5 &&& 0xFFFFFFFF
  | 11 => a.w5 >>> 32
  | _ => 0

/-- The low 32 bits of `lo`, then the low 32 bits of `hi` above them, as one word. -/
@[inline] def pairLimbs (lo hi : UInt64) : UInt64 := (lo &&& (0xFFFFFFFF : UInt64)) ||| (hi <<< 32)

/-- A joined word writes the low halves of its two words. -/
theorem pairLimbs_toNat (lo hi : UInt64) :
    (pairLimbs lo hi).toNat = lo.toNat % 2^32 + 2^32 * (hi.toNat % 2^32) := by
  have hs : (hi <<< 32).toNat = 2^32 * (hi.toNat % 2^32) := by
    rw [UInt64.toNat_shiftLeft]
    change hi.toNat <<< 32 % 2^64 = _
    rw [Nat.shiftLeft_eq]
    omega
  -- The two halves have disjoint bits, so their `or` is their sum.
  rw [pairLimbs, UInt64.toNat_or, low_toNat, hs, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt (i := 32) (Nat.mod_lt lo.toNat (by decide)) (hi.toNat % 2^32)]
  omega

/-- The low limb of a joined word is the low half of its low word. -/
theorem pairLimbs_low (lo hi : UInt64) :
    (pairLimbs lo hi &&& 0xFFFFFFFF).toNat = lo.toNat % 2^32 := by
  rw [low_toNat, pairLimbs_toNat]
  omega

/-- The high limb of a joined word is the low half of its high word. -/
theorem pairLimbs_high (lo hi : UInt64) :
    (pairLimbs lo hi >>> 32).toNat = hi.toNat % 2^32 := by
  rw [high_toNat, pairLimbs_toNat]
  omega

/-- A word is fixed by its two halves. -/
theorem eq_of_halves {x y : UInt64} (h0 : x &&& 0xFFFFFFFF = y &&& 0xFFFFFFFF)
    (h1 : x >>> 32 = y >>> 32) : x = y := by
  have e0 := congrArg UInt64.toNat h0
  have e1 := congrArg UInt64.toNat h1
  rw [low_toNat, low_toNat] at e0
  rw [high_toNat, high_toNat] at e1
  exact UInt64.toNat_inj.mp (by omega)

/-- Each limb is below `2^32`. -/
theorem Words6.limb_lt (a : Words6) (k : Nat) : (a.limb k).toNat < 2^32 := by
  have := a.w0.toNat_lt
  have := a.w1.toNat_lt
  have := a.w2.toNat_lt
  have := a.w3.toNat_lt
  have := a.w4.toNat_lt
  have := a.w5.toNat_lt
  unfold Words6.limb
  split <;> simp only [low_toNat, high_toNat, UInt64.toNat_zero] <;> omega

/-- The state of a product: six words and the word above them. -/
structure Acc6 where
  /-- The six low words. -/
  low : Words6
  /-- The word above bit 383. -/
  top : UInt64

/-- The integer of the state. -/
def Acc6.val (t : Acc6) : Nat := t.low.val + 2^384 * t.top.toNat

/--
One row of the CIOS product: `(t + a x + m p) / 2^64`.

The multiple `m` of `p` is the one that clears the low word of the sum.

`pinv` is `-p⁻¹ mod 2^64`.
-/
@[inline] def row6 (p : Words6) (pinv : UInt64) (a : Words6) (x : UInt64) (t : Acc6) : Acc6 :=
  -- The multiplication loop: `(C, S) := t[j] + a[j] x + C`, for `j` from 0 to 5.
  let u0 := mac a.w0 x t.low.w0 0
  let u1 := mac a.w1 x t.low.w1 u0.hi
  let u2 := mac a.w2 x t.low.w2 u1.hi
  let u3 := mac a.w3 x t.low.w3 u2.hi
  let u4 := mac a.w4 x t.low.w4 u3.hi
  let u5 := mac a.w5 x t.low.w5 u4.hi
  -- `(C, S) := t[6] + C`, then `t[6] := S` and `t[7] := C`.
  let u6 := plus t.top u5.hi 0
  -- `m := t[0] pinv mod 2^64`.
  let m := u0.lo * pinv
  -- The reduction loop: `(C, S) := t[j] + m p[j] + C`; the low word `S` of `j = 0` is zero.
  let v0 := mac m p.w0 u0.lo 0
  let v1 := mac m p.w1 u1.lo v0.hi
  let v2 := mac m p.w2 u2.lo v1.hi
  let v3 := mac m p.w3 u3.lo v2.hi
  let v4 := mac m p.w4 u4.lo v3.hi
  let v5 := mac m p.w5 u5.lo v4.hi
  -- The words move down by one: `t[j - 1] := S`, and the top takes both carries.
  let v6 := plus u6.lo v5.hi 0
  ⟨⟨v1.lo, v2.lo, v3.lo, v4.lo, v5.lo, v6.lo⟩, u6.hi + v6.hi⟩

/-- The six words of `a + b mod 2^384`, with the carry as the top word. -/
@[inline] def sum6 (a b : Words6) : Acc6 :=
  let s0 := plus a.w0 b.w0 0
  let s1 := plus a.w1 b.w1 s0.hi
  let s2 := plus a.w2 b.w2 s1.hi
  let s3 := plus a.w3 b.w3 s2.hi
  let s4 := plus a.w4 b.w4 s3.hi
  let s5 := plus a.w5 b.w5 s4.hi
  ⟨⟨s0.lo, s1.lo, s2.lo, s3.lo, s4.lo, s5.lo⟩, s5.hi⟩

/-- The six words of `a - b mod 2^384`, with the borrow as the top word. -/
@[inline] def diff6 (a b : Words6) : Acc6 :=
  let d0 := minus a.w0 b.w0 0
  let d1 := minus a.w1 b.w1 d0.hi
  let d2 := minus a.w2 b.w2 d1.hi
  let d3 := minus a.w3 b.w3 d2.hi
  let d4 := minus a.w4 b.w4 d3.hi
  let d5 := minus a.w5 b.w5 d4.hi
  ⟨⟨d0.lo, d1.lo, d2.lo, d3.lo, d4.lo, d5.lo⟩, d5.hi⟩

/-- `t - p` when `t ≥ p`, else `t`, for a state below `2 p`. -/
@[inline] def reduce6 (p : Words6) (t : Acc6) : Words6 :=
  -- Step 3 of CIOS: the result is `t - p` when `t ≥ p`, and `t` otherwise.
  let d := diff6 t.low p
  -- `t < p` exactly when the subtraction borrows more than the top word holds.
  if t.top < d.top then t.low else d.low

/-- The Montgomery product `a b 2^(-384) mod p`, for `a` below `p`. -/
@[inline] def mul6 (p : Words6) (pinv : UInt64) (a b : Words6) : Words6 :=
  -- One row for each word of `b`, from the lowest, starting from zero.
  let t : Acc6 := ⟨⟨0, 0, 0, 0, 0, 0⟩, 0⟩
  let t := row6 p pinv a b.w0 t
  let t := row6 p pinv a b.w1 t
  let t := row6 p pinv a b.w2 t
  let t := row6 p pinv a b.w3 t
  let t := row6 p pinv a b.w4 t
  let t := row6 p pinv a b.w5 t
  reduce6 p t

/-- The words of `t` where the mask `m` is set. -/
@[inline] def Words6.mask (t : Words6) (m : UInt64) : Words6 :=
  ⟨t.w0 &&& m, t.w1 &&& m, t.w2 &&& m, t.w3 &&& m, t.w4 &&& m, t.w5 &&& m⟩

/-- The low words of `d`, plus `p` mod `2^384` when the top word of `d` is a borrow of one.

The sum takes `p` through a mask of the borrow, with no branch. -/
@[inline] def addBack (p : Words6) (d : Acc6) : Words6 :=
  -- All ones on a borrow, and zero otherwise.
  let m := 0 - d.top
  -- The carry of this sum cancels the borrow.
  (sum6 d.low (p.mask m)).low

/-- `a + b mod p`, for `a` and `b` below `p` and `2 p < 2^384`. -/
@[inline] def add6 (p a b : Words6) : Words6 :=
  -- The sum is below `2^384`, so it has no carry.
  let s := (sum6 a b).low
  -- `s - p`, with `p` added back when `s < p`.
  addBack p (diff6 s p)

/-- `a - b mod p`, for `a` and `b` below `p`. -/
@[inline] def sub6 (p a b : Words6) : Words6 :=
  addBack p (diff6 a b)

/-! ## Proofs -/

/-- The sum and its carry write `a + b`, and the carry is at most one. -/
theorem sum6_val (a b : Words6) : (sum6 a b).val = a.val + b.val ∧ (sum6 a b).top.toNat ≤ 1 := by
  simp only [sum6]
  have e0 := plus_spec a.w0 b.w0 0 (by decide)
  generalize plus a.w0 b.w0 0 = s0 at *
  have e1 := plus_spec a.w1 b.w1 s0.hi e0.2
  generalize plus a.w1 b.w1 s0.hi = s1 at *
  have e2 := plus_spec a.w2 b.w2 s1.hi e1.2
  generalize plus a.w2 b.w2 s1.hi = s2 at *
  have e3 := plus_spec a.w3 b.w3 s2.hi e2.2
  generalize plus a.w3 b.w3 s2.hi = s3 at *
  have e4 := plus_spec a.w4 b.w4 s3.hi e3.2
  generalize plus a.w4 b.w4 s3.hi = s4 at *
  have e5 := plus_spec a.w5 b.w5 s4.hi e4.2
  generalize plus a.w5 b.w5 s4.hi = s5 at *
  refine ⟨?_, e5.2⟩
  simp only [wordRadix, UInt64.toNat_zero] at e0 e1 e2 e3 e4 e5
  simp only [Acc6.val, Words6.val]
  omega

/-- The difference and `b` write `a`, plus `2^384` on a borrow, which is at most one. -/
theorem diff6_val (a b : Words6) :
    (diff6 a b).low.val + b.val = a.val + 2^384 * (diff6 a b).top.toNat ∧
      (diff6 a b).top.toNat ≤ 1 := by
  simp only [diff6]
  have g0 := minus_spec a.w0 b.w0 0 (by decide)
  generalize minus a.w0 b.w0 0 = d0 at *
  have g1 := minus_spec a.w1 b.w1 d0.hi g0.2
  generalize minus a.w1 b.w1 d0.hi = d1 at *
  have g2 := minus_spec a.w2 b.w2 d1.hi g1.2
  generalize minus a.w2 b.w2 d1.hi = d2 at *
  have g3 := minus_spec a.w3 b.w3 d2.hi g2.2
  generalize minus a.w3 b.w3 d2.hi = d3 at *
  have g4 := minus_spec a.w4 b.w4 d3.hi g3.2
  generalize minus a.w4 b.w4 d3.hi = d4 at *
  have g5 := minus_spec a.w5 b.w5 d4.hi g4.2
  generalize minus a.w5 b.w5 d4.hi = d5 at *
  refine ⟨?_, g5.2⟩
  simp only [wordRadix, UInt64.toNat_zero] at g0 g1 g2 g3 g4 g5
  simp only [Words6.val]
  omega

/-- Six words are below `2^384`. -/
theorem Words6.val_lt (t : Words6) : t.val < 2^384 := by
  have := t.w0.toNat_lt
  have := t.w1.toNat_lt
  have := t.w2.toNat_lt
  have := t.w3.toNat_lt
  have := t.w4.toNat_lt
  have := t.w5.toNat_lt
  simp only [Words6.val]
  omega

/-- `m = t pinv mod 2^64` clears the low word of `t + m p`. -/
private theorem low_clear {pv p0 r pinv u : Nat} (hpv : pv = p0 + 2^64 * r)
    (hpinv : (pv * pinv + 1) % 2^64 = 0) : (u * pinv % 2^64 * p0 + u) % 2^64 = 0 := by
  -- The low word of `p` alone already gives `p0 pinv = -1 mod 2^64`.
  have h1 : 2^64 ∣ p0 * pinv + 1 := by
    have h := Nat.dvd_of_mod_eq_zero hpinv
    rw [hpv, show (p0 + 2^64 * r) * pinv + 1 = 2^64 * (r * pinv) + (p0 * pinv + 1) by
      rw [Nat.add_mul, Nat.mul_assoc]; omega] at h
    exact (Nat.dvd_add_right (Nat.dvd_mul_right _ _)).mp h
  -- Reducing `u pinv` mod `2^64` drops a multiple of `2^64` from `u (p0 pinv + 1)`.
  have h2 : 2^64 * (u * pinv / 2^64 * p0) + (u * pinv % 2^64 * p0 + u) =
      u * (p0 * pinv + 1) := by
    have hq := Nat.div_add_mod (u * pinv) (2^64)
    calc _ = (2^64 * (u * pinv / 2^64) + u * pinv % 2^64) * p0 + u := by
          rw [Nat.add_mul (2^64 * _), Nat.mul_assoc]; omega
      _ = u * (p0 * pinv + 1) := by
          rw [hq, Nat.mul_add, Nat.mul_one, Nat.mul_comm p0 pinv, Nat.mul_assoc]
  apply Nat.mod_eq_zero_of_dvd
  have h3 := Nat.dvd_mul_left_of_dvd h1 u
  rw [← h2] at h3
  exact (Nat.dvd_add_right (Nat.dvd_mul_right _ _)).mp h3

/-- A row adds `a x` and a multiple of `p`, divides by `2^64`, and stays below `2 p`. -/
theorem row6_spec {p : Words6} {pinv : UInt64} (hpinv : (p.val * pinv.toNat + 1) % 2^64 = 0)
    {a : Words6} (ha : a.val < p.val) (x : UInt64) {t : Acc6} (ht : t.val < 2 * p.val) :
    (row6 p pinv a x t).val < 2 * p.val ∧
      ∃ m : Nat, 2^64 * (row6 p pinv a x t).val = t.val + a.val * x.toNat + m * p.val := by
  simp only [row6]
  -- The multiplication loop.
  have e0 := mac_spec a.w0 x t.low.w0 0
  generalize mac a.w0 x t.low.w0 0 = u0 at *
  have e1 := mac_spec a.w1 x t.low.w1 u0.hi
  generalize mac a.w1 x t.low.w1 u0.hi = u1 at *
  have e2 := mac_spec a.w2 x t.low.w2 u1.hi
  generalize mac a.w2 x t.low.w2 u1.hi = u2 at *
  have e3 := mac_spec a.w3 x t.low.w3 u2.hi
  generalize mac a.w3 x t.low.w3 u2.hi = u3 at *
  have e4 := mac_spec a.w4 x t.low.w4 u3.hi
  generalize mac a.w4 x t.low.w4 u3.hi = u4 at *
  have e5 := mac_spec a.w5 x t.low.w5 u4.hi
  generalize mac a.w5 x t.low.w5 u4.hi = u5 at *
  have e6 := plus_spec t.top u5.hi 0 (by decide)
  generalize plus t.top u5.hi 0 = u6 at *
  -- The multiple `m` of `p` clears the low word.
  have hclear : ((u0.lo * pinv).toNat * p.w0.toNat + u0.lo.toNat) % 2^64 = 0 := by
    rw [UInt64.toNat_mul]
    refine low_clear (r := p.w1.toNat + 2^64 * p.w2.toNat + 2^128 * p.w3.toNat +
      2^192 * p.w4.toNat + 2^256 * p.w5.toNat) ?_ hpinv
    simp only [Words6.val]
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
  have f4 := mac_spec m p.w4 u4.lo v3.hi
  generalize mac m p.w4 u4.lo v3.hi = v4 at *
  have f5 := mac_spec m p.w5 u5.lo v4.hi
  generalize mac m p.w5 u5.lo v4.hi = v5 at *
  have f6 := plus_spec u6.lo v5.hi 0 (by decide)
  generalize plus u6.lo v5.hi 0 = v6 at *
  have hv0 : v0.lo.toNat = 0 := by
    have := v0.lo.toNat_lt
    simp only [UInt64.toNat_zero] at f0
    omega
  -- The two carries into the top word are at most one each, so they add without wrapping.
  have htop : (u6.hi + v6.hi).toNat = u6.hi.toNat + v6.hi.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by simp only [wordRadix] at e6 f6; omega)
  -- The row as an equation of integers.
  have key : 2^64 * Acc6.val ⟨⟨v1.lo, v2.lo, v3.lo, v4.lo, v5.lo, v6.lo⟩, u6.hi + v6.hi⟩ =
      t.val + a.val * x.toNat + m.toNat * p.val := by
    have hax : a.val * x.toNat = a.w0.toNat * x.toNat + 2^64 * (a.w1.toNat * x.toNat) +
        2^128 * (a.w2.toNat * x.toNat) + 2^192 * (a.w3.toNat * x.toNat) +
        2^256 * (a.w4.toNat * x.toNat) + 2^320 * (a.w5.toNat * x.toNat) := by
      simp only [Words6.val, Nat.add_mul, Nat.mul_assoc]
    have hmp : m.toNat * p.val = m.toNat * p.w0.toNat + 2^64 * (m.toNat * p.w1.toNat) +
        2^128 * (m.toNat * p.w2.toNat) + 2^192 * (m.toNat * p.w3.toNat) +
        2^256 * (m.toNat * p.w4.toNat) + 2^320 * (m.toNat * p.w5.toNat) := by
      simp only [Words6.val, Nat.mul_add, Nat.mul_left_comm m.toNat]
    rw [hax, hmp]
    simp only [wordRadix, UInt64.toNat_zero] at e0 e6 f0 f6
    simp only [Acc6.val, Words6.val, htop]
    omega
  refine ⟨?_, m.toNat, key⟩
  -- `2^64 t' = t + a x + m p < 2 p + p (2^64 - 1) + (2^64 - 1) p = 2^65 p`.
  have hax : a.val * x.toNat ≤ p.val * (2^64 - 1) :=
    Nat.mul_le_mul (by omega) (by have := x.toNat_lt; omega)
  have hmp : m.toNat * p.val ≤ (2^64 - 1) * p.val :=
    Nat.mul_le_mul_right _ (by have := m.toNat_lt; omega)
  omega

/-- The final subtraction gives the remainder mod `p`, for a state below `2 p` and `2 p < 2^384`. -/
theorem reduce6_val {p : Words6} (hp : 2 * p.val < 2^384) {t : Acc6} (ht : t.val < 2 * p.val) :
    (reduce6 p t).val = t.val % p.val := by
  -- The six words of the difference, with the final borrow: `d + p = t + 2^384 borrow`.
  obtain ⟨hd, hb⟩ := diff6_val t.low p
  have hD := (diff6 t.low p).low.val_lt
  simp only [reduce6, Acc6.val] at ht ⊢
  split
  · rename_i hc
    have hc' : t.top.toNat < (diff6 t.low p).top.toNat := hc
    generalize (diff6 t.low p).low.val = D at *
    generalize t.low.val = T at *
    generalize p.val = P at *
    -- The subtraction borrows, so `t < p`.
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i hc
    have hc' : ¬ t.top.toNat < (diff6 t.low p).top.toNat := hc
    generalize (diff6 t.low p).low.val = D at *
    generalize t.low.val = T at *
    generalize p.val = P at *
    -- No borrow: `p ≤ t < 2 p`, and the words hold `t - p`.
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The product is below `p`, and it is `a b` divided by `2^384` mod `p`. -/
theorem mul6_spec {p : Words6} {pinv : UInt64} (hp : 2 * p.val < 2^384)
    (hpinv : (p.val * pinv.toNat + 1) % 2^64 = 0) {a : Words6} (ha : a.val < p.val)
    (b : Words6) :
    (mul6 p pinv a b).val < p.val ∧
      2^384 * (mul6 p pinv a b).val % p.val = a.val * b.val % p.val := by
  -- `p` is odd, so it is not zero.
  have hp0 : 0 < p.val := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, Nat.zero_mul] at hpinv
    exact absurd hpinv (by decide)
  have h0 : Acc6.val ⟨⟨0, 0, 0, 0, 0, 0⟩, 0⟩ = 0 := by
    simp only [Acc6.val, Words6.val, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
  obtain ⟨b1, m0, e0⟩ := row6_spec hpinv ha b.w0 (t := ⟨⟨0, 0, 0, 0, 0, 0⟩, 0⟩)
    (by rw [h0]; omega)
  obtain ⟨b2, m1, e1⟩ := row6_spec hpinv ha b.w1 b1
  obtain ⟨b3, m2, e2⟩ := row6_spec hpinv ha b.w2 b2
  obtain ⟨b4, m3, e3⟩ := row6_spec hpinv ha b.w3 b3
  obtain ⟨b5, m4, e4⟩ := row6_spec hpinv ha b.w4 b4
  obtain ⟨b6, m5, e5⟩ := row6_spec hpinv ha b.w5 b5
  simp only [mul6]
  rw [reduce6_val hp b6]
  refine ⟨Nat.mod_lt _ hp0, ?_⟩
  -- The rows give `2^384 t = a b + M p`.
  have hb : a.val * b.val = a.val * b.w0.toNat + 2^64 * (a.val * b.w1.toNat) +
      2^128 * (a.val * b.w2.toNat) + 2^192 * (a.val * b.w3.toNat) +
      2^256 * (a.val * b.w4.toNat) + 2^320 * (a.val * b.w5.toNat) := by
    have hbv : b.val = b.w0.toNat + 2^64 * b.w1.toNat + 2^128 * b.w2.toNat +
        2^192 * b.w3.toNat + 2^256 * b.w4.toNat + 2^320 * b.w5.toNat := by
      simp only [Words6.val]
    rw [hbv]
    simp only [Nat.mul_add, Nat.mul_left_comm a.val]
  have hm : (m0 + 2^64 * m1 + 2^128 * m2 + 2^192 * m3 + 2^256 * m4 + 2^320 * m5) * p.val =
      m0 * p.val + 2^64 * (m1 * p.val) + 2^128 * (m2 * p.val) + 2^192 * (m3 * p.val) +
        2^256 * (m4 * p.val) + 2^320 * (m5 * p.val) := by
    simp only [Nat.add_mul, Nat.mul_assoc]
  have key : 2^384 * (row6 p pinv a b.w5 (row6 p pinv a b.w4 (row6 p pinv a b.w3
      (row6 p pinv a b.w2 (row6 p pinv a b.w1
        (row6 p pinv a b.w0 ⟨⟨0, 0, 0, 0, 0, 0⟩, 0⟩)))))).val =
      a.val * b.val + (m0 + 2^64 * m1 + 2^128 * m2 + 2^192 * m3 + 2^256 * m4 + 2^320 * m5) *
        p.val := by
    rw [h0] at e0
    omega
  -- `2^384` as an atom, so that no step tries to evaluate it.
  generalize (2:Nat)^384 = R at key ⊢
  rw [Nat.mul_mod_mod, key, Nat.add_mul_mod_self_right]

/-- The mask of a borrow keeps `t` on a borrow and clears it otherwise. -/
theorem Words6.val_mask (t : Words6) {c : UInt64} (hc : c.toNat ≤ 1) :
    (t.mask (0 - c)).val = t.val * c.toNat := by
  have h : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
    · exact Or.inl (UInt64.toNat_inj.mp h)
    · exact Or.inr (UInt64.toNat_inj.mp h)
  rcases h with rfl | rfl
  · have e (x : UInt64) : x &&& (0 - 0) = 0 := by rw [UInt64.sub_self, UInt64.and_zero]
    simp only [Words6.mask, Words6.val, e, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]
  · -- `0 - 1` is the word of all ones.
    have hm : ((0 : UInt64) - 1).toNat = 2^64 - 1 := by decide
    have e (x : UInt64) : x &&& (0 - 1) = x := UInt64.toNat_inj.mp (by
      rw [UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt x.toNat_lt])
    simp only [Words6.mask, e, UInt64.toNat_one, Nat.mul_one]

/-- Adding back gives `d + p` on a borrow and `d` otherwise, mod `2^384`. -/
theorem addBack_val (p : Words6) {d : Acc6} (hc : d.top.toNat ≤ 1) :
    (addBack p d).val = (d.low.val + p.val * d.top.toNat) % 2^384 := by
  obtain ⟨hs, -⟩ := sum6_val d.low (p.mask (0 - d.top))
  rw [Words6.val_mask p hc, Acc6.val] at hs
  have hl := (sum6 d.low (p.mask (0 - d.top))).low.val_lt
  simp only [addBack]
  generalize sum6 d.low (p.mask (0 - d.top)) = s at *
  generalize (2:Nat)^384 = K at *
  rw [← hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The sum is `a + b` mod `p`. -/
theorem add6_spec {p : Words6} (hp : 2 * p.val < 2^384) {a b : Words6} (ha : a.val < p.val)
    (hb : b.val < p.val) : (add6 p a b).val = (a.val + b.val) % p.val := by
  -- The sum is below `2 p < 2^384`, so it has no carry.
  obtain ⟨hs, -⟩ := sum6_val a b
  rw [Acc6.val] at hs
  have hS : (sum6 a b).low.val = a.val + b.val := by
    have hl := (sum6 a b).low.val_lt
    have hab : a.val + b.val < 2^384 := by omega
    generalize sum6 a b = s at *
    generalize (2:Nat)^384 = K at *
    rw [← Nat.mod_eq_of_lt hl, ← Nat.add_mul_mod_self_left, hs, Nat.mod_eq_of_lt hab]
  obtain ⟨hd, hbor⟩ := diff6_val (sum6 a b).low p
  have hD := (diff6 (sum6 a b).low p).low.val_lt
  rw [add6, addBack_val p hbor]
  rw [hS] at hd
  generalize (diff6 (sum6 a b).low p).low.val = D at *
  generalize (2:Nat)^384 = K at *
  -- With no borrow, `p ≤ a + b` and the result is `a + b - p`; with one, it is `a + b`.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbor with h | h <;> rw [h] at hd ⊢
  · rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hD, Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mul_one, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (a := a.val + b.val) (by omega)]
    omega

/-- The difference is `a - b` mod `p`. -/
theorem sub6_spec {p a b : Words6} (ha : a.val < p.val) (hb : b.val < p.val) :
    (sub6 p a b).val = (a.val + p.val - b.val) % p.val := by
  obtain ⟨hd, hbor⟩ := diff6_val a b
  have hD := (diff6 a b).low.val_lt
  have hP := p.val_lt
  rw [sub6, addBack_val p hbor]
  generalize (diff6 a b).low.val = D at *
  generalize (2:Nat)^384 = K at *
  -- With no borrow, `b ≤ a` and the result is `a - b`; with one, it is `a + p - b`.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbor with h | h <;> rw [h] at hd ⊢
  · rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hD, Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mul_one, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (a := a.val + p.val - b.val) (by omega)]
    omega

end EthLib.Cryptography.Word64
