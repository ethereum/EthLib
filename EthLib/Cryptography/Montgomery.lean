module

public import EthLib.Cryptography.Inverse

/-!
# Montgomery arithmetic

Arithmetic mod an odd modulus `p` below `2 ^ 256`, on eight limbs of 32 bits.

An element `a` is stored in Montgomery form, as `a R mod p` with `R = 2 ^ 256`.

The product of two forms is then `a b R ^ 2`, and one Montgomery reduction divides it by `R`.

The reduction adds the multiple of `p` that clears the low limb, then drops that limb.

So it needs no division by `p`.

The product is the Coarsely Integrated Operand Scanning (CIOS) method of Koç, Acar and Kaliski.

It appeared as "Analyzing and comparing Montgomery multiplication algorithms" in IEEE Micro 16(3).

<https://doi.org/10.1109/40.502403>

It interleaves the product and the reduction, one limb of `b` at a time.

Each product of two limbs fits in 64 bits, so the code needs no wider product.

Every operation keeps its result below `p`, and the theorems here prove those bounds.

The proofs that the operations agree with the integers mod `p` come with the other properties.
-/

@[expose] public section

namespace EthLib.Cryptography

namespace Montgomery

/-- The low 32 bits and the carry of `t + a * b + c`. -/
@[inline] def mac (t a b c : UInt64) : UInt64 × UInt64 :=
  let s := t + a * b + c
  (s &&& 0xFFFFFFFF, s >>> 32)

/-- The two words of `mac` write `t + a b + c`, when every input is below `2 ^ 32`. -/
theorem mac_spec {t a b c : UInt64} (ht : t.toNat < 2 ^ 32) (ha : a.toNat < 2 ^ 32)
    (hb : b.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    (mac t a b c).1.toNat + 2 ^ 32 * (mac t a b c).2.toNat
      = t.toNat + a.toNat * b.toNat + c.toNat ∧
    (mac t a b c).1.toNat < 2 ^ 32 ∧ (mac t a b c).2.toNat < 2 ^ 32 := by
  have hab : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hs : (t + a * b + c).toNat = t.toNat + a.toNat * b.toNat + c.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    rw [Nat.mod_eq_of_lt (a := a.toNat * b.toNat) (by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hm : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
  simp only [mac, UInt64.toNat_and, UInt64.toNat_shiftRight, hs, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp
  omega

/-- The low 32 bits of `x - y - b`, and the borrow out of them. -/
@[inline] def sbb (x y b : UInt64) : UInt64 × UInt64 :=
  let d := x - y - b
  (d &&& 0xFFFFFFFF, d >>> 63)

/-- The two words of `sbb` write `x - y - b`, with the borrow as a multiple of `2 ^ 32`. -/
theorem sbb_spec {x y b : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
    (hb : b.toNat ≤ 1) :
    (sbb x y b).1.toNat + y.toNat + b.toNat = x.toNat + 2 ^ 32 * (sbb x y b).2.toNat ∧
    (sbb x y b).1.toNat < 2 ^ 32 ∧ (sbb x y b).2.toNat ≤ 1 := by
  have hm : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
  simp only [sbb, UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_sub, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  simp
  omega

private theorem z1 : (0 : UInt64).toNat ≤ 1 := by decide

private theorem o64 : (1 : UInt64).toNat < 2 ^ 32 := by decide

private theorem lt33 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : x + y < 2 ^ 33 := by
  omega

private theorem z64 : (0 : UInt64).toNat < 2 ^ 32 := by decide

private theorem u32 (x : UInt32) : x.toUInt64.toNat < 2 ^ 32 := by
  simpa using x.toNat_lt

private theorem low_mul {x : UInt64} (hx : x.toNat < 2 ^ 32) (y : UInt32) :
    ((x * y.toUInt64) &&& 0xFFFFFFFF).toNat = x.toNat * y.toNat % 2 ^ 32 := by
  have hy := y.toNat_lt
  have hxy : x.toNat * y.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hx hy
    omega
  have hm : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
  simp only [UInt64.toNat_and, UInt64.toNat_mul, UInt32.toNat_toUInt64, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hxy]

private theorem low_zero {m x y z : Nat} (hm : m = x * y % 2 ^ 32) (h : (z * y + 1) % 2 ^ 32 = 0) :
    (x + m * z) % 2 ^ 32 = 0 := by
  subst hm
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod, Nat.mul_assoc, Nat.mul_comm y z]
  have : x + x * (z * y) = x * (z * y + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
  rw [this, Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

private theorem low_eq_zero {x y s : Nat} (e : x + 2 ^ 32 * y = s) (hs : s % 2 ^ 32 = 0)
    (hx : x < 2 ^ 32) : x = 0 := by
  omega

private theorem add_small {x y : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- An integer below `2 ^ 256`, as 8 limbs of 32 bits, the lowest first. -/
structure Limbs where
  l0 : UInt32
  l1 : UInt32
  l2 : UInt32
  l3 : UInt32
  l4 : UInt32
  l5 : UInt32
  l6 : UInt32
  l7 : UInt32
deriving DecidableEq, Inhabited

namespace Limbs

/-- The integer that the limbs write. -/
def val (a : Limbs) : Nat :=
  a.l0.toNat + 2 ^ 32 * (a.l1.toNat + 2 ^ 32 * (a.l2.toNat + 2 ^ 32 * (a.l3.toNat +
      2 ^ 32 * (a.l4.toNat + 2 ^ 32 * (a.l5.toNat + 2 ^ 32 * (a.l6.toNat +
      2 ^ 32 * (a.l7.toNat)))))))

/-- The limbs of `n mod 2 ^ 256`. -/
def ofNat (n : Nat) : Limbs :=
  ⟨(n % 2 ^ 32).toUInt32,
    (n / 2 ^ 32 % 2 ^ 32).toUInt32,
    (n / 2 ^ 64 % 2 ^ 32).toUInt32,
    (n / 2 ^ 96 % 2 ^ 32).toUInt32,
    (n / 2 ^ 128 % 2 ^ 32).toUInt32,
    (n / 2 ^ 160 % 2 ^ 32).toUInt32,
    (n / 2 ^ 192 % 2 ^ 32).toUInt32,
    (n / 2 ^ 224 % 2 ^ 32).toUInt32⟩

/-- The integer of the limbs is below `2 ^ 256`. -/
theorem val_lt (a : Limbs) : a.val < 2 ^ 256 := by
  have := a.l0.toNat_lt
  have := a.l1.toNat_lt
  have := a.l2.toNat_lt
  have := a.l3.toNat_lt
  have := a.l4.toNat_lt
  have := a.l5.toNat_lt
  have := a.l6.toNat_lt
  have := a.l7.toNat_lt
  simp only [val]
  omega

/-- The limbs of `n` write `n mod 2 ^ 256`. -/
theorem val_ofNat (n : Nat) : (ofNat n).val = n % 2 ^ 256 := by
  simp only [val, ofNat, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  omega

/-- The integer times `b`, limb by limb. -/
theorem val_mul (a : Limbs) (b : Nat) :
    a.val * b = a.l0.toNat * b + 2 ^ 32 * (a.l1.toNat * b + 2 ^ 32 * (a.l2.toNat * b +
        2 ^ 32 * (a.l3.toNat * b + 2 ^ 32 * (a.l4.toNat * b + 2 ^ 32 * (a.l5.toNat * b +
        2 ^ 32 * (a.l6.toNat * b + 2 ^ 32 * (a.l7.toNat * b))))))) := by
  simp only [val, Nat.add_mul, Nat.mul_assoc]

/-- `b` times the integer, limb by limb. -/
theorem mul_val (b : Nat) (a : Limbs) :
    b * a.val = b * a.l0.toNat + 2 ^ 32 * (b * a.l1.toNat + 2 ^ 32 * (b * a.l2.toNat +
        2 ^ 32 * (b * a.l3.toNat + 2 ^ 32 * (b * a.l4.toNat + 2 ^ 32 * (b * a.l5.toNat +
        2 ^ 32 * (b * a.l6.toNat + 2 ^ 32 * (b * a.l7.toNat))))))) := by
  simp only [val, Nat.mul_add, Nat.mul_left_comm b]

end Limbs

/-- 9 words: 8 limbs held in 64 bits, and one word above them. -/
structure Words where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64

namespace Words

/-- The integer that the words write. -/
def val (t : Words) : Nat :=
  t.w0.toNat + 2 ^ 32 * (t.w1.toNat + 2 ^ 32 * (t.w2.toNat + 2 ^ 32 * (t.w3.toNat +
      2 ^ 32 * (t.w4.toNat + 2 ^ 32 * (t.w5.toNat + 2 ^ 32 * (t.w6.toNat + 2 ^ 32 * (t.w7.toNat +
      2 ^ 32 * (t.w8.toNat))))))))

/-- Every word is below `2 ^ 32`. -/
def Small (t : Words) : Prop :=
  t.w0.toNat < 2 ^ 32 ∧ t.w1.toNat < 2 ^ 32 ∧ t.w2.toNat < 2 ^ 32 ∧ t.w3.toNat < 2 ^ 32 ∧
      t.w4.toNat < 2 ^ 32 ∧ t.w5.toNat < 2 ^ 32 ∧ t.w6.toNat < 2 ^ 32 ∧ t.w7.toNat < 2 ^ 32 ∧
      t.w8.toNat < 2 ^ 32

/-- Zero. -/
def zero : Words := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩


/-- The integer that the low 8 words write. -/
def low (t : Words) : Nat :=
  t.w0.toNat + 2 ^ 32 * (t.w1.toNat + 2 ^ 32 * (t.w2.toNat + 2 ^ 32 * (t.w3.toNat +
      2 ^ 32 * (t.w4.toNat + 2 ^ 32 * (t.w5.toNat + 2 ^ 32 * (t.w6.toNat +
      2 ^ 32 * (t.w7.toNat)))))))

/-- The low 8 words as limbs. -/
@[inline] def trunc (t : Words) : Limbs :=
  ⟨t.w0.toUInt32, t.w1.toUInt32, t.w2.toUInt32, t.w3.toUInt32, t.w4.toUInt32, t.w5.toUInt32,
      t.w6.toUInt32, t.w7.toUInt32⟩

/-- The words write their low limbs plus the top word times `2 ^ 256`. -/
theorem val_eq (t : Words) : t.val = t.low + 2 ^ 256 * t.w8.toNat := by
  simp only [val, low]
  omega

/-- The low limbs of small words write their low integer. -/
theorem trunc_val {t : Words} (h : t.Small) : t.trunc.val = t.low := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [trunc, low, Limbs.val, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt h0,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4,
      Nat.mod_eq_of_lt h5, Nat.mod_eq_of_lt h6, Nat.mod_eq_of_lt h7]

/-- The low limbs of small words write an integer below `2 ^ 256`. -/
theorem low_lt (t : Words) (h : t.Small) : t.low < 2 ^ 256 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [low]
  omega

/-- The zero words are small. -/
theorem zero_small : zero.Small := by
  simp only [Small, zero, UInt64.toNat_zero]
  decide

/-- The zero words write `0`. -/
theorem zero_val : zero.val = 0 := rfl

end Words

/-- One iteration of the CIOS product: `(t + a b + m p) / 2 ^ 32`.

`m` is the multiple of `p` that makes the low word of the sum zero. -/
@[inline] def step (p : Limbs) (pinv : UInt32) (t : Words) (a : Limbs) (b : UInt64) : Words :=
  let r0 := mac t.w0 a.l0.toUInt64 b 0
  let r1 := mac t.w1 a.l1.toUInt64 b r0.2
  let r2 := mac t.w2 a.l2.toUInt64 b r1.2
  let r3 := mac t.w3 a.l3.toUInt64 b r2.2
  let r4 := mac t.w4 a.l4.toUInt64 b r3.2
  let r5 := mac t.w5 a.l5.toUInt64 b r4.2
  let r6 := mac t.w6 a.l6.toUInt64 b r5.2
  let r7 := mac t.w7 a.l7.toUInt64 b r6.2
  let r8 := mac t.w8 0 0 r7.2
  let m := (r0.1 * pinv.toUInt64) &&& 0xFFFFFFFF
  let q0 := mac r0.1 m p.l0.toUInt64 0
  let q1 := mac r1.1 m p.l1.toUInt64 q0.2
  let q2 := mac r2.1 m p.l2.toUInt64 q1.2
  let q3 := mac r3.1 m p.l3.toUInt64 q2.2
  let q4 := mac r4.1 m p.l4.toUInt64 q3.2
  let q5 := mac r5.1 m p.l5.toUInt64 q4.2
  let q6 := mac r6.1 m p.l6.toUInt64 q5.2
  let q7 := mac r7.1 m p.l7.toUInt64 q6.2
  let q8 := mac r8.1 0 0 q7.2
  ⟨q1.1, q2.1, q3.1, q4.1, q5.1, q6.1, q7.1, q8.1, r8.2 + q8.2⟩

/-- One CIOS step adds `a b` and a multiple `m p` of `p`, then divides by `2 ^ 32`. -/
theorem step_spec {p : Limbs} {pinv : UInt32}
    (hpinv : (p.l0.toNat * pinv.toNat + 1) % 2 ^ 32 = 0)
    {t : Words} (ht : t.Small) (a : Limbs) {b : UInt64} (hb : b.toNat < 2 ^ 32) :
    ∃ m, m < 2 ^ 32 ∧ 2 ^ 32 * (step p pinv t a b).val = t.val + a.val * b.toNat + m * p.val ∧
      (step p pinv t a b).w0.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w1.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w2.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w3.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w4.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w5.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w6.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w7.toNat < 2 ^ 32 ∧
      (step p pinv t a b).w8.toNat < 2 ^ 33 := by
  obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8⟩ := ht
  simp only [step]
  generalize hr0 : mac t.w0 a.l0.toUInt64 b (0 : UInt64) = r0
  obtain ⟨er0, lr0, cr0⟩ := mac_spec ht0 (u32 a.l0) hb z64
  rw [hr0] at er0 lr0 cr0
  generalize hr1 : mac t.w1 a.l1.toUInt64 b r0.2 = r1
  obtain ⟨er1, lr1, cr1⟩ := mac_spec ht1 (u32 a.l1) hb cr0
  rw [hr1] at er1 lr1 cr1
  generalize hr2 : mac t.w2 a.l2.toUInt64 b r1.2 = r2
  obtain ⟨er2, lr2, cr2⟩ := mac_spec ht2 (u32 a.l2) hb cr1
  rw [hr2] at er2 lr2 cr2
  generalize hr3 : mac t.w3 a.l3.toUInt64 b r2.2 = r3
  obtain ⟨er3, lr3, cr3⟩ := mac_spec ht3 (u32 a.l3) hb cr2
  rw [hr3] at er3 lr3 cr3
  generalize hr4 : mac t.w4 a.l4.toUInt64 b r3.2 = r4
  obtain ⟨er4, lr4, cr4⟩ := mac_spec ht4 (u32 a.l4) hb cr3
  rw [hr4] at er4 lr4 cr4
  generalize hr5 : mac t.w5 a.l5.toUInt64 b r4.2 = r5
  obtain ⟨er5, lr5, cr5⟩ := mac_spec ht5 (u32 a.l5) hb cr4
  rw [hr5] at er5 lr5 cr5
  generalize hr6 : mac t.w6 a.l6.toUInt64 b r5.2 = r6
  obtain ⟨er6, lr6, cr6⟩ := mac_spec ht6 (u32 a.l6) hb cr5
  rw [hr6] at er6 lr6 cr6
  generalize hr7 : mac t.w7 a.l7.toUInt64 b r6.2 = r7
  obtain ⟨er7, lr7, cr7⟩ := mac_spec ht7 (u32 a.l7) hb cr6
  rw [hr7] at er7 lr7 cr7
  generalize hr8 : mac t.w8 0 0 r7.2 = r8
  obtain ⟨er8, lr8, cr8⟩ := mac_spec ht8 z64 z64 cr7
  rw [hr8] at er8 lr8 cr8
  generalize hm : (r0.1 * pinv.toUInt64) &&& 0xFFFFFFFF = m
  have hmv : m.toNat = r0.1.toNat * pinv.toNat % 2 ^ 32 := hm ▸ low_mul lr0 pinv
  have hml : m.toNat < 2 ^ 32 := hmv ▸ Nat.mod_lt _ (by decide)
  generalize hq0 : mac r0.1 m p.l0.toUInt64 (0 : UInt64) = q0
  obtain ⟨eq0, lq0, cq0⟩ := mac_spec lr0 hml (u32 p.l0) z64
  rw [hq0] at eq0 lq0 cq0
  generalize hq1 : mac r1.1 m p.l1.toUInt64 q0.2 = q1
  obtain ⟨eq1, lq1, cq1⟩ := mac_spec lr1 hml (u32 p.l1) cq0
  rw [hq1] at eq1 lq1 cq1
  generalize hq2 : mac r2.1 m p.l2.toUInt64 q1.2 = q2
  obtain ⟨eq2, lq2, cq2⟩ := mac_spec lr2 hml (u32 p.l2) cq1
  rw [hq2] at eq2 lq2 cq2
  generalize hq3 : mac r3.1 m p.l3.toUInt64 q2.2 = q3
  obtain ⟨eq3, lq3, cq3⟩ := mac_spec lr3 hml (u32 p.l3) cq2
  rw [hq3] at eq3 lq3 cq3
  generalize hq4 : mac r4.1 m p.l4.toUInt64 q3.2 = q4
  obtain ⟨eq4, lq4, cq4⟩ := mac_spec lr4 hml (u32 p.l4) cq3
  rw [hq4] at eq4 lq4 cq4
  generalize hq5 : mac r5.1 m p.l5.toUInt64 q4.2 = q5
  obtain ⟨eq5, lq5, cq5⟩ := mac_spec lr5 hml (u32 p.l5) cq4
  rw [hq5] at eq5 lq5 cq5
  generalize hq6 : mac r6.1 m p.l6.toUInt64 q5.2 = q6
  obtain ⟨eq6, lq6, cq6⟩ := mac_spec lr6 hml (u32 p.l6) cq5
  rw [hq6] at eq6 lq6 cq6
  generalize hq7 : mac r7.1 m p.l7.toUInt64 q6.2 = q7
  obtain ⟨eq7, lq7, cq7⟩ := mac_spec lr7 hml (u32 p.l7) cq6
  rw [hq7] at eq7 lq7 cq7
  generalize hq8 : mac r8.1 0 0 q7.2 = q8
  obtain ⟨eq8, lq8, cq8⟩ := mac_spec lr8 z64 z64 cq7
  rw [hq8] at eq8 lq8 cq8
  have hz := low_eq_zero eq0 (low_zero hmv hpinv) lq0
  have hw : (r8.2 + q8.2).toNat = r8.2.toNat + q8.2.toNat := add_small cr8 cq8
  refine ⟨m.toNat, hml, ?_, lq1, lq2, lq3, lq4, lq5, lq6, lq7, lq8, by rw [hw]; exact lt33 cr8 cq8⟩
  rw [Limbs.val_mul, Limbs.mul_val]
  simp only [Words.val, hw, UInt32.toNat_toUInt64, UInt64.toNat_zero, Nat.mul_zero,
    Nat.add_zero] at *
  clear lr0 cr0 lq0 cq0 lr1 cr1 lq1 cq1 lr2 cr2 lq2 cq2 lr3 cr3 lq3 cq3 lr4 cr4 lq4 cq4 lr5 cr5 lq5
  clear cq5 lr6 cr6 lq6 cq6 lr7 cr7 lq7 cq7 lr8 cr8 lq8 cq8 hmv hml hpinv hb hw
  clear ht0 hr0 hq0 ht1 hr1 hq1 ht2 hr2 hq2 ht3 hr3 hq3 ht4 hr4 hq4 ht5 hr5 hq5 ht6 hr6 hq6 ht7 hr7
  clear hq7 ht8 hr8 hq8 hm
  grind

/-- A modulus with an inverse mod `2 ^ 32` is positive. -/
theorem pos_of_pinv {p : Limbs} {pinv : UInt32}
    (hpinv : (p.l0.toNat * pinv.toNat + 1) % 2 ^ 32 = 0) : 0 < p.val := by
  rcases Nat.eq_zero_or_pos p.l0.toNat with h | h
  · rw [h, Nat.zero_mul] at hpinv
    exact absurd hpinv (by decide)
  · simp only [Limbs.val]
    omega

/-- One CIOS step keeps its words small and its value below `2 p`. -/
theorem step_inv {p : Limbs} {pinv : UInt32}
    (hpinv : (p.l0.toNat * pinv.toNat + 1) % 2 ^ 32 = 0)
    {t : Words} (ht : t.Small) (htv : t.val < 2 * p.val) {a : Limbs} (ha : a.val < p.val)
    {b : UInt64} (hb : b.toNat < 2 ^ 32) :
    ∃ m, 2 ^ 32 * (step p pinv t a b).val = t.val + a.val * b.toNat + m * p.val ∧
      (step p pinv t a b).Small ∧ (step p pinv t a b).val < 2 * p.val := by
  obtain ⟨m, hm, he, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := step_spec hpinv ht a hb
  have hb1 : a.val * b.toNat ≤ p.val * (2 ^ 32 - 1) := Nat.mul_le_mul (Nat.le_of_lt ha) (by omega)
  have hb2 : m * p.val ≤ (2 ^ 32 - 1) * p.val := Nat.mul_le_mul_right _ (by omega)
  have hv : (step p pinv t a b).val < 2 * p.val := by omega
  refine ⟨m, he, ⟨h0, h1, h2, h3, h4, h5, h6, h7, ?_⟩, hv⟩
  have := p.val_lt
  clear he hb1 hb2
  generalize step p pinv t a b = s at *
  simp only [Words.val] at hv
  omega

/-- The CIOS product `a b 2 ^ (-256)` mod `p`, below `2 p`, before its last reduction. -/
@[inline] def mulWords (p : Limbs) (pinv : UInt32) (a b : Limbs) : Words :=
  let t := step p pinv Words.zero a b.l0.toUInt64
  let t := step p pinv t a b.l1.toUInt64
  let t := step p pinv t a b.l2.toUInt64
  let t := step p pinv t a b.l3.toUInt64
  let t := step p pinv t a b.l4.toUInt64
  let t := step p pinv t a b.l5.toUInt64
  let t := step p pinv t a b.l6.toUInt64
  step p pinv t a b.l7.toUInt64

/-- The CIOS product is `a b R⁻¹` mod `p`, small and below `2 p`. -/
theorem mulWords_spec {p : Limbs} {pinv : UInt32}
    (hpinv : (p.l0.toNat * pinv.toNat + 1) % 2 ^ 32 = 0) {a : Limbs} (ha : a.val < p.val)
    (b : Limbs) :
    ∃ k, 2 ^ 256 * (mulWords p pinv a b).val = a.val * b.val + k * p.val ∧
      (mulWords p pinv a b).Small ∧ (mulWords p pinv a b).val < 2 * p.val := by
  have hp := pos_of_pinv hpinv
  have z0 := Words.zero_small
  have z1 : Words.zero.val < 2 * p.val := by rw [Words.zero_val]; omega
  simp only [mulWords]
  obtain ⟨m0, e0, s0, v0⟩ := step_inv hpinv z0 z1 ha (u32 b.l0)
  generalize step p pinv Words.zero a b.l0.toUInt64 = t1 at *
  obtain ⟨m1, e1, s1, v1⟩ := step_inv hpinv s0 v0 ha (u32 b.l1)
  generalize step p pinv t1 a b.l1.toUInt64 = t2 at *
  obtain ⟨m2, e2, s2, v2⟩ := step_inv hpinv s1 v1 ha (u32 b.l2)
  generalize step p pinv t2 a b.l2.toUInt64 = t3 at *
  obtain ⟨m3, e3, s3, v3⟩ := step_inv hpinv s2 v2 ha (u32 b.l3)
  generalize step p pinv t3 a b.l3.toUInt64 = t4 at *
  obtain ⟨m4, e4, s4, v4⟩ := step_inv hpinv s3 v3 ha (u32 b.l4)
  generalize step p pinv t4 a b.l4.toUInt64 = t5 at *
  obtain ⟨m5, e5, s5, v5⟩ := step_inv hpinv s4 v4 ha (u32 b.l5)
  generalize step p pinv t5 a b.l5.toUInt64 = t6 at *
  obtain ⟨m6, e6, s6, v6⟩ := step_inv hpinv s5 v5 ha (u32 b.l6)
  generalize step p pinv t6 a b.l6.toUInt64 = t7 at *
  obtain ⟨m7, e7, s7, v7⟩ := step_inv hpinv s6 v6 ha (u32 b.l7)
  generalize step p pinv t7 a b.l7.toUInt64 = t8 at *
  refine ⟨m0 + 2 ^ 32 * (m1 + 2 ^ 32 * (m2 + 2 ^ 32 * (m3 + 2 ^ 32 * (m4 + 2 ^ 32 * (m5 +
      2 ^ 32 * (m6 + 2 ^ 32 * (m7))))))), ?_, s7, v7⟩
  rw [Words.zero_val] at e0
  rw [Limbs.mul_val]
  simp only [UInt32.toNat_toUInt64] at *
  clear s0 v0 s1 v1 s2 v2 s3 v3 s4 v4 s5 v5 s6 v6 s7 v7 z0 z1
  grind

/-- The low 8 words of `x` minus `p`, and the borrow out of them as the top word. -/
@[inline] def subWords (x : Words) (p : Limbs) : Words :=
  let d0 := sbb x.w0 p.l0.toUInt64 0
  let d1 := sbb x.w1 p.l1.toUInt64 d0.2
  let d2 := sbb x.w2 p.l2.toUInt64 d1.2
  let d3 := sbb x.w3 p.l3.toUInt64 d2.2
  let d4 := sbb x.w4 p.l4.toUInt64 d3.2
  let d5 := sbb x.w5 p.l5.toUInt64 d4.2
  let d6 := sbb x.w6 p.l6.toUInt64 d5.2
  let d7 := sbb x.w7 p.l7.toUInt64 d6.2
  ⟨d0.1, d1.1, d2.1, d3.1, d4.1, d5.1, d6.1, d7.1, d7.2⟩

/-- The words of `x - p` write the difference, with the borrow on top. -/
theorem subWords_spec {x : Words} (hx : x.Small) (p : Limbs) :
    (subWords x p).Small ∧
      (subWords x p).low + p.val = x.low + 2 ^ 256 * (subWords x p).w8.toNat ∧
      (subWords x p).w8.toNat ≤ 1 := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8⟩ := hx
  simp only [subWords]
  generalize hd0 : sbb x.w0 p.l0.toUInt64 (0 : UInt64) = d0
  obtain ⟨ed0, ld0, bd0⟩ := sbb_spec hx0 (u32 p.l0) z1
  rw [hd0] at ed0 ld0 bd0
  generalize hd1 : sbb x.w1 p.l1.toUInt64 d0.2 = d1
  obtain ⟨ed1, ld1, bd1⟩ := sbb_spec hx1 (u32 p.l1) bd0
  rw [hd1] at ed1 ld1 bd1
  generalize hd2 : sbb x.w2 p.l2.toUInt64 d1.2 = d2
  obtain ⟨ed2, ld2, bd2⟩ := sbb_spec hx2 (u32 p.l2) bd1
  rw [hd2] at ed2 ld2 bd2
  generalize hd3 : sbb x.w3 p.l3.toUInt64 d2.2 = d3
  obtain ⟨ed3, ld3, bd3⟩ := sbb_spec hx3 (u32 p.l3) bd2
  rw [hd3] at ed3 ld3 bd3
  generalize hd4 : sbb x.w4 p.l4.toUInt64 d3.2 = d4
  obtain ⟨ed4, ld4, bd4⟩ := sbb_spec hx4 (u32 p.l4) bd3
  rw [hd4] at ed4 ld4 bd4
  generalize hd5 : sbb x.w5 p.l5.toUInt64 d4.2 = d5
  obtain ⟨ed5, ld5, bd5⟩ := sbb_spec hx5 (u32 p.l5) bd4
  rw [hd5] at ed5 ld5 bd5
  generalize hd6 : sbb x.w6 p.l6.toUInt64 d5.2 = d6
  obtain ⟨ed6, ld6, bd6⟩ := sbb_spec hx6 (u32 p.l6) bd5
  rw [hd6] at ed6 ld6 bd6
  generalize hd7 : sbb x.w7 p.l7.toUInt64 d6.2 = d7
  obtain ⟨ed7, ld7, bd7⟩ := sbb_spec hx7 (u32 p.l7) bd6
  rw [hd7] at ed7 ld7 bd7
  refine ⟨⟨ld0, ld1, ld2, ld3, ld4, ld5, ld6, ld7, Nat.lt_of_le_of_lt bd7 (by decide)⟩, ?_, bd7⟩
  clear hd0 ld0 bd0 hd1 ld1 bd1 hd2 ld2 bd2 hd3 ld3 bd3 hd4 ld4 bd4 hd5 ld5 bd5 hd6 ld6 bd6 hd7 ld7
  clear bd7 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8
  simp only [Words.low, Limbs.val, UInt32.toNat_toUInt64, UInt64.toNat_zero, Nat.add_zero] at *
  grind

/-- `x - p` when `x ≥ p`, else `x`, for `x < 2 p`. -/
@[inline] def reduce (p : Limbs) (x : Words) : Limbs :=
  let d := subWords x p
  -- The borrow exceeds the top word of `x` exactly when `x < p`.
  if x.w8 < d.w8 then x.trunc else d.trunc

/-- The final reduction gives the value mod `p`. -/
theorem reduce_spec {p : Limbs} {x : Words} (hx : x.Small) (hv : x.val < 2 * p.val) :
    (reduce p x).val = x.val % p.val := by
  obtain ⟨ds, de, db⟩ := subWords_spec hx p
  have hX := x.val_eq
  have hlx := x.low_lt hx
  have hld := (subWords x p).low_lt ds
  have hp := p.val_lt
  simp only [reduce]
  split
  · rename_i h
    rw [Words.trunc_val hx]
    have h' : x.w8.toNat < (subWords x p).w8.toNat := h
    have : x.val < p.val := by omega
    rw [Nat.mod_eq_of_lt this]
    omega
  · rename_i h
    rw [Words.trunc_val ds]
    have h' : ¬ x.w8.toNat < (subWords x p).w8.toNat := h
    have : p.val ≤ x.val := by omega
    rw [Nat.mod_eq_sub_mod this, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `a + b`, as limbs and a carry word. -/
@[inline] def addWords (a b : Limbs) : Words :=
  let s0 := mac a.l0.toUInt64 b.l0.toUInt64 1 0
  let s1 := mac a.l1.toUInt64 b.l1.toUInt64 1 s0.2
  let s2 := mac a.l2.toUInt64 b.l2.toUInt64 1 s1.2
  let s3 := mac a.l3.toUInt64 b.l3.toUInt64 1 s2.2
  let s4 := mac a.l4.toUInt64 b.l4.toUInt64 1 s3.2
  let s5 := mac a.l5.toUInt64 b.l5.toUInt64 1 s4.2
  let s6 := mac a.l6.toUInt64 b.l6.toUInt64 1 s5.2
  let s7 := mac a.l7.toUInt64 b.l7.toUInt64 1 s6.2
  ⟨s0.1, s1.1, s2.1, s3.1, s4.1, s5.1, s6.1, s7.1, s7.2⟩

/-- The words of `a + b` are small and write the sum. -/
theorem addWords_spec (a b : Limbs) :
    (addWords a b).Small ∧ (addWords a b).val = a.val + b.val := by
  simp only [addWords]
  generalize hs0 : mac a.l0.toUInt64 b.l0.toUInt64 1 (0 : UInt64) = s0
  obtain ⟨es0, ls0, cs0⟩ := mac_spec (u32 a.l0) (u32 b.l0) o64 z64
  rw [hs0] at es0 ls0 cs0
  generalize hs1 : mac a.l1.toUInt64 b.l1.toUInt64 1 s0.2 = s1
  obtain ⟨es1, ls1, cs1⟩ := mac_spec (u32 a.l1) (u32 b.l1) o64 cs0
  rw [hs1] at es1 ls1 cs1
  generalize hs2 : mac a.l2.toUInt64 b.l2.toUInt64 1 s1.2 = s2
  obtain ⟨es2, ls2, cs2⟩ := mac_spec (u32 a.l2) (u32 b.l2) o64 cs1
  rw [hs2] at es2 ls2 cs2
  generalize hs3 : mac a.l3.toUInt64 b.l3.toUInt64 1 s2.2 = s3
  obtain ⟨es3, ls3, cs3⟩ := mac_spec (u32 a.l3) (u32 b.l3) o64 cs2
  rw [hs3] at es3 ls3 cs3
  generalize hs4 : mac a.l4.toUInt64 b.l4.toUInt64 1 s3.2 = s4
  obtain ⟨es4, ls4, cs4⟩ := mac_spec (u32 a.l4) (u32 b.l4) o64 cs3
  rw [hs4] at es4 ls4 cs4
  generalize hs5 : mac a.l5.toUInt64 b.l5.toUInt64 1 s4.2 = s5
  obtain ⟨es5, ls5, cs5⟩ := mac_spec (u32 a.l5) (u32 b.l5) o64 cs4
  rw [hs5] at es5 ls5 cs5
  generalize hs6 : mac a.l6.toUInt64 b.l6.toUInt64 1 s5.2 = s6
  obtain ⟨es6, ls6, cs6⟩ := mac_spec (u32 a.l6) (u32 b.l6) o64 cs5
  rw [hs6] at es6 ls6 cs6
  generalize hs7 : mac a.l7.toUInt64 b.l7.toUInt64 1 s6.2 = s7
  obtain ⟨es7, ls7, cs7⟩ := mac_spec (u32 a.l7) (u32 b.l7) o64 cs6
  rw [hs7] at es7 ls7 cs7
  refine ⟨⟨ls0, ls1, ls2, ls3, ls4, ls5, ls6, ls7, cs7⟩, ?_⟩
  clear hs0 ls0 cs0 hs1 ls1 cs1 hs2 ls2 cs2 hs3 ls3 cs3 hs4 ls4 cs4 hs5 ls5 cs5 hs6 ls6 cs6 hs7 ls7
  clear cs7
  simp only [Words.val, Limbs.val, UInt32.toNat_toUInt64, UInt64.toNat_one, Nat.mul_one,
    UInt64.toNat_zero, Nat.add_zero] at *
  grind

/-- The limbs with a zero word above them. -/
@[inline] def Limbs.toWords (a : Limbs) : Words :=
  ⟨a.l0.toUInt64, a.l1.toUInt64, a.l2.toUInt64, a.l3.toUInt64, a.l4.toUInt64, a.l5.toUInt64,
      a.l6.toUInt64, a.l7.toUInt64, 0⟩

/-- The words of limbs are small. -/
theorem Limbs.toWords_small (a : Limbs) : a.toWords.Small := by
  simp only [toWords, Words.Small, UInt32.toNat_toUInt64, UInt64.toNat_zero, UInt32.toNat_lt,
    Nat.two_pow_pos, and_self]

/-- The words of limbs write their integer. -/
theorem Limbs.toWords_low (a : Limbs) : a.toWords.low = a.val := by
  simp only [toWords, Words.low, val, UInt32.toNat_toUInt64]

/-- `a - b` when `a ≥ b`, else `a - b + p`. -/
@[inline] def subLimbs (p a b : Limbs) : Limbs :=
  let d := subWords a.toWords b
  if d.w8 = 0 then d.trunc else (addWords d.trunc p).trunc

/-- The difference of `a` and `b` below `p` is `a - b` mod `p`. -/
theorem subLimbs_spec {p a b : Limbs} (ha : a.val < p.val) (hb : b.val < p.val) :
    (subLimbs p a b).val = (a.val + p.val - b.val) % p.val := by
  obtain ⟨ds, de, db⟩ := subWords_spec a.toWords_small b
  rw [Limbs.toWords_low] at de
  have hld := (subWords a.toWords b).low_lt ds
  have hp := p.val_lt
  simp only [subLimbs]
  split
  · rename_i h
    have h' : (subWords a.toWords b).w8.toNat = 0 := by rw [h]; rfl
    rw [Words.trunc_val ds, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rename_i h
    have h' : (subWords a.toWords b).w8.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp h0)
    obtain ⟨es, ev⟩ := addWords_spec (subWords a.toWords b).trunc p
    rw [Words.trunc_val ds] at ev
    have hX := (addWords (subWords a.toWords b).trunc p).val_eq
    have hle := (addWords (subWords a.toWords b).trunc p).low_lt es
    rw [Words.trunc_val es, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Whether `a < b`: the subtraction `a - b` borrows. -/
@[inline] def Limbs.lt (a b : Limbs) : Bool :=
  (subWords a.toWords b).w8 != 0

/-- The comparison of limbs is the comparison of their integers. -/
theorem Limbs.lt_iff (a b : Limbs) : a.lt b = true ↔ a.val < b.val := by
  obtain ⟨ds, de, db⟩ := subWords_spec a.toWords_small b
  rw [Limbs.toWords_low] at de
  have hld := (subWords a.toWords b).low_lt ds
  have ha := a.val_lt
  have hb := b.val_lt
  simp only [Limbs.lt, bne_iff_ne, ne_eq]
  rw [← UInt64.toNat_inj, UInt64.toNat_zero]
  omega

/-- The four bytes of `b` from `i`, read big-endian.

A byte past the end reads as `0`. -/
@[inline] def Limbs.word (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 * 16777216 + b[i + 1]!.toUInt32 * 65536 + b[i + 2]!.toUInt32 * 256 +
    b[i + 3]!.toUInt32

/-- The 32 bytes of `b` from `off`, read big-endian.

A byte past the end reads as `0`. -/
@[inline] def Limbs.ofBytesBE (b : ByteArray) (off : Nat) : Limbs :=
  ⟨word b (off + 28), word b (off + 24), word b (off + 20), word b (off + 16), word b (off + 12),
    word b (off + 8), word b (off + 4), word b off⟩

/-- The integer as 32 bytes, big-endian. -/
def Limbs.toBytesBE (a : Limbs) : ByteArray :=
  ⟨#[(a.l7 >>> 24).toUInt8, (a.l7 >>> 16).toUInt8, (a.l7 >>> 8).toUInt8, a.l7.toUInt8,
    (a.l6 >>> 24).toUInt8, (a.l6 >>> 16).toUInt8, (a.l6 >>> 8).toUInt8, a.l6.toUInt8,
    (a.l5 >>> 24).toUInt8, (a.l5 >>> 16).toUInt8, (a.l5 >>> 8).toUInt8, a.l5.toUInt8,
    (a.l4 >>> 24).toUInt8, (a.l4 >>> 16).toUInt8, (a.l4 >>> 8).toUInt8, a.l4.toUInt8,
    (a.l3 >>> 24).toUInt8, (a.l3 >>> 16).toUInt8, (a.l3 >>> 8).toUInt8, a.l3.toUInt8,
    (a.l2 >>> 24).toUInt8, (a.l2 >>> 16).toUInt8, (a.l2 >>> 8).toUInt8, a.l2.toUInt8,
    (a.l1 >>> 24).toUInt8, (a.l1 >>> 16).toUInt8, (a.l1 >>> 8).toUInt8, a.l1.toUInt8,
    (a.l0 >>> 24).toUInt8, (a.l0 >>> 16).toUInt8, (a.l0 >>> 8).toUInt8, a.l0.toUInt8]⟩

/-- An odd modulus `p` below `2 ^ 256`, with the constants of its Montgomery arithmetic.

The Montgomery radix is `R = 2 ^ 256`. -/
structure Modulus where
  /-- The modulus. -/
  p : Nat
  /-- The limbs of the modulus. -/
  pLimbs : Limbs
  /-- `-p⁻¹ mod 2 ^ 32`. -/
  pinv : UInt32
  /-- `R mod p`, the form of `1`. -/
  r1 : Limbs
  /-- `R ^ 2 mod p`, which puts an integer into Montgomery form. -/
  r2 : Limbs
  /-- `R ^ 3 mod p`, which puts an inverse into Montgomery form. -/
  r3 : Limbs
  pLimbs_spec : pLimbs.val = p
  pinv_spec : (pLimbs.l0.toNat * pinv.toNat + 1) % 2 ^ 32 = 0
  r1_spec : r1.val = 2 ^ 256 % p
  r2_spec : r2.val = 2 ^ 256 * 2 ^ 256 % p
  r3_spec : r3.val = 2 ^ 256 * 2 ^ 256 * 2 ^ 256 % p

end Montgomery

open Montgomery in
/-- An integer mod `M.p` in Montgomery form.

The limbs hold `a R mod p` for the integer `a` that the element stands for.

They are below `p`, so each element has exactly one form. -/
structure Montgomery (M : Montgomery.Modulus) where
  /-- `a R mod p`. -/
  limbs : Limbs
  lt : limbs.val < M.p
deriving DecidableEq

namespace Montgomery

variable {M : Modulus}

/-- The modulus is positive. -/
theorem Modulus.pos (M : Modulus) : 0 < M.p := M.pLimbs_spec ▸ pos_of_pinv M.pinv_spec

/-- A bound by the modulus is a bound by its limbs. -/
theorem Modulus.lt_pLimbs (M : Modulus) {x : Nat} (h : x < M.p) : x < M.pLimbs.val := by
  rw [M.pLimbs_spec]
  exact h

/-- `R mod p` is below `p`. -/
theorem Modulus.r1_lt (M : Modulus) : M.r1.val < M.p := by
  rw [M.r1_spec]
  exact Nat.mod_lt _ M.pos

/-- `R ^ 2 mod p` is below `p`. -/
theorem Modulus.r2_lt (M : Modulus) : M.r2.val < M.p := by
  rw [M.r2_spec]
  exact Nat.mod_lt _ M.pos

/-- `R ^ 3 mod p` is below `p`. -/
theorem Modulus.r3_lt (M : Modulus) : M.r3.val < M.p := by
  rw [M.r3_spec]
  exact Nat.mod_lt _ M.pos

/-- The Montgomery product of `a`, below `p`, and `b`: `a b R⁻¹ mod p`. -/
@[inline] def mulLimbs (M : Modulus) (a : Limbs) (ha : a.val < M.p) (b : Limbs) :
    Montgomery M :=
  ⟨reduce M.pLimbs (mulWords M.pLimbs M.pinv a b), by
    obtain ⟨_, _, hs, hv⟩ := mulWords_spec M.pinv_spec (M.lt_pLimbs ha) b
    rw [reduce_spec hs hv, M.pLimbs_spec]
    exact Nat.mod_lt _ M.pos⟩

/-- Zero. -/
@[inline] def zero : Montgomery M :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩, M.pos⟩

/-- One, whose form is `R mod p`. -/
@[inline] def one : Montgomery M :=
  ⟨M.r1, M.r1_lt⟩

/-- `a + b mod p`. -/
@[inline] def add (a b : Montgomery M) : Montgomery M :=
  ⟨reduce M.pLimbs (addWords a.limbs b.limbs), by
    obtain ⟨hs, hv⟩ := addWords_spec a.limbs b.limbs
    have := a.lt
    have := b.lt
    rw [reduce_spec hs (by rw [M.pLimbs_spec]; omega), M.pLimbs_spec]
    exact Nat.mod_lt _ M.pos⟩

/-- `a - b mod p`. -/
@[inline] def sub (a b : Montgomery M) : Montgomery M :=
  ⟨subLimbs M.pLimbs a.limbs b.limbs, by
    rw [subLimbs_spec (M.lt_pLimbs a.lt) (M.lt_pLimbs b.lt), M.pLimbs_spec]
    exact Nat.mod_lt _ M.pos⟩

/-- `-a mod p`. -/
@[inline] def neg (a : Montgomery M) : Montgomery M :=
  sub zero a

/-- `a b mod p`, by the Montgomery product of the two forms. -/
@[inline] def mul (a b : Montgomery M) : Montgomery M :=
  mulLimbs M a.limbs a.lt b.limbs

/-- The element that stands for `n mod p`.

The Montgomery product with `R ^ 2 mod p` turns `n` into `n R mod p`. -/
def ofNat (n : Nat) : Montgomery M :=
  mulLimbs M M.r2 M.r2_lt (Limbs.ofNat (n % M.p))

/-- The limbs of `1`. -/
def Limbs.one : Limbs := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- The integer below `p` that the element stands for.

The Montgomery product with `1` turns `a R` into `a`. -/
def toNat (a : Montgomery M) : Nat :=
  (mulLimbs M a.limbs a.lt Limbs.one).limbs.val

/-- The inverse of `a`, and `0` for `0`.

The Euclidean algorithm inverts the form `a R`, which gives `a⁻¹ R⁻¹`.

The Montgomery product with `R ^ 3 mod p` turns it into `a⁻¹ R`. -/
def inv (a : Montgomery M) : Montgomery M :=
  haveI : NeZero M.p := ⟨Nat.pos_iff_ne_zero.mp M.pos⟩
  mulLimbs M M.r3 M.r3_lt (Limbs.ofNat (Fin.inverse (⟨a.limbs.val, a.lt⟩ : Fin M.p)).val)

/-- `a ^ n`, by square and multiply. -/
def pow (a : Montgomery M) (n : Nat) : Montgomery M :=
  if n = 0 then one
  else
    let half := pow (mul a a) (n / 2)
    if n % 2 = 1 then mul a half else half
termination_by n
decreasing_by omega

/-- The element of the 32 bytes of `b` from `off`, read big-endian.

It is `none` when they write an integer of at least `p`. -/
def ofBytesBE (b : ByteArray) (off : Nat) : Option (Montgomery M) :=
  let l := Limbs.ofBytesBE b off
  if l.lt M.pLimbs then some (mulLimbs M M.r2 M.r2_lt l) else none

/-- The integer that the element stands for, as 32 bytes, big-endian. -/
def toBytesBE (a : Montgomery M) : ByteArray :=
  (mulLimbs M a.limbs a.lt Limbs.one).limbs.toBytesBE

instance : Zero (Montgomery M) := ⟨zero⟩
instance : One (Montgomery M) := ⟨one⟩
instance : Add (Montgomery M) := ⟨add⟩
instance : Sub (Montgomery M) := ⟨sub⟩
instance : Neg (Montgomery M) := ⟨neg⟩
instance : Mul (Montgomery M) := ⟨mul⟩
instance : Inv (Montgomery M) := ⟨inv⟩
instance : Pow (Montgomery M) Nat := ⟨pow⟩
instance : NatCast (Montgomery M) := ⟨ofNat⟩
instance : Inhabited (Montgomery M) := ⟨zero⟩

end Montgomery


end EthLib.Cryptography
