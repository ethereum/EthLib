module

public import EthLib.Cryptography.Bls.Fp2
public import EthLib.Cryptography.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.FpZMod
public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.FpModel
public import EthLib.Cryptography.Proofs.Bls.BaseFieldMap
public import EthLib.Cryptography.Proofs.Fp2
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Proofs: `Fp2`

`Fp2` is the quadratic extension `Fp[i] / (i^2 + 1)`.

This file proves that it is a field, with the library's own operations.

It also proves that the library's exponentiation is the field power.

A square root that it returns squares back to its input.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Fp2

open Cryptography.Fp2 (c0 c1 beq isZero conjugate inverse)

/-! ## Extensionality and basic projections -/

@[ext]
theorem ext {a b : Fp2} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

@[simp] theorem zero_eq_zero : zero = (0 : Fp2) := rfl
@[simp] theorem one_eq_one : one = (1 : Fp2) := rfl

@[simp] theorem zero_c0 : (0 : Fp2).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2).c1 = 0 := rfl
@[simp] theorem i_c0 : (i : Fp2).c0 = 0 := rfl
@[simp] theorem i_c1 : (i : Fp2).c1 = 1 := rfl
@[simp] theorem ofFp_c0 (x : Fp) : (ofFp x).c0 = x := rfl
@[simp] theorem ofFp_c1 (x : Fp) : (ofFp x).c1 = 0 := rfl

@[simp] theorem add_c0 (a b : Fp2) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp2) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp2) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp2) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl
@[simp] theorem conjugate_c0 (a : Fp2) : a.conjugate.c0 = a.c0 := rfl
@[simp] theorem conjugate_c1 (a : Fp2) : a.conjugate.c1 = -a.c1 := rfl

/-! ## Boolean equality and zero check -/

theorem beq_iff_eq {a b : Fp2} : a.beq b = true ↔ a = b :=
  Cryptography.Fp2.beq_iff Fp.embedding

theorem isZero_iff {a : Fp2} : a.isZero = true ↔ a = 0 :=
  Cryptography.Fp2.isZero_iff Fp.embedding

/-! ## Ring axioms and `CommRing Fp2` -/

section RingLaws

protected theorem add_comm (a b : Fp2) : a + b = b + a :=
  Cryptography.Fp2.add_comm Fp.embedding a b

protected theorem add_assoc (a b c : Fp2) : a + b + c = a + (b + c) :=
  Cryptography.Fp2.add_assoc Fp.embedding a b c

protected theorem zero_add (a : Fp2) : 0 + a = a :=
  Cryptography.Fp2.zero_add Fp.embedding a

protected theorem add_zero (a : Fp2) : a + 0 = a :=
  Cryptography.Fp2.add_zero Fp.embedding a

protected theorem neg_add_cancel (a : Fp2) : -a + a = 0 :=
  Cryptography.Fp2.neg_add_cancel Fp.embedding a

protected theorem sub_eq_add_neg (a b : Fp2) : a - b = a + -b :=
  Cryptography.Fp2.sub_eq_add_neg Fp.embedding a b

protected theorem mul_comm (a b : Fp2) : a * b = b * a :=
  Cryptography.Fp2.mul_comm Fp.embedding a b

protected theorem mul_assoc (a b c : Fp2) : a * b * c = a * (b * c) :=
  Cryptography.Fp2.mul_assoc Fp.embedding a b c

protected theorem one_mul (a : Fp2) : 1 * a = a :=
  Cryptography.Fp2.one_mul Fp.embedding a

protected theorem mul_one (a : Fp2) : a * 1 = a :=
  Cryptography.Fp2.mul_one Fp.embedding a

protected theorem zero_mul (a : Fp2) : 0 * a = 0 :=
  Cryptography.Fp2.zero_mul Fp.embedding a

protected theorem mul_zero (a : Fp2) : a * 0 = 0 :=
  Cryptography.Fp2.mul_zero Fp.embedding a

protected theorem left_distrib (a b c : Fp2) : a * (b + c) = a * b + a * c :=
  Cryptography.Fp2.left_distrib Fp.embedding a b c

protected theorem right_distrib (a b c : Fp2) : (a + b) * c = a * c + b * c :=
  Cryptography.Fp2.right_distrib Fp.embedding a b c

instance : AddCommGroup Fp2 where
  add_assoc := Fp2.add_assoc
  zero_add := Fp2.zero_add
  add_zero := Fp2.add_zero
  neg_add_cancel := Fp2.neg_add_cancel
  add_comm := Fp2.add_comm
  sub_eq_add_neg := Fp2.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : CommRing Fp2 where
  left_distrib := Fp2.left_distrib
  right_distrib := Fp2.right_distrib
  zero_mul := Fp2.zero_mul
  mul_zero := Fp2.mul_zero
  mul_assoc := Fp2.mul_assoc
  one_mul := Fp2.one_mul
  mul_one := Fp2.mul_one
  mul_comm := Fp2.mul_comm

/-! ## Basis, non-residue, conjugation, and norm -/

theorem i_sq : (i : Fp2) * i = -1 := by
  apply ext <;> apply Fp.toZMod.injective <;> simp

/-- The element `xi = 1 + i`.

It is not a cube in `Fp2`, so `Fp6` adjoins a cube root of it.
-/
def xi : Fp2 := ⟨1, 1⟩

@[simp]
theorem mulByOnePlusI_eq (a : Fp2) : a.mulByOnePlusI = a * xi := by
  apply ext <;> apply Fp.toZMod.injective <;> simp [mulByOnePlusI, xi]

theorem conjugate_add (a b : Fp2) : (a + b).conjugate = a.conjugate + b.conjugate := by
  apply ext <;> apply Fp.toZMod.injective
  · simp
  · simp; ring

theorem conjugate_sub (a b : Fp2) : (a - b).conjugate = a.conjugate - b.conjugate := by
  apply ext <;> apply Fp.toZMod.injective
  · simp
  · simp; ring

theorem conjugate_neg (a : Fp2) : (-a).conjugate = -a.conjugate := by
  apply ext <;> apply Fp.toZMod.injective <;> simp

theorem conjugate_mul (a b : Fp2) : (a * b).conjugate = a.conjugate * b.conjugate := by
  apply ext <;> apply Fp.toZMod.injective
  · simp
  · simp; ring

@[simp]
theorem conjugate_conjugate (a : Fp2) : a.conjugate.conjugate = a := by
  apply ext <;> apply Fp.toZMod.injective <;> simp

/-- The norm `N(c0 + c1*i) = c0^2 + c1^2`, an element of `Fp`.

It equals `a * conjugate a`, and it is multiplicative.
-/
def norm (a : Fp2) : Fp := a.c0 * a.c0 + a.c1 * a.c1

theorem mul_conjugate_eq_norm (a : Fp2) : a * a.conjugate = ofFp (norm a) := by
  apply ext <;> apply Fp.toZMod.injective
  · simp [norm]
  · simp; ring

theorem conjugate_mul_eq_norm (a : Fp2) : a.conjugate * a = ofFp (norm a) := by
  rw [Fp2.mul_comm, mul_conjugate_eq_norm]

theorem norm_mul (a b : Fp2) : norm (a * b) = norm a * norm b := by
  apply Fp.toZMod.injective
  simp only [norm, mul_c0, mul_c1]
  push_toZMod
  ring

@[simp] theorem norm_zero : norm 0 = 0 := by
  apply Fp.toZMod.injective
  simp [norm]
@[simp] theorem norm_one : norm 1 = 1 := by
  apply Fp.toZMod.injective
  simp [norm]
@[simp] theorem norm_conjugate (a : Fp2) : norm a.conjugate = norm a := by
  apply Fp.toZMod.injective
  simp [norm]

end RingLaws

/-! ## Non-squareness of `-1` in `Fp` and `Fp2.inverse` correctness -/

/-- `-1` is not a square mod `p`, since `p = 3 mod 4`. -/
private theorem sq_ne_neg_one_zmod (y : ZMod Fp.modulus) : y * y ≠ -1 :=
  Cryptography.Fp2.zmod_mul_self_ne_neg_one (by decide) y

/-- `-1` is not a square in `Fp`, because `p = 3 mod 4`. -/
theorem sq_ne_neg_one (y : Fp) : y * y ≠ -1 := fun h =>
  sq_ne_neg_one_zmod (Fp.toZMod y) (by rw [← Fp.toZMod_mul, h, Fp.toZMod_neg, Fp.toZMod_one])

/-- The norm is zero only at zero. -/
theorem norm_eq_zero_iff (a : Fp2) : norm a = 0 ↔ a = 0 := by
  -- Every element `a = c0 + c1*i` has a norm `N(a) = c0^2 + c1^2` in `Fp`.
  --
  -- The norm is zero only at zero, because `-1` is not a square in `Fp`.
  --
  -- That holds since `p = 3 mod 4`.
  constructor
  · intro h
    have h' := congrArg Fp.toZMod h
    simp only [norm, Fp.toZMod_add, Fp.toZMod_mul, Fp.toZMod_zero] at h'
    obtain ⟨h0, h1⟩ := Cryptography.Fp2.norm_eq_zero sq_ne_neg_one_zmod h'
    apply ext <;> apply Fp.toZMod.injective <;> simp [h0, h1]
  · rintro rfl
    exact norm_zero

theorem norm_ne_zero_iff (a : Fp2) : norm a ≠ 0 ↔ a ≠ 0 :=
  not_congr (norm_eq_zero_iff a)

private theorem fp_mul_inverse {x : Fp} (hx : x ≠ 0) :
    Fp.toZMod x * Fp.toZMod x.inverse = 1 := by
  rw [Fp.toZMod_inverse]
  exact mul_inv_cancel₀ fun h => hx (Fp.toZMod_inj.mp (h.trans Fp.toZMod_zero.symm))

theorem mul_inverse_cancel {a : Fp2} (h : a ≠ 0) : a * a.inverse = 1 :=
  -- The norm is zero only at zero, so every nonzero element is invertible.
  Cryptography.Fp2.mul_inverse_cancel Fp.embedding sq_ne_neg_one_zmod h

theorem mul_inverse_of_norm_ne_zero {a : Fp2} (h : norm a ≠ 0) :
    a * a.inverse = 1 :=
  mul_inverse_cancel ((norm_ne_zero_iff a).mp h)

theorem inverse_mul_cancel {a : Fp2} (h : a ≠ 0) : a.inverse * a = 1 := by
  rw [Fp2.mul_comm, mul_inverse_cancel h]

@[simp]
theorem inverse_zero : (0 : Fp2).inverse = 0 :=
  Cryptography.Fp2.inverse_zero Fp.embedding

instance : Field Fp2 where
  inv := inverse
  exists_pair_ne := ⟨0, 1, Cryptography.Fp2.zero_ne_one Fp.embedding⟩
  mul_inv_cancel := fun a h => mul_inverse_cancel h
  inv_zero := inverse_zero
  div_eq_mul_inv := fun _ _ => rfl
  nnqsmul := _
  qsmul := _

/-- `Fp2` maps into itself, as a field of Mathlib, by the identity. -/
def embedding : FieldOps.Embedding Fp2 Fp2 where
  toFun a := a
  injective := fun _ _ h => h
  map_add _ _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl
  map_neg _ := rfl
  map_zero := rfl
  map_one := rfl
  map_inverse _ := rfl
  beq_iff _ _ := beq_iff_eq
  isZero_iff _ := isZero_iff

/-! ## Exponentiation (`powNat`) -/

theorem powNat_eq_pow (a : Fp2) (e : Nat) : powNat a e = a ^ e :=
  Cryptography.Fp2.powNat_eq_npow _ rfl (fun _ _ => rfl) a e

theorem powNat_zero (a : Fp2) : powNat a 0 = one := by
  rw [powNat_eq_pow, pow_zero, one_eq_one]

theorem powNat_one (a : Fp2) : powNat a 1 = a := by
  rw [powNat_eq_pow, pow_one]

theorem powNat_succ (a : Fp2) (e : Nat) : powNat a (e + 1) = a * powNat a e := by
  rw [powNat_eq_pow, powNat_eq_pow, pow_succ']

/-! ## Square-root soundness -/

private theorem c0_ne_zero_zmod {a0 a1 s' c0 inv2 : ZMod Fp.modulus}
    (ha1 : a1 ≠ 0)
    (hs : s' * s' = a0 * a0 + a1 * a1)
    (h2inv : (2 : ZMod Fp.modulus) * inv2 = 1)
    (hc0 : c0 * c0 = (a0 + s') * inv2) :
    (2 : ZMod Fp.modulus) * c0 ≠ 0 := by
  have h2ne : (2 : ZMod Fp.modulus) ≠ 0 := by decide
  have hc0_2 : 2 * (c0 * c0) = a0 + s' := by
    linear_combination 2 * hc0 + (a0 + s') * h2inv
  have hc0_ne : c0 ≠ 0 := by
    intro hc00
    have h0 : a0 + s' = 0 := by
      linear_combination -hc0_2 + 2 * c0 * hc00
    have ha1_sq : a1 * a1 = 0 := by
      linear_combination -hs + (s' - a0) * h0
    exact ha1 (mul_self_eq_zero.mp ha1_sq)
  exact mul_ne_zero h2ne hc0_ne

private theorem sqrt_c0_zmod {a0 a1 s' c0 w inv2 : ZMod Fp.modulus}
    (hs : s' * s' = a0 * a0 + a1 * a1)
    (h2inv : (2 : ZMod Fp.modulus) * inv2 = 1)
    (hc0 : c0 * c0 = (a0 + s') * inv2)
    (h2c0_inv : (2 * c0) * w = 1) :
    c0 * c0 - (a1 * w) * (a1 * w) = a0 := by
  have hc0_2 : 2 * (c0 * c0) = a0 + s' := by
    linear_combination 2 * hc0 + (a0 + s') * h2inv
  linear_combination
    w * w * hs
    + w * w * (2 * c0 * c0 - a0 + s') * hc0_2
    - (c0 * c0 - a0) * (2 * c0 * w + 1) * h2c0_inv

private theorem sqrt_c1_zmod {a1 c0 w : ZMod Fp.modulus}
    (h2c0_inv : (2 * c0) * w = 1) :
    c0 * (a1 * w) + (a1 * w) * c0 = a1 := by
  linear_combination a1 * h2c0_inv

private theorem two_mul_inverse : (2 : ZMod Fp.modulus) * Fp.toZMod (Fp.ofNat 2).inverse = 1 := by
  have h := fp_mul_inverse (x := Fp.ofNat 2) (Fp.ne_of_model (by
    simp only [Fp.toModel_ofNat, Fp.toModel_zero']
    decide +kernel))
  push_toZMod at h
  exact h

private theorem sqrt_branch_gen_aux {invFn : Fp → Fp}
    (hinv : ∀ x : Fp, x ≠ 0 → Fp.toZMod x * Fp.toZMod (invFn x) = 1)
    {a0 a1 s' c0 inv2 : Fp}
    (ha1 : a1 ≠ 0)
    (hs : s' * s' = a0 * a0 + a1 * a1)
    (h2inv : (2 : ZMod Fp.modulus) * Fp.toZMod inv2 = 1)
    (hc0 : c0 * c0 = (a0 + s') * inv2) :
    let w := invFn (Fp.ofNat 2 * c0)
    (⟨c0, a1 * w⟩ : Fp2) * ⟨c0, a1 * w⟩ = ⟨a0, a1⟩ := by
  intro w
  have hs' := congrArg Fp.toZMod hs
  have hc0' := congrArg Fp.toZMod hc0
  push_toZMod at hs' hc0'
  have ha1' : Fp.toZMod a1 ≠ 0 := fun h => ha1 (Fp.toZMod_inj.mp (h.trans Fp.toZMod_zero.symm))
  have h2c0_ne : (Fp.ofNat 2 * c0 : Fp) ≠ 0 := fun h => by
    have h' := congrArg Fp.toZMod h
    push_toZMod at h'
    exact c0_ne_zero_zmod ha1' hs' h2inv hc0' h'
  have h2c0_inv := hinv (Fp.ofNat 2 * c0) h2c0_ne
  push_toZMod at h2c0_inv
  apply ext <;> apply Fp.toZMod.injective <;> simp only [mul_c0, mul_c1] <;> push_toZMod
  · exact sqrt_c0_zmod hs' h2inv hc0' h2c0_inv
  · exact sqrt_c1_zmod h2c0_inv

/-! ## Sign-bit flip -/

/-- Negating a nonzero `Fp2` element flips its sign bit (`draft-irtf-cfrg-pairing-friendly-curves-07` Appendix C).

When `c1 ≠ 0`, the sign comes from `c1`, which is negated.

When `c1 = 0`, `c0` is nonzero, and the sign comes from `c0`, which is negated.
-/
theorem signBit_neg {y : Fp2} (hy : y ≠ 0) :
    Fp2.signBit (-y) = !Fp2.signBit y := by
  unfold Fp2.signBit
  -- Negation preserves whether the imaginary part is zero.
  have hc1_zero : (-y).c1.isZero = y.c1.isZero := by
    rw [Bool.eq_iff_iff, Fp.isZero_iff, Fp.isZero_iff, Fp2.neg_c1, ← Fp.toZMod_inj,
      Fp.toZMod_neg, Fp.toZMod_zero, neg_eq_zero, ← Fp.toZMod_zero, Fp.toZMod_inj]
  rw [hc1_zero]
  by_cases hc1 : y.c1.isZero = true
  -- When c1 = 0, a nonzero element has c0 != 0, so signBit inspects c0.
  · simp only [hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Fp2.neg_c0]
    have hc1_eq : y.c1 = 0 := Fp.isZero_iff.mp hc1
    have hc0_ne : y.c0 ≠ 0 := fun hc0_eq => hy (Fp2.ext hc0_eq hc1_eq)
    exact G1.signBit_neg hc0_ne
  -- When c1 != 0, signBit inspects c1 directly.
  · simp only [hc1, Bool.not_false, ↓reduceIte, Fp2.neg_c1]
    have hc1_ne : y.c1 ≠ 0 := fun hc1_eq => hc1 (Fp.isZero_iff.mpr hc1_eq)
    exact G1.signBit_neg hc1_ne

/-! ## Square roots by the complex method -/

private theorem sqrt_branch_neg_zmod {a0 a1 s r t w : ZMod Fp.modulus}
    (ha1 : a1 ≠ 0) (hs : s * s = a0 * a0 + a1 * a1)
    (ht : 2 * t = 1) (hr : r * r = -((a0 + s) * t))
    (hw : (2 * r) * w = 1) :
    (a1 * w) * (a1 * w) - r * r = a0 ∧
      (a1 * w) * r + r * (a1 * w) = a1 := by
  have hr' : 2 * r * r + a0 + s = 0 := by
    linear_combination 2 * hr - (a0 + s) * ht
  have hrne : r ≠ 0 := by
    intro hr0
    have ha0 : a0 + s = 0 := by simpa [hr0] using hr'
    have ha1sq : a1 * a1 = 0 := by
      linear_combination -hs + (s - a0) * ha0
    exact ha1 (mul_self_eq_zero.mp ha1sq)
  have hreal : (4 * r * r) * ((a1 * w) * (a1 * w) - r * r - a0) = 0 := by
    linear_combination a1 * a1 * (2 * r * w + 1) * hw -
      (2 * r * r + a0 - s) * hr' - hs
  have hnonzero : (4 : ZMod Fp.modulus) * r * r ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by decide) hrne) hrne
  constructor
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hreal).resolve_left hnonzero)
  · linear_combination a1 * hw

private theorem sqrt_branch_neg_aux {a0 a1 s r t : Fp}
    (ha1 : a1 ≠ 0) (hs : s * s = a0 * a0 + a1 * a1)
    (ht : (2 : ZMod Fp.modulus) * Fp.toZMod t = 1)
    (hr : r * r = -((a0 + s) * t)) :
    (⟨a1 * (Fp.ofNat 2 * r).inverse, r⟩ : Fp2) *
      ⟨a1 * (Fp.ofNat 2 * r).inverse, r⟩ = ⟨a0, a1⟩ := by
  have hs' := congrArg Fp.toZMod hs
  have hr' := congrArg Fp.toZMod hr
  push_toZMod at hs' hr'
  have ha1' : Fp.toZMod a1 ≠ 0 := fun h => ha1 (Fp.toZMod.injective (by simpa using h))
  have hrne : Fp.toZMod r ≠ 0 := by
    intro hr0
    rw [hr0, mul_zero] at hr'
    have ha0 : Fp.toZMod a0 + Fp.toZMod s = 0 := by
      linear_combination 2 * hr' - (Fp.toZMod a0 + Fp.toZMod s) * ht
    have ha1sq : Fp.toZMod a1 * Fp.toZMod a1 = 0 := by
      linear_combination -hs' + (Fp.toZMod s - Fp.toZMod a0) * ha0
    exact ha1' (mul_self_eq_zero.mp ha1sq)
  have hw : (2 * Fp.toZMod r) * Fp.toZMod (Fp.ofNat 2 * r).inverse = 1 := by
    rw [Fp.toZMod_inverse, Fp.toZMod_mul, Fp.toZMod_ofNat]
    exact mul_inv_cancel₀ (mul_ne_zero (by decide) hrne)
  have hout := sqrt_branch_neg_zmod ha1' hs' ht hr' hw
  apply ext <;> apply Fp.toZMod.injective <;> simp only [mul_c0, mul_c1] <;> push_toZMod
  · exact hout.1
  · exact hout.2

/-- A root returned by the square root in `Fp2` squares to its input. -/
theorem sqrt_mul_self {a c : Fp2} (h : Fp2.sqrt a = some c) : c * c = a := by
  rcases Cryptography.Fp2.sqrt_eq_some_cases h with ⟨hz, hcases⟩ | ⟨hz, s, hs, hcases⟩ <;>
    simp only [Fp.baseField_sqrtCandidate] at hcases
  · have ha1 : a.c1 = 0 := Fp.isZero_iff.mp hz
    rcases hcases with ⟨hr, rfl⟩ | ⟨hr, rfl⟩
    · have hs := Fp.beq_iff.mp hr
      apply ext <;> apply Fp.toZMod.injective <;> simp only [mul_c0, mul_c1] <;>
        push_toZMod <;> simp_all [← Fp.toZMod_mul]
    · have hs : Fp.sqrtCandidate a.c0 * Fp.sqrtCandidate a.c0 = -a.c0 := by
        rcases Fp.sqrtCandidate_sq_or_neg a.c0 with hpos | hneg
        · rw [Fp.baseField_beq, Fp.beq_iff.mpr hpos] at hr
          cases hr
        · exact hneg
      apply ext <;> apply Fp.toZMod.injective <;> simp only [mul_c0, mul_c1] <;>
        push_toZMod <;> simp_all [← Fp.toZMod_mul]
  · have ha1 : a.c1 ≠ 0 := fun h0 => by
      rw [Fp.baseField_isZero, Fp.isZero_iff.mpr h0] at hz
      cases hz
    have hn := Fp.baseField_sqrt_mul_self hs
    rcases hcases with ⟨hr, rfl⟩ | ⟨hr, rfl⟩
    · exact sqrt_branch_gen_aux (fun _ hx => fp_mul_inverse hx) ha1 hn two_mul_inverse
        (Fp.beq_iff.mp hr)
    · have hr' :
          Fp.sqrtCandidate ((a.c0 + s) * BaseField.inverse (BaseField.ofNat 2 : Fp)) *
            Fp.sqrtCandidate ((a.c0 + s) * BaseField.inverse (BaseField.ofNat 2 : Fp)) =
            -((a.c0 + s) * BaseField.inverse (BaseField.ofNat 2 : Fp)) := by
        rcases Fp.sqrtCandidate_sq_or_neg _ with hpos | hneg
        · rw [Fp.baseField_beq, Fp.beq_iff.mpr hpos] at hr
          cases hr
        · exact hneg
      exact sqrt_branch_neg_aux ha1 hn two_mul_inverse hr'

/-- The square root in `Fp2` succeeds on every square. -/
theorem sqrt_complete {a b : Fp2} (hb : b * b = a) :
    ∃ c, Fp2.sqrt a = some c := by
  apply Cryptography.Fp2.sqrt_isSome_of_norm
  have hn : (b.c0 * b.c0 + b.c1 * b.c1) * (b.c0 * b.c0 + b.c1 * b.c1) =
      a.c0 * a.c0 + a.c1 * a.c1 := by
    rw [← hb]
    apply Fp.toZMod.injective
    simp only [mul_c0, mul_c1]
    push_toZMod
    ring
  exact ⟨_, Fp.baseField_sqrt_complete hn⟩

/-- The square root in `Fp2` fails exactly on the elements that are not squares. -/
theorem sqrt_eq_none_iff {a : Fp2} : Fp2.sqrt a = none ↔ ∀ b : Fp2, b * b ≠ a := by
  constructor
  · -- A square has a root, so the square root does not fail on it.
    intro h b hb
    obtain ⟨c, hc⟩ := sqrt_complete hb
    rw [h] at hc
    cases hc
  · -- A returned root squares to the input, so the input is a square.
    intro h
    cases hc : Fp2.sqrt a with
    | none => rfl
    | some c => exact absurd (sqrt_mul_self hc) (h c)

/-! ## Equations decided in the model

This section decides equations of closed terms in the model of `Fp`.

There the kernel computes on natural numbers. -/

/-- Two elements are equal when their images in the model are. -/
theorem eq_of_model {a b : Fp2} (h : (a.map Fp.toModel).beq (b.map Fp.toModel) = true) :
    a = b :=
  beq_iff_eq.mp (by rwa [map_beq] at h)

/-- Two elements differ when their images in the model do. -/
theorem ne_of_model {a b : Fp2} (h : (a.map Fp.toModel).beq (b.map Fp.toModel) = false) :
    a ≠ b := by
  rintro rfl
  rw [map_beq, (beq_iff_eq (a := a)).mpr rfl] at h
  exact Bool.noConfusion h

/-- The image of the norm is the norm computed on the image. -/
theorem toModel_norm (a : Fp2) :
    Fp.toModel (norm a) =
      (a.map Fp.toModel).c0 * (a.map Fp.toModel).c0 +
        (a.map Fp.toModel).c1 * (a.map Fp.toModel).c1 := by
  rw [norm, Fp.toModel_add, Fp.toModel_mul, Fp.toModel_mul]
  rfl

/-- One is not zero, so its zero test fails. -/
theorem one_isZero : (one : Fp2).isZero = false :=
  Bool.eq_false_iff.mpr fun h => one_ne_zero (isZero_iff.mp h)

/-- A natural number is the element with that real part and a zero imaginary part. -/
theorem natCast_eq (n : Nat) : (n : Fp2) = ⟨Fp.ofNat n, Fp.zero⟩ := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, Fp.zero_def]
    apply ext
    · show (0 : Fp2).c0 = Fp.ofNat 0
      exact Fp.ext (by rw [zero_c0, Fp.val_zero, Fp.val_ofNat, Nat.zero_mod])
    · exact zero_c1
  | succ n ih =>
    rw [Nat.cast_succ, ih]
    apply ext
    · apply Fp.ext
      show (Fp.ofNat n + 1).val = _
      rw [Fp.val_add, Fp.val_ofNat, Fp.val_ofNat, Fp.val_one, Nat.mod_add_mod]
    · show (0 : Fp) + 0 = 0
      exact Fp.toZMod.injective (by rw [Fp.toZMod_add, Fp.toZMod_zero, add_zero])

/-- A numeral is the element with that real part and a zero imaginary part. -/
theorem numeral_eq (n : Nat) [n.AtLeastTwo] : (OfNat.ofNat n : Fp2) = ⟨Fp.ofNat n, Fp.zero⟩ :=
  natCast_eq n

/-- The division of the field multiplies by the library's inverse. -/
theorem div_eq_mul_inverse (a b : Fp2) : a / b = a * b.inverse := rfl

/-- The inverse of the field is the library's inverse. -/
theorem inv_eq_inverse (a : Fp2) : a⁻¹ = a.inverse := rfl

end EthLib.Cryptography.Bls.Fp2

namespace EthLib.Cryptography.Bls

/-- Decides an equation or a disequation of closed terms in `Fp` or `Fp2`, in the model.

The listed definitions are unfolded first.

The field operations are rewritten to the library's, and the map is pushed down to the integers.

So the kernel computes in the model, on natural numbers. -/
macro "decide_eq_at_model" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (first
              | apply Fp.ne_of_model
              | apply Fp.eq_of_model
              | apply Fp2.ne_of_model
              | apply Fp2.eq_of_model
             simp only [← Fp2.powNat_eq_pow, Fp2.numeral_eq, Fp2.div_eq_mul_inverse,
               Fp2.inv_eq_inverse, ← Fp2.one_eq_one, ← Fp2.zero_eq_zero, Fp2.map_add, Fp2.map_sub,
               Fp2.map_neg, Fp2.map_mul, Fp2.map_mk, Fp2.map_one, Fp2.map_zero, Fp2.map_i,
               Fp2.map_ofFp, Fp2.map_conjugate, Fp2.map_inverse, Fp2.map_powNat,
               Fp2.map_mulByOnePlusI, Fp.toModel_ofNat, Fp.toModel_zero, Fp.toModel_one,
               Fp.toModel_zero', Fp.toModel_one', Fp.toModel_numeral, Fp.toModel_add,
               Fp.toModel_sub, Fp.toModel_mul, Fp.toModel_neg, Fp.toModel_inverse,
               Fp.toModel_powNat, Fp2.toModel_norm, Fp.baseField_ofNat, Fp.baseField_zero,
               Fp.baseField_one, Fp.baseField_inverse, Fp.baseField_powNat, $ids,*]
             decide +kernel))

end EthLib.Cryptography.Bls
