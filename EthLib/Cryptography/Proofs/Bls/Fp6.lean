module

public import EthLib.Cryptography.Bls.Fp6
public import EthLib.Cryptography.Proofs.Bls.Fp2

/-!
# Proofs: `Fp6`

`Fp6` is the cubic extension `Fp2[v] / (v^3 - xi)`, with `xi = 1 + i`.

This file proves that it is a field, with the library's own operations.

Every element has a norm in `Fp2`, and the norm is zero only at zero.

That rests on one fact: `xi` is not a cube in `Fp2`.

The norm of `xi` down to `Fp` is `2`, and `2` is not a cube in `Fp`.

The kernel checks the last step by computing `2^((p-1)/3) mod p`, which is not `1`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Fp6

/-! ## Extensionality and coordinate projections -/

@[ext]
theorem ext {a b : Fp6} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) : a = b := by
  cases a; cases b; simp_all

instance : Zero Fp6 := ⟨zero⟩
instance : One Fp6 := ⟨one⟩

@[simp] theorem zero_eq_zero : zero = (0 : Fp6) := rfl
@[simp] theorem one_eq_one : one = (1 : Fp6) := rfl

@[simp] theorem zero_c0 : (0 : Fp6).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp6).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Fp6).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp6).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp6).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Fp6).c2 = 0 := rfl
@[simp] theorem v_c0 : v.c0 = 0 := rfl
@[simp] theorem v_c1 : v.c1 = 1 := rfl
@[simp] theorem v_c2 : v.c2 = 0 := rfl
@[simp] theorem ofFp2_c0 (x : Fp2) : (ofFp2 x).c0 = x := rfl
@[simp] theorem ofFp2_c1 (x : Fp2) : (ofFp2 x).c1 = 0 := rfl
@[simp] theorem ofFp2_c2 (x : Fp2) : (ofFp2 x).c2 = 0 := rfl

@[simp] theorem add_c0 (a b : Fp6) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp6) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Fp6) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem sub_c0 (a b : Fp6) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp6) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Fp6) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem neg_c0 (a : Fp6) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp6) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Fp6) : (-a).c2 = -a.c2 := rfl

@[simp] theorem mul_c0 (a b : Fp6) :
    (a * b).c0 = ((a.c1 + a.c2) * (b.c1 + b.c2) - a.c1 * b.c1 - a.c2 * b.c2).mulByOnePlusI + a.c0 * b.c0 := rfl
@[simp] theorem mul_c1 (a b : Fp6) :
    (a * b).c1 = (a.c0 + a.c1) * (b.c0 + b.c1) - a.c0 * b.c0 - a.c1 * b.c1 + (a.c2 * b.c2).mulByOnePlusI := rfl
@[simp] theorem mul_c2 (a b : Fp6) :
    (a * b).c2 = (a.c0 + a.c2) * (b.c0 + b.c2) - a.c0 * b.c0 - a.c2 * b.c2 + a.c1 * b.c1 := rfl

/-! ## Boolean equality and zero check -/

theorem beq_iff_eq {a b : Fp6} : a.beq b = true ↔ a = b := by
  rw [beq, Bool.and_eq_true, Bool.and_eq_true, Fp2.beq_iff_eq, Fp2.beq_iff_eq, Fp2.beq_iff_eq]
  exact ⟨fun ⟨⟨h0, h1⟩, h2⟩ => ext h0 h1 h2,
    fun h => ⟨⟨congrArg c0 h, congrArg c1 h⟩, congrArg c2 h⟩⟩

theorem isZero_iff {a : Fp6} : a.isZero = true ↔ a = 0 := by
  rw [isZero, Bool.and_eq_true, Bool.and_eq_true, Fp2.isZero_iff, Fp2.isZero_iff, Fp2.isZero_iff]
  exact ⟨fun ⟨⟨h0, h1⟩, h2⟩ => ext h0 h1 h2,
    fun h => ⟨⟨congrArg c0 h, congrArg c1 h⟩, congrArg c2 h⟩⟩

instance : LawfulBEq Fp6 where
  eq_of_beq {a b} h := by
    cases a; cases b
    change (_ && (_ && _)) = true at h
    rw [Bool.and_eq_true, Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq, _root_.beq_iff_eq] at h
    exact ext h.1 h.2.1 h.2.2
  rfl {a} := by
    cases a
    change (_ && (_ && _)) = true
    simp

instance : DecidableEq Fp6 := fun a b =>
  if h : a.beq b then isTrue (beq_iff_eq.mp h)
  else isFalse (fun heq => h (beq_iff_eq.mpr heq))

/-! ## Ring axioms, `AddCommGroup Fp6`, and `CommRing Fp6` -/

protected theorem add_comm (a b : Fp6) : a + b = b + a := by
  apply ext <;> simp <;> ring

protected theorem add_assoc (a b c : Fp6) : a + b + c = a + (b + c) := by
  apply ext <;> simp <;> ring

protected theorem zero_add (a : Fp6) : 0 + a = a := by
  apply ext <;> simp

protected theorem add_zero (a : Fp6) : a + 0 = a := by
  apply ext <;> simp

protected theorem neg_add_cancel (a : Fp6) : -a + a = 0 := by
  apply ext <;> simp

protected theorem sub_eq_add_neg (a b : Fp6) : a - b = a + -b := by
  apply ext <;> simp [_root_.sub_eq_add_neg]

protected theorem mul_comm (a b : Fp6) : a * b = b * a := by
  apply ext <;> simp <;> ring

protected theorem mul_assoc (a b c : Fp6) : a * b * c = a * (b * c) := by
  apply ext <;> simp <;> ring

protected theorem one_mul (a : Fp6) : 1 * a = a := by
  apply ext <;> simp

protected theorem mul_one (a : Fp6) : a * 1 = a := by
  apply ext <;> simp

protected theorem zero_mul (a : Fp6) : 0 * a = 0 := by
  apply ext <;> simp

protected theorem mul_zero (a : Fp6) : a * 0 = 0 := by
  apply ext <;> simp

protected theorem left_distrib (a b c : Fp6) : a * (b + c) = a * b + a * c := by
  apply ext <;> simp <;> ring

protected theorem right_distrib (a b c : Fp6) : (a + b) * c = a * c + b * c := by
  apply ext <;> simp <;> ring

instance : AddCommGroup Fp6 where
  add_assoc := Fp6.add_assoc
  zero_add := Fp6.zero_add
  add_zero := Fp6.add_zero
  neg_add_cancel := Fp6.neg_add_cancel
  add_comm := Fp6.add_comm
  sub_eq_add_neg := Fp6.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : CommRing Fp6 where
  left_distrib := Fp6.left_distrib
  right_distrib := Fp6.right_distrib
  zero_mul := Fp6.zero_mul
  mul_zero := Fp6.mul_zero
  mul_assoc := Fp6.mul_assoc
  one_mul := Fp6.one_mul
  mul_one := Fp6.mul_one
  mul_comm := Fp6.mul_comm

/-! ## Multiplication by `v` -/

@[simp]
theorem mulByV_eq (a : Fp6) : a.mulByV = a * v := by
  apply ext <;> simp [mulByV]

/-! ## Norm over `Fp2` and `Fp6.inverse` soundness -/

/-- The norm of `a` down to `Fp2`.

It is the denominator of the library's inverse.
-/
def norm (a : Fp6) : Fp2 :=
  let xi := Fp2.mulByOnePlusI
  let t0 := a.c0 * a.c0 - xi (a.c1 * a.c2)
  let t1 := xi (a.c2 * a.c2) - a.c0 * a.c1
  let t2 := a.c1 * a.c1 - a.c0 * a.c2
  a.c0 * t0 + xi (a.c2 * t1) + xi (a.c1 * t2)

private theorem norm_mul_aux (a0 a1 a2 b0 b1 b2 xi : Fp2) :
    let c0 := ((a1 + a2) * (b1 + b2) - a1 * b1 - a2 * b2) * xi + a0 * b0
    let c1 := (a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1 + a2 * b2 * xi
    let c2 := (a0 + a2) * (b0 + b2) - a0 * b0 - a2 * b2 + a1 * b1
    (c0 * (c0 * c0 - c1 * c2 * xi) + c2 * (c2 * c2 * xi - c0 * c1) * xi + c1 * (c1 * c1 - c0 * c2) * xi) =
      (a0 * (a0 * a0 - a1 * a2 * xi) + a2 * (a2 * a2 * xi - a0 * a1) * xi + a1 * (a1 * a1 - a0 * a2) * xi) *
      (b0 * (b0 * b0 - b1 * b2 * xi) + b2 * (b2 * b2 * xi - b0 * b1) * xi + b1 * (b1 * b1 - b0 * b2) * xi) := by
  ring

theorem norm_mul (a b : Fp6) : norm (a * b) = norm a * norm b := by
  simp only [norm, mul_c0, mul_c1, mul_c2, Fp2.mulByOnePlusI_eq]
  exact norm_mul_aux a.c0 a.c1 a.c2 b.c0 b.c1 b.c2 Fp2.xi

@[simp] theorem norm_zero : norm 0 = 0 := by simp [norm]
@[simp] theorem norm_one : norm 1 = 1 := by simp [norm]

@[simp]
theorem norm_v : norm v = Fp2.xi := by
  decide

theorem norm_mulByV (a : Fp6) : norm a.mulByV = (norm a).mulByOnePlusI := by
  rw [mulByV_eq, norm_mul, norm_v, Fp2.mulByOnePlusI_eq]

/-! ## `xi` is not a cube, so the norm is zero only at zero -/

open scoped Fin.CommRing in
theorem norm_mulByOnePlusI (a : Fp2) : Fp2.norm a.mulByOnePlusI = 2 * Fp2.norm a := by
  simp only [Fp2.norm, Fp2.mulByOnePlusI]
  ring

@[simp]
theorem norm_xi : Fp2.norm Fp2.xi = Fp.ofNat 2 := by
  decide

open scoped EthLib.Cryptography.Bls.Fp in
set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
private theorem cube_ne_two_zmod (z : ZMod Fp.modulus) : z * z * z ≠ 2 := by
  -- If `z^3 = 2`, then `2^((p-1)/3) = z^(p-1) = 1`, which the kernel refutes.
  intro h
  have h3 : z ^ 3 = ((2 : Nat) : ZMod Fp.modulus) := by
    have h2 : (2 : ZMod Fp.modulus) = ((2 : Nat) : ZMod Fp.modulus) := rfl
    rw [← h2]
    linear_combination h
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at h
    revert h; decide
  have hfermat : z ^ (Fp.modulus - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hz
  rw [show Fp.modulus - 1 = 3 * ((Fp.modulus - 1) / 3) by decide,
    pow_mul, h3] at hfermat
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 2 3
    (by decide) (by decide) hfermat

open scoped EthLib.Cryptography.Bls.Fp in
private theorem cube_eq_two_mul_cube_zmod {u w nxi : ZMod Fp.modulus}
    (hnxi : nxi = 2) (h : u * u * u = w * w * w * nxi) : w = 0 := by
  by_contra hw
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  rw [hnxi] at h
  have hcube : (u * w⁻¹) * (u * w⁻¹) * (u * w⁻¹) = 2 := by
    linear_combination (w⁻¹ * w⁻¹ * w⁻¹) * h +
      2 * ((w * w⁻¹) * (w * w⁻¹) + w * w⁻¹ + 1) * hinv
  exact cube_ne_two_zmod (u * w⁻¹) hcube

private theorem cube_eq_xi_mul_cube {x y : Fp2}
    (h : x * x * x = y * y * y * Fp2.xi) : y = 0 := by
  -- Taking norms gives `N(x)^3 = N(y)^3 * 2` in `Fp`, so `N(y) = 0`.
  have hnorm : Fp2.norm (x * x * x) = Fp2.norm (y * y * y * Fp2.xi) :=
    congrArg Fp2.norm h
  simp only [Fp2.norm_mul] at hnorm
  have hy0 : Fp2.norm y = 0 :=
    cube_eq_two_mul_cube_zmod (u := Fp2.norm x) (w := Fp2.norm y)
      (nxi := Fp2.norm Fp2.xi) rfl hnorm
  exact (Fp2.norm_eq_zero_iff y).mp hy0

private theorem norm_eq_zero_aux {a0 a1 a2 : Fp2}
    (h : a0 * (a0 * a0 - a1 * a2 * Fp2.xi) +
      a2 * (a2 * a2 * Fp2.xi - a0 * a1) * Fp2.xi +
      a1 * (a1 * a1 - a0 * a2) * Fp2.xi = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 := by
  -- The `t_i` are the cofactors the library's inverse multiplies by.
  -- A zero norm forces `t0^3 = t1^3 * xi`, so `t1 = 0`, and then `t0 = t2 = 0`.
  -- The same cube argument on the `a_i` then forces each of them to zero.
  set xi := Fp2.xi
  set t0 := a0 * a0 - a1 * a2 * xi
  set t1 := a2 * a2 * xi - a0 * a1
  set t2 := a1 * a1 - a0 * a2
  have ht01 : t0 * t0 * t0 = t1 * t1 * t1 * xi := by
    linear_combination (a0 * t0 - a2 * t1 * xi) * h
  have ht1 : t1 = 0 := cube_eq_xi_mul_cube ht01
  have ht0_sq : t0 * t0 = 0 := by
    linear_combination a0 * h + t2 * xi * ht1
  have ht0 : t0 = 0 := mul_self_eq_zero.mp ht0_sq
  have ht2_xi : t2 * t2 * xi = 0 := by
    linear_combination a1 * h + t0 * ht1
  have hxi_ne : xi ≠ 0 := by decide
  have ht2_sq : t2 * t2 = 0 := (mul_eq_zero.mp ht2_xi).resolve_right hxi_ne
  have ht2 : t2 = 0 := mul_self_eq_zero.mp ht2_sq
  have ha01 : a0 * a0 * a0 = a1 * a1 * a1 * xi := by
    linear_combination a0 * ht0 - a1 * xi * ht2
  have ha1 : a1 = 0 := cube_eq_xi_mul_cube ha01
  have ha0_sq : a0 * a0 = 0 := by
    linear_combination ht0 + a2 * xi * ha1
  have ha0 : a0 = 0 := mul_self_eq_zero.mp ha0_sq
  have ha2_xi : a2 * a2 * xi = 0 := by
    linear_combination ht1 + a0 * ha1
  have ha2_sq : a2 * a2 = 0 := (mul_eq_zero.mp ha2_xi).resolve_right hxi_ne
  have ha2 : a2 = 0 := mul_self_eq_zero.mp ha2_sq
  exact ⟨ha0, ha1, ha2⟩

/-- The norm is zero only at zero. -/
theorem norm_eq_zero_iff (a : Fp6) : norm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    simp only [norm, Fp2.mulByOnePlusI_eq] at h
    obtain ⟨h0, h1, h2⟩ := norm_eq_zero_aux h
    exact ext h0 h1 h2
  · rintro rfl
    exact norm_zero

theorem norm_ne_zero_iff (a : Fp6) : norm a ≠ 0 ↔ a ≠ 0 :=
  not_congr (norm_eq_zero_iff a)

private theorem mul_inverse_c0_aux (a0 a1 a2 xi invDet : Fp2)
    (hdet : (a0 * (a0 * a0 - a1 * a2 * xi) + a2 * (a2 * a2 * xi - a0 * a1) * xi +
      a1 * (a1 * a1 - a0 * a2) * xi) * invDet = 1) :
    let t0 := a0 * a0 - a1 * a2 * xi
    let t1 := a2 * a2 * xi - a0 * a1
    let t2 := a1 * a1 - a0 * a2
    ((a1 + a2) * (t1 * invDet + t2 * invDet) - a1 * (t1 * invDet) - a2 * (t2 * invDet)) * xi +
      a0 * (t0 * invDet) = 1 := by
  linear_combination hdet

private theorem mul_inverse_c1_aux (a0 a1 a2 xi invDet : Fp2) :
    let t0 := a0 * a0 - a1 * a2 * xi
    let t1 := a2 * a2 * xi - a0 * a1
    let t2 := a1 * a1 - a0 * a2
    (a0 + a1) * (t0 * invDet + t1 * invDet) - a0 * (t0 * invDet) - a1 * (t1 * invDet) +
      a2 * (t2 * invDet) * xi = 0 := by
  ring

private theorem mul_inverse_c2_aux (a0 a1 a2 xi invDet : Fp2) :
    let t0 := a0 * a0 - a1 * a2 * xi
    let t1 := a2 * a2 * xi - a0 * a1
    let t2 := a1 * a1 - a0 * a2
    (a0 + a2) * (t0 * invDet + t2 * invDet) - a0 * (t0 * invDet) - a2 * (t2 * invDet) +
      a1 * (t1 * invDet) = 0 := by
  ring

private theorem inverse_eq (a : Fp6) :
    a.inverse =
      let xi := Fp2.mulByOnePlusI
      let t0 := a.c0 * a.c0 - xi (a.c1 * a.c2)
      let t1 := xi (a.c2 * a.c2) - a.c0 * a.c1
      let t2 := a.c1 * a.c1 - a.c0 * a.c2
      ⟨t0 * (norm a).inverse, t1 * (norm a).inverse, t2 * (norm a).inverse⟩ := rfl

private theorem mul_inverse_aux (a : Fp6) (invDet : Fp2) (h : norm a * invDet = 1) :
    let xi := Fp2.mulByOnePlusI
    let t0 := a.c0 * a.c0 - xi (a.c1 * a.c2)
    let t1 := xi (a.c2 * a.c2) - a.c0 * a.c1
    let t2 := a.c1 * a.c1 - a.c0 * a.c2
    a * ⟨t0 * invDet, t1 * invDet, t2 * invDet⟩ = 1 := by
  have hdet :
      (a.c0 * (a.c0 * a.c0 - a.c1 * a.c2 * Fp2.xi)
        + a.c2 * (a.c2 * a.c2 * Fp2.xi - a.c0 * a.c1) * Fp2.xi
        + a.c1 * (a.c1 * a.c1 - a.c0 * a.c2) * Fp2.xi) * invDet = 1 := by
    simpa only [norm, Fp2.mulByOnePlusI_eq] using h
  refine ext ?_ ?_ ?_
  · simp only [mul_c0, Fp2.mulByOnePlusI_eq, one_c0]
    exact mul_inverse_c0_aux a.c0 a.c1 a.c2 Fp2.xi invDet hdet
  · simp only [mul_c1, Fp2.mulByOnePlusI_eq, one_c1]
    exact mul_inverse_c1_aux a.c0 a.c1 a.c2 Fp2.xi invDet
  · simp only [mul_c2, Fp2.mulByOnePlusI_eq, one_c2]
    exact mul_inverse_c2_aux a.c0 a.c1 a.c2 Fp2.xi invDet

theorem mul_inverse_of_norm_invertible {a : Fp6} (h : norm a * (norm a).inverse = 1) :
    a * a.inverse = 1 := by
  rw [inverse_eq]
  exact mul_inverse_aux a (norm a).inverse h

theorem mul_inverse_of_norm_ne_zero {a : Fp6} (h : norm a ≠ 0) :
    a * a.inverse = 1 :=
  mul_inverse_of_norm_invertible (Fp2.mul_inverse_cancel h)

theorem inverse_mul_of_norm_ne_zero {a : Fp6} (h : norm a ≠ 0) :
    a.inverse * a = 1 := by
  rw [Fp6.mul_comm, mul_inverse_of_norm_ne_zero h]

theorem mul_inverse_cancel {a : Fp6} (h : a ≠ 0) : a * a.inverse = 1 :=
  mul_inverse_of_norm_ne_zero ((norm_ne_zero_iff a).mpr h)

theorem inverse_mul_cancel {a : Fp6} (h : a ≠ 0) : a.inverse * a = 1 := by
  rw [Fp6.mul_comm, mul_inverse_cancel h]

@[simp]
theorem inverse_zero : (0 : Fp6).inverse = 0 := by
  rw [inverse_eq, norm_zero, Fp2.inverse_zero]
  apply ext <;> simp

instance : Field Fp6 where
  inv := inverse
  exists_pair_ne := ⟨0, 1, fun h => by
    have := congrArg (fun x => x.c0.c0) h
    revert this; decide⟩
  mul_inv_cancel := fun _ h => mul_inverse_cancel h
  inv_zero := inverse_zero
  div_eq_mul_inv := fun _ _ => rfl
  nnqsmul := _
  qsmul := _

end EthLib.Cryptography.Bls.Fp6
