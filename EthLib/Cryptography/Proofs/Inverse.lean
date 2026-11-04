module

public import EthLib.Cryptography.Inverse
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Proofs: the Euclidean inverse is the field inverse

Each coefficient times `a` equals its remainder mod `m`, at every step.

So at the end, the result times `a` is the gcd of `a` and `m`.

For a prime `m` and `a != 0` the gcd is `1`, so the result is the inverse in `ZMod m`.

For `a = 0` the result is `0`, as for the inverse of `ZMod m`.
-/

@[expose] public section

namespace EthLib.Cryptography

/-- If each coefficient times `a` equals its remainder mod `m`, the result times `a` is the gcd. -/
theorem euclid_mul {m : Nat} (a : ZMod m) (r r' : Nat) (s s' : Int)
    (h : (r : ZMod m) = s * a) (h' : (r' : ZMod m) = s' * a) :
    ((Nat.gcd r r' : Nat) : ZMod m) = (euclid r r' s s' : ZMod m) * a := by
  fun_induction euclid r r' s s' with
  | case1 r s => simpa using h
  | case2 r r' s s' h0 ih =>
    rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
    refine ih h' ?_
    -- `r = r' * (r / r') + r mod r'`, so the new remainder is `r - (r / r') * r'`.
    have hdiv := congrArg (fun n : Nat => (n : ZMod m)) (Nat.div_add_mod r r')
    simp only [Nat.cast_add, Nat.cast_mul] at hdiv
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    linear_combination hdiv + h - ((r / r' : Nat) : ZMod m) * h'

/-- The inverse of `0` is `0`. -/
theorem Fin.inverse_zero {m : Nat} [NeZero m] : Fin.inverse (0 : Fin m) = 0 := by
  have hm : m ≠ 0 := NeZero.ne m
  -- One step turns `(0, m)` into `(m, 0)`, with the coefficients `(0, 1)`.
  simp [Fin.inverse, euclid, hm]

/-- The inverse of `1` is `1`. -/
theorem Fin.inverse_one {m : Nat} [NeZero m] : Fin.inverse (1 : Fin m) = 1 := by
  rcases Nat.lt_or_ge 1 m with hm | hm
  · -- Two steps turn `(1, m)` into `(m, 1)`, then `(1, 0)`, with the coefficient `1`.
    have e : euclid 1 m 1 0 = 1 := by
      rw [euclid, ite_eq_right (by omega), Nat.mod_eq_of_lt hm, euclid,
        ite_eq_right one_ne_zero, Nat.mod_one, euclid, ite_eq_left rfl]
      simp
    apply Fin.ext
    rw [Fin.inverse, Fin.val_one', Nat.mod_eq_of_lt hm, e, Fin.val_ofNat,
      Int.emod_eq_of_lt (by decide) (by exact_mod_cast hm)]
    exact Nat.mod_eq_of_lt hm
  · -- `Fin 1` has one element.
    have : m = 1 := by have := NeZero.ne m; omega
    subst this
    exact Subsingleton.elim _ _

/-- For a prime `m`, the Euclidean inverse is the inverse of `ZMod m`. -/
theorem Fin.inverse_val {m : Nat} [NeZero m] [Fact m.Prime] (a : Fin m) :
    ((Fin.inverse a).val : ZMod m) = (a.val : ZMod m)⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    simp [Fin.inverse_zero]
  have hm : 0 < (m : Int) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  -- `a` is below the prime `m` and not zero, so it is coprime to `m`.
  have hcop : Nat.gcd a.val m = 1 := by
    rw [Nat.gcd_comm]
    refine (Nat.coprime_comm.mp ?_).symm
    refine (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hd => ha (Fin.ext ?_)
    exact Nat.eq_zero_of_dvd_of_lt hd a.isLt
  have hmul := euclid_mul (a.val : ZMod m) a.val m 1 0 (by simp) (by simp)
  rw [hcop] at hmul
  set s := euclid a.val m 1 0
  -- The result is `s mod m`, which casts to `s` in `ZMod m`.
  have hres : ((Fin.inverse a).val : ZMod m) = (s : ZMod m) := by
    have hnn : 0 ≤ s % m := Int.emod_nonneg _ hm.ne'
    rw [Fin.inverse, Fin.val_ofNat, ZMod.natCast_mod, ← Int.cast_natCast,
      Int.toNat_of_nonneg hnn, ZMod.intCast_mod]
  rw [hres]
  exact (eq_inv_of_mul_eq_one_left (by simpa using hmul.symm))

/-- The same fact through any map that agrees with the cast of the value. -/
theorem Fin.inverse_map {m : Nat} [NeZero m] [Fact m.Prime] (f : Fin m → ZMod m)
    (hf : ∀ x, f x = (x.val : ZMod m)) (a : Fin m) : f (Fin.inverse a) = (f a)⁻¹ := by
  rw [hf, hf, Fin.inverse_val]

end EthLib.Cryptography
