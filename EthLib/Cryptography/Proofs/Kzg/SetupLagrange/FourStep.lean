module

public import EthLib.Cryptography.Proofs.Kzg.FftG1

/-!
# Proofs: a transform of size 4096 as three rounds of transforms of size 16

Take points `P_j` of order dividing `r`, for `j < 4096`, a scalar `c`, and `ζ` with `ζ^4096 = 1`.

The transform of the points has entry `T_k = sum_{j < 4096} (c ζ^(j k)) P_j`.

Write `j = 256 j1 + 16 j2 + j3` and `k = k1 + 16 k2 + 256 k3`, each digit below 16.

Mod 4096, `j k` is `256 j1 k1 + 16 j2 k1 + 256 j2 k2 + j3 k1 + 16 j3 k2 + 256 j3 k3`.

So `T_k` is computed in three rounds of transforms of size 16, each with the root `u = ζ^256`.

1. `A(k1, j2, j3) = sum_{j1} u^(j1 k1) P_(256 j1 + 16 j2 + j3)`.
2. `B(k1, k2, j3) = sum_{j2} u^(j2 k2) (c ζ^(16 j2 k1)) A(k1, j2, j3)`.
3. `T_k = sum_{j3} u^(j3 k3) ζ^(j3 (k1 + 16 k2)) B(k1, k2, j3)`.

The scalars act on points through their value below `r`.

The statement holds for every `ζ` with `ζ^4096 = 1`, primitive or not.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls (Fr G1)
open scoped EthLib.Cryptography.Bls.Fr
open Finset

/-- A sum over `j < a b` is a sum over `i < a` of sums over `t < b`, at `j = b i + t`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (f : Nat → M) (a b : Nat) :
    ∑ j ∈ range (a * b), f j = ∑ i ∈ range a, ∑ t ∈ range b, f (b * i + t) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, Nat.mul_comm a b]

/-- The scalar of each term after the three rounds is `c ζ^(j k)`. -/
private theorem scalar_eq {ζ : Fr} (hζ : ζ ^ 4096 = 1) (c : Fr) (j1 j2 j3 k1 k2 k3 : Nat) :
    (ζ ^ 256) ^ (j3 * k3) * (ζ ^ (j3 * (k1 + 16 * k2)) *
      ((ζ ^ 256) ^ (j2 * k2) * (c * ζ ^ (16 * j2 * k1) * (ζ ^ 256) ^ (j1 * k1)))) =
      c * ζ ^ ((256 * j1 + 16 * j2 + j3) * (k1 + 16 * k2 + 256 * k3)) := by
  have he : (256 * j1 + 16 * j2 + j3) * (k1 + 16 * k2 + 256 * k3) =
      (256 * (j3 * k3) + j3 * (k1 + 16 * k2) + 256 * (j2 * k2) + 16 * j2 * k1 + 256 * (j1 * k1)) +
        4096 * (j1 * k2 + 16 * j1 * k3 + j2 * k3) := by ring
  rw [he, pow_add, pow_mul ζ 4096, hζ, one_pow, mul_one]
  simp only [← pow_mul, pow_add]
  ring

/-- A sum over `j < 4096` as three sums over the digits of `j = 256 j1 + 16 j2 + j3`. -/
private theorem sum_range_digits {M : Type*} [AddCommMonoid M] (f : Nat → M) :
    ∑ j ∈ range 4096, f j =
      ∑ j3 ∈ range 16, ∑ j2 ∈ range 16, ∑ j1 ∈ range 16, f (256 * j1 + 16 * j2 + j3) := by
  calc ∑ j ∈ range 4096, f j
      = ∑ j1 ∈ range 16, ∑ t ∈ range 256, f (256 * j1 + t) := sum_range_mul f 16 256
    _ = ∑ j1 ∈ range 16, ∑ j2 ∈ range 16, ∑ j3 ∈ range 16, f (256 * j1 + 16 * j2 + j3) :=
        sum_congr rfl fun j1 _ => by
          rw [show 256 = 16 * 16 from rfl, sum_range_mul]
          simp only [Nat.add_assoc]
    _ = ∑ j2 ∈ range 16, ∑ j1 ∈ range 16, ∑ j3 ∈ range 16, f (256 * j1 + 16 * j2 + j3) :=
        sum_comm
    _ = ∑ j2 ∈ range 16, ∑ j3 ∈ range 16, ∑ j1 ∈ range 16, f (256 * j1 + 16 * j2 + j3) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_comm

/-- Entry `k1 + 16 k2 + 256 k3` of a transform of size 4096, as three rounds of size 16. -/
theorem sum_eq_threeRounds {P : Nat → G1.curve.toAffine.Point}
    (htor : ∀ j, Fr.modulus • P j = 0) {ζ : Fr} (hζ : ζ ^ 4096 = 1) (c : Fr)
    (k1 k2 k3 : Nat) :
    ∑ j ∈ range 4096, (c * ζ ^ (j * (k1 + 16 * k2 + 256 * k3))).val • P j =
      ∑ j3 ∈ range 16, ((ζ ^ 256) ^ (j3 * k3)).val • (ζ ^ (j3 * (k1 + 16 * k2))).val •
        ∑ j2 ∈ range 16, ((ζ ^ 256) ^ (j2 * k2)).val • (c * ζ ^ (16 * j2 * k1)).val •
          ∑ j1 ∈ range 16, ((ζ ^ 256) ^ (j1 * k1)).val • P (256 * j1 + 16 * j2 + j3) := by
  -- Push the scalars into the sums, then merge them into one scalar per point.
  simp only [smul_sum, ← nsmul_val_mul_of_torsion (htor _), scalar_eq hζ]
  exact sum_range_digits _

end EthLib.Cryptography.Kzg.SetupLagrange
