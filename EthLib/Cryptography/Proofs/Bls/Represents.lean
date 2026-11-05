module

public import EthLib.Cryptography.Proofs.Bls.PairingLaws
public import EthLib.Cryptography.Proofs.Bls.G1Msm

/-!
# Proofs: the scalars that sums and multiples represent

A valid point represents `a • g` when its group element is `a` times the generator.

The sum of representatives of `a • g` and `b • g` represents `(a + b) • g`.

A multiple `s • P` of a representative of `a • g` represents `(s * a) • g`.

So a multi-scalar multiplication of representatives represents the same combination of scalars.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open scoped EthLib.Cryptography.Bls.Fr

namespace G1

/-- The sum of representatives of `a • g1` and `b • g1` represents `(a + b) • g1`. -/
theorem Represents.add {P Q : G1} {a b : Fr} (hP : Represents P a) (hQ : Represents Q b) :
    Represents (add P Q) (a + b) := by
  refine ⟨valid_add hP.1 hQ.1, ?_⟩
  rw [toPoint_add hP.1 hQ.1, hP.2, hQ.2, toPoint_mul_generator, toPoint_mul_generator,
    toPoint_mul_generator, ofFr_add]

/-- A multiple `s • P` of a representative of `a • g1` represents `(s * a) • g1`. -/
theorem Represents.mul {P : G1} {a : Fr} (hP : Represents P a) (s : Fr) :
    Represents (mul P s) (s * a) := by
  refine ⟨valid_mul hP.1 s, ?_⟩
  rw [toPoint_mul hP.1 s, hP.2, toPoint_mul_generator, toPoint_mul_generator, ofFr_mul]

/-- A point represents at most one scalar, since the generator has order `r`. -/
theorem Represents.unique {P : G1} {a b : Fr} (ha : Represents P a) (hb : Represents P b) :
    a = b := by
  have h : ofFr a = ofFr b := by
    rw [← toPoint_mul_generator, ← toPoint_mul_generator, ← ha.2, ← hb.2]
  have hfin : IsOfFinAddOrder (toPoint generator) :=
    addOrderOf_pos_iff.mp (addOrderOf_toPoint_generator ▸ Fr.modulus_pos)
  rw [ofFr, ofFr, hfin.nsmul_inj_mod, addOrderOf_toPoint_generator, Nat.mod_eq_of_lt a.isLt,
    Nat.mod_eq_of_lt b.isLt] at h
  exact Fin.ext h

/-- The point of a sum of products is the sum of the multiples of the points. -/
theorem sum_nsmul_ofFr (n : Nat) (s a : Nat → Fr) :
    ∑ j ∈ Finset.range n, (s j).val • ofFr (a j) =
      ofFr (∑ j ∈ Finset.range n, s j * a j) := by
  induction n with
  | zero => simp [ofFr_zero]
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, ofFr_add, ofFr_mul]

/-- A multi-scalar multiplication of representatives represents the combination of the scalars.

Let point `j` represent `a_j • g1`, and let `s_j` be scalar `j`.

Then the sum of the `s_j` times the points represents `(sum_j s_j * a_j) • g1`. -/
theorem represents_msm {points : Array G1} {scalars : Array Fr} {a : Nat → Fr}
    (hsize : points.size = scalars.size)
    (h : ∀ j < points.size, Represents points[j]! (a j)) :
    Represents (msm points scalars) (∑ j ∈ Finset.range points.size, scalars[j]! * a j) := by
  have hmin : (if points.size ≤ scalars.size then points.size else scalars.size) =
      points.size := by
    simp [hsize]
  obtain ⟨hv, hpt⟩ := toPoint_msm points scalars (fun j hj => (h j (hmin ▸ hj)).1)
  refine ⟨hv, ?_⟩
  rw [hpt, hmin, toPoint_mul_generator, ← sum_nsmul_ofFr]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(h j (Finset.mem_range.mp hj)).2, toPoint_mul_generator]

end G1

namespace G2

/-- The sum of representatives of `a • g2` and `b • g2` represents `(a + b) • g2`. -/
theorem Represents.add {P Q : G2} {a b : Fr} (hP : Represents P a) (hQ : Represents Q b) :
    Represents (add P Q) (a + b) := by
  refine ⟨valid_add hP.1 hQ.1, ?_⟩
  rw [toPoint_add hP.1 hQ.1, hP.2, hQ.2, toPoint_mul_generator, toPoint_mul_generator,
    toPoint_mul_generator, ofFr_add]

/-- A multiple `s • Q` of a representative of `b • g2` represents `(s * b) • g2`. -/
theorem Represents.mul {Q : G2} {b : Fr} (hQ : Represents Q b) (s : Fr) :
    Represents (mul Q s) (s * b) := by
  refine ⟨valid_mul hQ.1 s, ?_⟩
  rw [toPoint_mul hQ.1 s, hQ.2, toPoint_mul_generator, toPoint_mul_generator, ofFr_mul]

end G2

end EthLib.Cryptography.Bls
