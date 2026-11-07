module

public import EthLib.Cryptography.Proofs.AltBn128.Nondegenerate
public import EthLib.Cryptography.Proofs.AltBn128.PairingLaws
public import EthLib.Cryptography.Proofs.ZModSum

/-!
# Proofs: the pairing law of alt_bn128 from bilinearity

The pairing law of the check follows from one equation on the multiples of the generators:

`e(a P1, b P2) = e(P1, P2)^(a b)` for all `a` and `b` in `Fr`.

The check multiplies the Miller loops of its pairs and applies the final exponentiation once.

The final exponentiation is multiplicative.

So the check tests whether the product of the pairings is 1.

By the equation, that product is `e(P1, P2)` to the power `sum_i a_i b_i`.

The pairing of the generators has order `q`, so the power is 1 exactly when `q` divides the sum.

This file takes the equation as a hypothesis.

The proof of the equation imports this file and lives in another one.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

/-- Bilinearity on the multiples of the generators: `e(a P1, b P2) = e(P1, P2)^(a b)`. -/
def PairingBilinear : Prop :=
  ∀ a b : ZMod Fr.modulus,
    pairing (Point.mulBits 256 a.val Point.generator) (Point2.mulBits 256 b.val Point2.generator) =
      pairing Point.generator Point2.generator ^ (a.val * b.val)

/-- The final exponentiation of 1 is 1. -/
theorem finalExponentiation_one : finalExponentiation 1 = 1 := by
  rw [finalExponentiation_eq_pow, one_pow]

/-- One step of the check: the Miller loop of a pair, or nothing for a point at infinity. -/
private def checkStep (f : Fp12) : Point × Point2 → Fp12
  | (.affine xp yp, q@(.affine _ _)) => f * millerLoop q xp yp
  | _ => f

/-- A step multiplies the final exponentiation by the pairing of the pair. -/
private theorem finalExponentiation_checkStep (f : Fp12) (pq : Point × Point2) :
    finalExponentiation (checkStep f pq) = finalExponentiation f * pairing pq.1 pq.2 := by
  obtain ⟨P, Q⟩ := pq
  cases P <;> cases Q <;>
    simp only [checkStep, pairing, finalExponentiation_mul] <;> exact (mul_one _).symm

/-- The check of a list of pairs passes exactly when the product of their pairings is 1. -/
theorem pairingCheck_eq_true_iff (l : List (Point × Point2)) :
    pairingCheck l = true ↔ (l.map fun pq => pairing pq.1 pq.2).prod = 1 := by
  have hfold (acc : Fp12) : finalExponentiation (l.foldl checkStep acc) =
      finalExponentiation acc * (l.map fun pq => pairing pq.1 pq.2).prod := by
    induction l generalizing acc with
    | nil => simp
    | cons pq l ih => rw [List.foldl_cons, ih, finalExponentiation_checkStep, List.map_cons,
        List.prod_cons, mul_assoc]
  have hcheck : pairingCheck l = (finalExponentiation (l.foldl checkStep 1) == 1) := rfl
  rw [hcheck, beq_iff_eq, hfold, finalExponentiation_one, one_mul]

/-- The check of `[(P1, P2)]` fails. -/
theorem pairingCheck_generators : pairingCheck [(Point.generator, Point2.generator)] = false := by
  rw [Bool.eq_false_iff, ne_eq, pairingCheck_eq_true_iff]
  simpa using pairing_generators_ne_one

/-- Under bilinearity, the product of the pairings is a power of `e(P1, P2)`. -/
private theorem prod_pairing (h : PairingBilinear) :
    ∀ (pairs : List (Point × Point2)) (a b : List (ZMod Fr.modulus)) (ha : a.length = pairs.length)
      (hb : b.length = pairs.length),
      (∀ i (hi : i < pairs.length),
        (pairs[i]).1.Represents (a[i]'(ha ▸ hi)) ∧ (pairs[i]).2.Represents (b[i]'(hb ▸ hi))) →
      (pairs.map fun pq => pairing pq.1 pq.2).prod =
        pairing Point.generator Point2.generator ^
          (List.zipWith (fun x y => x.val * y.val) a b).sum
  | [], [], [], _, _, _ => by simp
  | [], _ :: _, _, ha, _, _ => by simp at ha
  | [], [], _ :: _, _, hb, _ => by simp at hb
  | _ :: _, [], _, ha, _, _ => by simp at ha
  | _ :: _, _ :: _, [], _, hb, _ => by simp at hb
  | pq :: ps, x :: xs, y :: ys, ha, hb, hr => by
    obtain ⟨hP, hQ⟩ := hr 0 (by simp)
    have ih := prod_pairing h ps xs ys (by simpa using ha) (by simpa using hb) fun i hi => by
      have := hr (i + 1) (Nat.succ_lt_succ hi)
      simpa only [List.getElem_cons_succ] using this
    simp only [List.getElem_cons_zero] at hP hQ
    rw [List.map_cons, List.prod_cons, ih, List.zipWith_cons_cons, List.sum_cons, pow_add, hP, hQ,
      h]

/-- Bilinearity gives the pairing law of the check. -/
theorem PairingLaws.of_bilinear (h : PairingBilinear) : PairingLaws where
  pairingCheck_iff pairs a b ha hb hr := by
    rw [pairingCheck_eq_true_iff, prod_pairing h pairs a b ha hb hr, ← dvd_sum_zipWith_val_iff]
    have hord := orderOf_pairing_generators
    exact (hord ▸ orderOf_dvd_iff_pow_eq_one).symm

end EthLib.Cryptography.AltBn128
