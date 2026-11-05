module

public import EthLib.Cryptography.Proofs.Bls.Nondegenerate
public import EthLib.Cryptography.Proofs.Bls.PairingLaws
public import EthLib.Cryptography.Proofs.ZModSum

/-!
# Proofs: the pairing law from bilinearity

The pairing law of the check follows from one equation on the multiples of the generators:

`e(a g1, b g2) = e(g1, g2)^(a b)` for all `a` and `b` in `Fr`.

The check multiplies the factors of its pairs and applies the final exponentiation once.

The final exponentiation is multiplicative.

So the check tests whether the product of the pairings is 1.

By the equation, that product is `e(g1, g2)` to the power `sum_i a_i b_i`.

The pairing of the generators has order `r`, so the power is 1 exactly when `r` divides the sum.

No theorem proves the equation yet, so it stays a hypothesis.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open scoped EthLib.Cryptography.Bls.Fr

/-- Bilinearity on the multiples of the generators: `e(a g1, b g2) = e(g1, g2)^(a b)`. -/
def PairingBilinear : Prop :=
  ∀ a b : Fr, pairing (G1.mul G1.generator a) (G2.mul G2.generator b) =
    pairing G1.generator G2.generator ^ (a.val * b.val)

private theorem finalExponentiation_one : finalExponentiation 1 = 1 := by
  rw [finalExponentiation_eq_pow, one_pow]

/-- The pairing is the final exponentiation of the pair's factor, or 1 without a factor. -/
theorem pairing_eq_factor (P : G1) (Q : G2) :
    pairing P Q = finalExponentiation ((pairFactor (P, Q)).getD 1) := by
  unfold pairing pairFactor
  split
  · rw [Option.getD_none, finalExponentiation_one, Fp12.one_eq_one]
  · rfl

/-- The final exponentiation of the folded factors is the product of the pairings. -/
theorem finalExp_foldl (l : List (G1 × G2)) (acc : Fp12) :
    finalExponentiation ((l.filterMap pairFactor).foldl (· * ·) acc) =
      finalExponentiation acc * (l.map fun pq => pairing pq.1 pq.2).prod := by
  induction l generalizing acc with
  | nil => simp
  | cons pq l ih =>
    rw [List.map_cons, List.prod_cons, pairing_eq_factor]
    cases h : pairFactor pq with
    | none =>
      simp only [List.filterMap_cons, h, Option.getD_none, finalExponentiation_one, one_mul]
      exact ih acc
    | some f =>
      simp only [List.filterMap_cons, h, Option.getD_some, List.foldl_cons]
      rw [ih, finalExponentiation_mul, mul_assoc]

/-- Representatives have the pairing of their group elements. -/
theorem pairing_congr {P : G1} {Q : G2} {a b : Fr} (hP : G1.Represents P a)
    (hQ : G2.Represents Q b) :
    pairing P Q = pairing (G1.mul G1.generator a) (G2.mul G2.generator b) := by
  rw [pairing_eq_factor, pairing_eq_factor,
    pairFactor_congr hP.1 (G1.valid_mul G1.valid_generator a) hP.2 hQ.1
      (G2.valid_mul G2.valid_generator b) hQ.2]

/-- The check of a list of pairs accepts exactly when the product of their pairings is 1. -/
theorem pairingCheck_toArray_iff (l : List (G1 × G2)) :
    pairingCheck l.toArray = true ↔ (l.map fun pq => pairing pq.1 pq.2).prod = 1 := by
  rw [pairingCheck_eq_finalExp_prod, Fp12.isOne_iff, List.toList_toArray, finalExp_foldl,
    Fp12.one_eq_one, finalExponentiation_one, one_mul]

/-- Under bilinearity, the product of the pairings is a power of `e(g1, g2)`. -/
private theorem prod_pairing (h : PairingBilinear) :
    ∀ (pairs : List (G1 × G2)) (a b : List Fr),
      a.length = pairs.length → b.length = pairs.length →
      (∀ i (hi : i < pairs.length),
        G1.Represents (pairs[i]).1 a[i]! ∧ G2.Represents (pairs[i]).2 b[i]!) →
      (pairs.map fun pq => pairing pq.1 pq.2).prod =
        pairing G1.generator G2.generator ^ (List.zipWith (fun x y => x.val * y.val) a b).sum
  | [], [], [], _, _, _ => by simp
  | [], _ :: _, _, ha, _, _ => by simp at ha
  | [], [], _ :: _, _, hb, _ => by simp at hb
  | _ :: _, [], _, ha, _, _ => by simp at ha
  | _ :: _, _ :: _, [], _, hb, _ => by simp at hb
  | pq :: ps, x :: xs, y :: ys, ha, hb, hr => by
    obtain ⟨hP, hQ⟩ := hr 0 (by simp)
    have ih := prod_pairing h ps xs ys (by simpa using ha) (by simpa using hb) fun i hi => by
      have := hr (i + 1) (Nat.succ_lt_succ hi)
      simpa only [List.getElem_cons_succ, List.getElem!_cons_succ] using this
    simp only [List.getElem_cons_zero, List.getElem!_cons_zero] at hP hQ
    rw [List.map_cons, List.prod_cons, ih, List.zipWith_cons_cons, List.sum_cons, pow_add,
      pairing_congr hP hQ, h]

/-- A sum of products of values is zero in `Fr` exactly when `r` divides it.

It is the statement over `ZMod r`, carried to `Fr` by the isomorphism. -/
private theorem dvd_sum_zipWith_val_iff_fr (a b : List Fr) :
    Fr.modulus ∣ (List.zipWith (fun x y => x.val * y.val) a b).sum ↔
      (List.zipWith (· * ·) a b).sum = 0 := by
  have h := dvd_sum_zipWith_val_iff (n := Fr.modulus) (a.map Fr.toZMod) (b.map Fr.toZMod)
  have e1 : List.zipWith (fun x y => x.val * y.val) (a.map Fr.toZMod) (b.map Fr.toZMod) =
      List.zipWith (fun x y => x.val * y.val) a b := by
    rw [List.zipWith_map]
    congr
    funext x y
    rw [Fr.val_eq x, Fr.val_eq y]
    rfl
  have e2 : List.zipWith (· * ·) (a.map Fr.toZMod) (b.map Fr.toZMod) =
      (List.zipWith (· * ·) a b).map Fr.toZMod := by
    rw [List.zipWith_map, List.map_zipWith]
    exact congrArg (fun f => List.zipWith f a b)
      (funext fun x => funext fun y => (map_mul Fr.toZMod x y).symm)
  rw [e1, e2, ← map_list_sum, map_eq_zero_iff _ Fr.toZMod.injective] at h
  exact h

/-- Bilinearity gives the pairing law of the check. -/
theorem PairingLaws.of_bilinear (h : PairingBilinear) : PairingLaws where
  pairingCheck_iff pairs a b ha hb hr := by
    rw [pairingCheck_toArray_iff, prod_pairing h pairs a b ha hb hr]
    have hord := orderOf_pairing_generators
    exact (hord ▸ orderOf_dvd_iff_pow_eq_one).symm.trans
      (dvd_sum_zipWith_val_iff_fr a b)

end EthLib.Cryptography.Bls
