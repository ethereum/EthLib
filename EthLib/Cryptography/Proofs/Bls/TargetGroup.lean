module

public import EthLib.Cryptography.Proofs.Bls.PairingBilinear
import EthLib.Cryptography.Proofs.Bls.PairingAte

/-!
# Proofs: a model of the target group of the pairing

The pairing maps a point of `G1` and a point of `G2` into a target group `GT`.

The model takes `GT` as a commutative monoid with an element `gT` of order `r`.

An element represents a scalar `t` of `Fr` when it is `gT^t`.

The pairing law of the model says that the pairing of `a g1` and `b g2` represents `a b`.

The pairing of BLS12-381, into `Fp12`, is such a model.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open scoped EthLib.Cryptography.Bls.Fr

/-- A target group: a pairing into a commutative monoid, with the pairing law on its scalars.

The generator is the pairing of the generators of `G1` and `G2`, and it has order `r`. -/
structure TargetGroup (GT : Type) [CommMonoid GT] where
  /-- The pairing. -/
  pair : G1 → G2 → GT
  /-- The generator of the target group. -/
  generator : GT
  /-- The generator has order dividing `r`. -/
  pow_modulus : generator ^ Fr.modulus = 1
  /-- The generator is not 1, so its order is `r`. -/
  generator_ne_one : generator ≠ 1
  /-- The pairing of `a g1` and `b g2` is the generator to the power `a b`. -/
  pair_represents : ∀ {P : G1} {Q : G2} {a b : Fr}, G1.Represents P a → G2.Represents Q b →
    pair P Q = generator ^ (a * b).val

namespace TargetGroup

variable {GT : Type} [CommMonoid GT] (M : TargetGroup GT)

/-- An element represents `t` when it is the generator to the power `t`. -/
def Represents (x : GT) (t : Fr) : Prop := x = M.generator ^ t.val

/-- The generator has order `r`. -/
theorem orderOf_generator : orderOf M.generator = Fr.modulus :=
  orderOf_eq_prime M.pow_modulus M.generator_ne_one

/-- An element represents at most one scalar. -/
theorem Represents.unique {M : TargetGroup GT} {x : GT} {s t : Fr} (hs : M.Represents x s)
    (ht : M.Represents x t) : s = t := by
  have h := hs.symm.trans ht
  have hfin : IsOfFinOrder M.generator :=
    orderOf_pos_iff.mp (M.orderOf_generator ▸ Fr.modulus_pos)
  rw [hfin.pow_inj_mod, M.orderOf_generator, Nat.mod_eq_of_lt (Fr.val_lt s),
    Nat.mod_eq_of_lt (Fr.val_lt t)] at h
  exact Fr.ext h

/-- The pairing of representatives represents the product of their scalars. -/
theorem represents_pair {P : G1} {Q : G2} {a b : Fr} (hP : G1.Represents P a)
    (hQ : G2.Represents Q b) : M.Represents (M.pair P Q) (a * b) :=
  M.pair_represents hP hQ

/-- The identity represents zero. -/
theorem represents_one : M.Represents 1 0 := by
  simp [Represents]

/-- A product of representatives represents the sum of their scalars. -/
theorem Represents.mul {M : TargetGroup GT} {x y : GT} {s t : Fr} (hx : M.Represents x s)
    (hy : M.Represents y t) : M.Represents (x * y) (s + t) := by
  have h := pow_mod_orderOf M.generator (s.val + t.val)
  rw [M.orderOf_generator] at h
  rw [Represents, hx, hy, ← pow_add, Fr.val_add, h]

/-- A product of pairings of representatives represents the sum of the products of scalars. -/
theorem represents_prod_pair {ι : Type} (s : Finset ι) {P : ι → G1} {Q : ι → G2} {a b : ι → Fr}
    (h : ∀ i ∈ s, G1.Represents (P i) (a i) ∧ G2.Represents (Q i) (b i)) :
    M.Represents (∏ i ∈ s, M.pair (P i) (Q i)) (∑ i ∈ s, a i * b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.represents_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have hjr := h j (Finset.mem_insert_self j s)
    exact (M.represents_pair hjr.1 hjr.2).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end TargetGroup

/-! ## The pairing of BLS12-381 -/

/-- Pairs of representatives whose products of scalars sum to zero.

The check accepts them, so the product of their pairings is 1. -/
private theorem pairing_mul_eq_one (l : List (G1 × G2)) (a b : List Fr)
    (ha : a.length = l.length) (hb : b.length = l.length)
    (hr : ∀ i (h : i < l.length),
      G1.Represents (l[i]).1 (a[i]'(ha ▸ h)) ∧ G2.Represents (l[i]).2 (b[i]'(hb ▸ h)))
    (hsum : (List.zipWith (· * ·) a b).sum = 0) :
    (l.map fun pq => pairing pq.1 pq.2).prod = 1 :=
  (pairingCheck_toArray_iff l).mp ((pairingLaws.pairingCheck_iff l a b ha hb hr).mpr hsum)

/-- The scalars of the check on `(P, Q)` and `(-(a b) g1, g2)`. -/
private theorem sum_two (a b : Fr) :
    (List.zipWith (· * ·) [a, -(a * b)] [b, 1]).sum = 0 := by
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil]
  ring

/-- The scalars of the check on `c` copies of `(g1, g2)` and on `(-c g1, g2)`. -/
private theorem sum_replicate (c : Fr) :
    (List.zipWith (· * ·) (List.replicate c.val 1 ++ [-c])
      (List.replicate c.val 1 ++ [1])).sum = 0 := by
  rw [List.zipWith_append (by simp), List.zipWith_replicate, List.sum_append, List.sum_replicate]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
    nsmul_eq_mul, min_self, Fr.natCast_val, mul_one]
  ring

/-- Entry `i` of `n` copies of `x` followed by `y` is `x` below `n`, and `y` at `n`. -/
private theorem getElem_replicate_append {α : Type} {n i : Nat} (x y : α)
    (hi : i < (List.replicate n x ++ [y]).length) :
    (List.replicate n x ++ [y])[i] = if i < n then x else y := by
  have hi' : i < n + 1 := by simpa using hi
  by_cases h : i < n
  · simp only [h, ↓reduceIte]
    rw [List.getElem_append_left (by simpa using h), List.getElem_replicate]
  · simp only [h, ↓reduceIte]
    rw [List.getElem_append_right (by simpa using h)]
    have hin : i - (List.replicate n x).length = 0 := by simp only [List.length_replicate]; omega
    simp only [hin, List.getElem_singleton]

/-- `e(P, Q) = e(g1, g2)^(a b)` for representatives. -/
theorem pairing_eq_pow_of_laws {P : G1} {Q : G2} {a b : Fr}
    (hP : G1.Represents P a) (hQ : G2.Represents Q b) :
    pairing P Q = pairing G1.generator G2.generator ^ (a * b).val := by
  -- Both sides times `e(-(a b) g1, g2)` give 1, by the check on two lists of pairs.
  set c := a * b
  set N := G1.mul (G1.generator : G1) (-c)
  have hN : G1.Represents N (-c) := G1.represents_mul_generator (-c)
  have h₁ := pairing_mul_eq_one [(P, Q), (N, G2.generator)] [a, -c] [b, 1] rfl rfl
    (fun i hi => by
      match i, hi with
      | 0, _ => exact ⟨hP, hQ⟩
      | 1, _ => exact ⟨hN, G2.represents_generator⟩)
    (by exact sum_two a b)
  have h₂ := pairing_mul_eq_one
    (List.replicate c.val (G1.generator, G2.generator) ++ [(N, G2.generator)])
    (List.replicate c.val (1 : Fr) ++ [(-c : Fr)]) (List.replicate c.val (1 : Fr) ++ [(1 : Fr)])
    (by simp)
    (by simp)
    (fun i hi => by
      rw [getElem_replicate_append, getElem_replicate_append, getElem_replicate_append]
      split
      · exact ⟨G1.represents_generator, G2.represents_generator⟩
      · exact ⟨hN, G2.represents_generator⟩)
    (by exact sum_replicate c)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h₁
  simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h₂
  calc pairing P Q
      = pairing P Q * (pairing G1.generator G2.generator ^ c.val * pairing N G2.generator) := by
        rw [h₂, mul_one]
    _ = pairing G1.generator G2.generator ^ c.val * (pairing P Q * pairing N G2.generator) := by
        ring
    _ = _ := by rw [h₁, mul_one]

/-- The pairing of BLS12-381 is a model of the target group.

Its target is `Fp12`, and its generator is `e(g1, g2)`. -/
noncomputable def TargetGroup.ofPairingLaws : TargetGroup Fp12 where
  pair := pairing
  generator := pairing G1.generator G2.generator
  pow_modulus := orderOf_pairing_generators ▸ pow_orderOf_eq_one _
  generator_ne_one := pairing_generators_ne_one
  pair_represents hP hQ := pairing_eq_pow_of_laws hP hQ

end EthLib.Cryptography.Bls
