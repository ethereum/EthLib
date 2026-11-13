module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Proofs.Bls.CurveMap

/-!
# Proofs: the BLS12-381 pairing under a map of base fields

A map of base fields that respects their operations commutes with each step of the pairing.

So the Miller loop, the final exponentiation and the pairing give the same value, once mapped.

The pairing check gives the same verdict.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open EthLib.Cryptography.BaseField (Hom)

variable {F G : Type} [BaseField F] [BaseField G]

private theorem G2.map_add' (f : Hom F G) (p q : G2 F) :
    G2.map f (p.add q) = (G2.map f p).add (G2.map f q) :=
  G2.map_add f p q

theorem map_lineValue (f : Hom F G) (c0 c2 c3 : Fp2 F) :
    (lineValue c0 c2 c3).map f = lineValue (c0.map f) (c2.map f) (c3.map f) := by
  simp only [lineValue, Fp12.map, Fp6.map, Fp2.map_zero]

theorem map_millerDouble (f : Hom F G) (T : G2 F) (xp yp : F) (g : Fp12 F) :
    Prod.map (G2.map f) (Fp12.map f) (millerDouble T xp yp g)
      = millerDouble (T.map f) (f xp) (f yp) (g.map f) := by
  simp only [millerDouble, Prod.map, G2.map_double, Fp12.map_mul, map_lineValue,
    Fp2.map_sub, Fp2.map_mul, Fp2.map_neg, Fp2.map_ofFp, f.map_ofNat]
  rfl

theorem map_millerAdd (f : Hom F G) (T : G2 F) (xq yq : Fp2 F) (xp yp : F) (g : Fp12 F) :
    Prod.map (G2.map f) (Fp12.map f) (millerAdd T xq yq xp yp g)
      = millerAdd (T.map f) (xq.map f) (yq.map f) (f xp) (f yp) (g.map f) := by
  simp only [millerAdd, Prod.map, G2.map_add', Fp12.map_mul, map_lineValue,
    Fp2.map_sub, Fp2.map_mul, Fp2.map_neg, Fp2.map_ofFp]
  simp only [G2.map, Fp2.map_one]

theorem map_millerSteps (f : Hom F G) (s : Nat) (xq yq : Fp2 F) (xp yp : F) (n : Nat)
    (T : G2 F) (g : Fp12 F) :
    (millerSteps s xq yq xp yp n T g).map f
      = millerSteps s (xq.map f) (yq.map f) (f xp) (f yp) n (T.map f) (g.map f) := by
  induction n generalizing T g with
  | zero => rfl
  | succ n ih =>
    simp only [millerSteps]
    rw [← map_millerDouble]
    obtain ⟨T1, g1⟩ := millerDouble T xp yp g
    dsimp only [Prod.map]
    by_cases hb : (s >>> n) &&& 1 = 1
    · simp only [hb, ↓reduceIte]
      rw [← map_millerAdd]
      obtain ⟨T2, g2⟩ := millerAdd T1 xq yq xp yp g1
      exact ih T2 g2
    · simp only [hb, ↓reduceIte]
      exact ih T1 g1

theorem map_millerLoop (f : Hom F G) (s : Nat) (q : Fp2 F × Fp2 F) (p : F × F) :
    (millerLoop s q p).map f
      = millerLoop s (Prod.map (Fp2.map f) (Fp2.map f) q) (Prod.map f f p) := by
  simp only [millerLoop, map_millerSteps, Fp12.map_one, G2.map, Fp2.map_one, Prod.map]

theorem map_finalExponentiation (f : Hom F G) (g : Fp12 F) :
    (finalExponentiation g).map f = finalExponentiation (g.map f) := by
  simp only [finalExponentiation, Fp12.map_mul, Fp12.map_conjugate, Fp12.map_inverse,
    Fp12.map_frobenius, Fp12.map_cyclotomicPow]

theorem map_pairing (f : Hom F G) (P : G1 F) (Q : G2 F) :
    (pairing P Q).map f = pairing (P.map f) (Q.map f) := by
  simp only [pairing, G1.map_isInfinity, G2.map_isInfinity, apply_ite (Fp12.map f),
    Fp12.map_one, map_finalExponentiation, Fp12.map_conjugate, map_millerLoop,
    G1.map_toAffine, G2.map_toAffine]

/-- The factor of a pair commutes with the map. -/
private theorem map_pairFactor (f : Hom F G) (pq : G1 F × G2 F) :
    (pairFactor pq).map (Fp12.map f) = pairFactor (Prod.map (G1.map f) (G2.map f) pq) := by
  obtain ⟨p, q⟩ := pq
  unfold pairFactor
  simp only [Prod.map, G1.map_isInfinity, G2.map_isInfinity]
  split
  · rfl
  · rw [Option.map_some, ← G1.map_toAffine, ← G2.map_toAffine, ← map_millerLoop,
      ← Fp12.map_conjugate]

/-- The product of the factors commutes with the map. -/
private theorem map_foldl_pairFactor (f : Hom F G) (l : List (G1 F × G2 F)) (acc : Fp12 F) :
    ((l.filterMap pairFactor).foldl (· * ·) acc).map f =
      ((l.map (Prod.map (G1.map f) (G2.map f))).filterMap pairFactor).foldl (· * ·)
        (acc.map f) := by
  induction l generalizing acc with
  | nil => rfl
  | cons pq l ih =>
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, ← map_pairFactor]
    cases pairFactor pq with
    | none => exact ih acc
    | some x => rw [Option.map_some, List.foldl_cons, List.foldl_cons, ih, Fp12.map_mul]

theorem map_pairingCheck (f : Hom F G) (pairs : Array (G1 F × G2 F)) :
    pairingCheck (pairs.map (Prod.map (G1.map f) (G2.map f))) = pairingCheck pairs := by
  unfold pairingCheck
  rw [← Array.foldl_toList, Array.toList_filterMap, ← Array.foldl_toList, Array.toList_filterMap,
    Array.toList_map, ← Fp12.map_one f, ← map_foldl_pairFactor, ← map_finalExponentiation,
    Fp12.map_isOne]

end EthLib.Cryptography.Bls
