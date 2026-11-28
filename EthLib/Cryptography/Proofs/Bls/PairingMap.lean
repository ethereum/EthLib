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

theorem map_mulLine (f : Hom F G) (g : Fp12 F) (c0 c2 c3 : Fp2 F) :
    (g.mulLine c0 c2 c3).map f = (g.map f).mulLine (c0.map f) (c2.map f) (c3.map f) := by
  simp only [Fp12.mulLine, Fp12.map, Fp6.map_add, Fp6.map_sub, Fp6.map_mulBy01, Fp6.map_mulBy1,
    Fp6.map_mulByV, Fp2.map_add]

theorem map_millerDouble (f : Hom F G) (T : G2 F) (xp yp : F) (g : Fp12 F) :
    Prod.map (G2.map f) (Fp12.map f) (millerDouble T xp yp g)
      = millerDouble (T.map f) (f xp) (f yp) (g.map f) := by
  simp only [millerDouble, Prod.map, G2.map_double, map_mulLine,
    Fp2.map_add, Fp2.map_sub, Fp2.map_mul, Fp2.map_neg, Fp2.map_square, Fp2.map_mulFp]
  rfl

theorem map_millerAdd (f : Hom F G) (T : G2 F) (xq yq : Fp2 F) (xp yp : F) (g : Fp12 F) :
    Prod.map (G2.map f) (Fp12.map f) (millerAdd T xq yq xp yp g)
      = millerAdd (T.map f) (xq.map f) (yq.map f) (f xp) (f yp) (g.map f) := by
  simp only [millerAdd, Prod.map, G2.map_add_fn, map_mulLine,
    Fp2.map_sub, Fp2.map_mul, Fp2.map_neg, Fp2.map_square, Fp2.map_mulFp]
  simp only [G2.map, G1.map, Fp2.hom, Fp2.map_one]

/-- A pair of the Miller loop, with each coordinate mapped. -/
def MillerState.map (f : Hom F G) (x : MillerState F) : MillerState G :=
  ⟨Prod.map (Fp2.map f) (Fp2.map f) x.q, Prod.map f f x.p, x.t.map f⟩

theorem map_millerLines (f : Hom F G) (b : Bool) (xs : List (MillerState F)) (g : Fp12 F) :
    Prod.map (List.map (MillerState.map f)) (Fp12.map f) (millerLines b xs g)
      = millerLines b (xs.map (MillerState.map f)) (g.map f) := by
  induction xs generalizing g with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨⟨xq, yq⟩, ⟨xp, yp⟩, T⟩ := x
    simp only [millerLines, List.map_cons, MillerState.map, Prod.map]
    rw [← map_millerDouble]
    obtain ⟨T1, g1⟩ := millerDouble T xp yp g
    dsimp only [Prod.map]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← ih g1]
      rfl
    · simp only [↓reduceIte]
      rw [← map_millerAdd]
      obtain ⟨T2, g2⟩ := millerAdd T1 xq yq xp yp g1
      dsimp only [Prod.map]
      rw [← ih g2]
      rfl

theorem map_millerSteps (f : Hom F G) (s n : Nat) (xs : List (MillerState F)) (g : Fp12 F) :
    (millerSteps s n xs g).map f = millerSteps s n (xs.map (MillerState.map f)) (g.map f) := by
  induction n generalizing xs g with
  | zero => rfl
  | succ n ih =>
    simp only [millerSteps]
    rw [← Fp12.map_square, ← map_millerLines]
    exact ih _ _

theorem map_millerLoopAll (f : Hom F G) (s : Nat) (pairs : List ((Fp2 F × Fp2 F) × (F × F))) :
    (millerLoopAll s pairs).map f
      = millerLoopAll s
        (pairs.map (Prod.map (Prod.map (Fp2.map f) (Fp2.map f)) (Prod.map f f))) := by
  simp only [millerLoopAll, map_millerSteps, Fp12.map_one, List.map_map]
  congr 2
  funext qp
  simp only [Function.comp, MillerState.map, G2.map, G1.map, Fp2.hom, Fp2.map_one, Prod.map]

theorem map_millerLoop (f : Hom F G) (s : Nat) (q : Fp2 F × Fp2 F) (p : F × F) :
    (millerLoop s q p).map f
      = millerLoop s (Prod.map (Fp2.map f) (Fp2.map f) q) (Prod.map f f p) := by
  simp only [millerLoop, map_millerLoopAll, List.map_cons, List.map_nil]
  rfl

theorem map_finalExponentiation (f : Hom F G) (g : Fp12 F) :
    (finalExponentiation g).map f = finalExponentiation (g.map f) := by
  simp only [finalExponentiation, Fp12.map_mul, Fp12.map_conjugate, Fp12.map_inverse,
    Fp12.map_frobenius, Fp12.map_cyclotomicPow, Fp12.map_compressedPow]

/-- The factor of a pair commutes with the map. -/
private theorem map_pairFactor (f : Hom F G) (pq : G1 F × G2 F) :
    (pairFactor pq).map (Fp12.map f) = pairFactor (Prod.map (G1.map f.toHom) (G2.map f) pq) := by
  obtain ⟨p, q⟩ := pq
  unfold pairFactor
  simp only [Prod.map, G1.map_isInfinity, G2.map_isInfinity]
  split
  · rfl
  · rw [Option.map_some, ← G1.map_toAffine, ← G2.map_toAffine, ← map_millerLoop,
      ← Fp12.map_conjugate]

theorem map_pairing (f : Hom F G) (P : G1 F) (Q : G2 F) :
    (pairing P Q).map f = pairing (P.map f.toHom) (Q.map f) := by
  unfold pairing
  rw [show (P.map f.toHom, Q.map f) = Prod.map (G1.map f.toHom) (G2.map f) (P, Q) from rfl,
    ← map_pairFactor]
  cases pairFactor (P, Q) with
  | none => exact Fp12.map_one f
  | some x => exact map_finalExponentiation f x

/-- The affine coordinates of the finite pairs commute with the map. -/
private theorem map_filterMap_finite (f : Hom F G) (l : List (G1 F × G2 F)) :
    (l.map (Prod.map (G1.map f.toHom) (G2.map f))).filterMap (fun pq =>
        if pq.1.isInfinity || pq.2.isInfinity then none else some (pq.2.toAffine, pq.1.toAffine))
      = (l.filterMap fun pq =>
          if pq.1.isInfinity || pq.2.isInfinity then none
          else some (pq.2.toAffine, pq.1.toAffine)).map
        (Prod.map (Prod.map (Fp2.map f) (Fp2.map f)) (Prod.map f f)) := by
  induction l with
  | nil => rfl
  | cons pq l ih =>
    obtain ⟨p, q⟩ := pq
    simp only [List.map_cons, List.filterMap_cons, Prod.map, G1.map_isInfinity,
      G2.map_isInfinity]
    by_cases h : (p.isInfinity || q.isInfinity) = true
    · simp only [h, ↓reduceIte, ih]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ih, List.map_cons, ← G1.map_toAffine,
        ← G2.map_toAffine]
      rfl

theorem map_pairingCheck (f : Hom F G) (pairs : Array (G1 F × G2 F)) :
    pairingCheck (pairs.map (Prod.map (G1.map f.toHom) (G2.map f))) = pairingCheck pairs := by
  unfold pairingCheck
  dsimp only
  rw [Array.toList_map, map_filterMap_finite, ← Fp12.map_isOne f (finalExponentiation _),
    map_finalExponentiation, Fp12.map_conjugate, map_millerLoopAll]

end EthLib.Cryptography.Bls
