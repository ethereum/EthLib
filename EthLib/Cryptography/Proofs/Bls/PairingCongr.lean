module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Proofs.Bls.G1Group
public import EthLib.Cryptography.Proofs.Bls.G2Group

/-!
# Proofs: the pairing check depends only on affine points

A point has many Jacobian representatives `(X, Y, Z)`.

They all scale to one affine point `(X / Z^2, Y / Z^3)`.

The pairing check reads only that affine point, so every representative gives the same answer.

A pair with a point at infinity adds no factor, so it does not change the answer.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open WeierstrassCurve.Jacobian

/-- Two valid points with the same group element have the same affine coordinates. -/
theorem G1.toAffine_congr {P Q : G1} (hP : G1.Valid P) (hQ : G1.Valid Q)
    (h : G1.toPoint P = G1.toPoint Q) : P.isInfinity = Q.isInfinity ∧ P.toAffine = Q.toAffine :=
  G1.Law.toAffine_congr Fp.embedding 4 hP hQ h

/-- Two valid points with the same group element have the same affine coordinates. -/
theorem G2.toAffine_congr {P Q : G2} (hP : G2.Valid P) (hQ : G2.Valid Q)
    (h : G2.toPoint P = G2.toPoint Q) : P.isInfinity = Q.isInfinity ∧ P.toAffine = Q.toAffine :=
  G1.Law.toAffine_congr Fp2.embedding G2.bTwist hP hQ h

/-- The pairing check is the final exponentiation of the product of the factors, in order. -/
theorem pairingCheck_eq_finalExp_prod (pairs : Array (G1 × G2)) :
    pairingCheck pairs =
      (finalExponentiation ((pairs.toList.filterMap pairFactor).foldl (· * ·) Fp12.one)).isOne := by
  unfold pairingCheck
  rw [← Array.foldl_toList, Array.toList_filterMap]

/-- Pairs whose points have the same group elements have the same factor. -/
theorem pairFactor_congr {p p' : G1} {q q' : G2}
    (hp : G1.Valid p) (hp' : G1.Valid p') (hpp : G1.toPoint p = G1.toPoint p')
    (hq : G2.Valid q) (hq' : G2.Valid q') (hqq : G2.toPoint q = G2.toPoint q') :
    pairFactor (p, q) = pairFactor (p', q') := by
  unfold pairFactor
  dsimp only
  rw [(G1.toAffine_congr hp hp' hpp).1, (G2.toAffine_congr hq hq' hqq).1,
    (G1.toAffine_congr hp hp' hpp).2, (G2.toAffine_congr hq hq' hqq).2]

/-- The pairing check depends only on the group elements of valid points. -/
theorem pairingCheck_congr {ps qs : Array (G1 × G2)} (hsize : ps.size = qs.size)
    (h : ∀ i (hi : i < ps.size),
      G1.Valid ps[i].1 ∧ G1.Valid (qs[i]'(hsize ▸ hi)).1 ∧
        G1.toPoint ps[i].1 = G1.toPoint (qs[i]'(hsize ▸ hi)).1 ∧
      G2.Valid ps[i].2 ∧ G2.Valid (qs[i]'(hsize ▸ hi)).2 ∧
        G2.toPoint ps[i].2 = G2.toPoint (qs[i]'(hsize ▸ hi)).2) :
    pairingCheck ps = pairingCheck qs := by
  have hmap : ps.toList.map pairFactor = qs.toList.map pairFactor := by
    apply List.ext_getElem (by simp [hsize])
    intro i hi _
    simp only [List.length_map, Array.length_toList] at hi
    obtain ⟨hp, hp', hpp, hq, hq', hqq⟩ := h i hi
    simpa using pairFactor_congr hp hp' hpp hq hq' hqq
  -- Both sides drop the missing factors of the same list.
  have hid : ∀ l : List (G1 × G2), l.filterMap pairFactor = (l.map pairFactor).filterMap id :=
    fun l => by rw [List.filterMap_map]; rfl
  rw [pairingCheck_eq_finalExp_prod, pairingCheck_eq_finalExp_prod, hid, hid, hmap]

/-- Appending pairs that each hold a point at infinity does not change the pairing check. -/
theorem pairingCheck_append_infinity (ps qs : Array (G1 × G2))
    (h : ∀ pq ∈ qs, (pq.1.isInfinity || pq.2.isInfinity) = true) :
    pairingCheck (ps ++ qs) = pairingCheck ps := by
  have hnil : qs.toList.filterMap pairFactor = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro pq hpq
    simp [pairFactor, h pq (Array.mem_toList_iff.mp hpq)]
  rw [pairingCheck_eq_finalExp_prod, pairingCheck_eq_finalExp_prod, Array.toList_append,
    List.filterMap_append, hnil, List.append_nil]

end EthLib.Cryptography.Bls
