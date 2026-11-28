module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Proofs.Bls.G1Group
public import EthLib.Cryptography.Proofs.Bls.G2Group
public import EthLib.Cryptography.Proofs.Bls.MillerLoop

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

/-- A doubling step multiplies `f` by a factor that does not depend on `f`. -/
private theorem millerDouble_eq (T : G2) (xp yp : Fp) (f : Fp12) :
    millerDouble T xp yp f = ((millerDouble T xp yp 1).1, f * (millerDouble T xp yp 1).2) := by
  simp only [millerDouble, mulLine_eq, one_mul]

/-- An addition step multiplies `f` by a factor that does not depend on `f`. -/
private theorem millerAdd_eq (T : G2) (xq yq : Fp2) (xp yp : Fp) (f : Fp12) :
    millerAdd T xq yq xp yp f =
      ((millerAdd T xq yq xp yp 1).1, f * (millerAdd T xq yq xp yp 1).2) := by
  simp only [millerAdd, mulLine_eq, one_mul]

/-- One bit of the loop of several pairs is the bit of each pair, with the product of the lines. -/
private theorem millerLines_eq (b : Bool) (xs : List (MillerState Fp)) (f : Fp12) :
    millerLines b xs f = (xs.flatMap fun x => (millerLines b [x] 1).1,
      f * (xs.map fun x => (millerLines b [x] 1).2).prod) := by
  induction xs generalizing f with
  | nil => simp [millerLines]
  | cons x xs ih =>
    rw [millerLines.eq_2, List.flatMap_cons, List.map_cons, List.prod_cons,
      millerLines.eq_2 b 1 x [], millerDouble_eq x.t _ _ f]
    cases b
    · simp [millerLines.eq_1, ih, mul_assoc]
    · simp [millerLines.eq_1, millerAdd_eq _ _ _ _ _ (f * _),
        millerAdd_eq _ _ _ _ _ (millerDouble x.t x.p.1 x.p.2 1).2, ih, mul_assoc]

/-- A product over a flattened list, regrouped by the outer list. -/
private theorem prod_pow_mul_flatMap {α : Type} (xs : List α) (a : α → Fp12)
    (c : α → List (MillerState Fp)) (h : MillerState Fp → Fp12) (k : ℕ) :
    (xs.map a).prod ^ k * ((xs.flatMap c).map h).prod =
      (xs.map fun x => a x ^ k * ((c x).map h).prod).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
      List.prod_append, mul_pow, ← ih]
    ring

/-- The loop of several pairs is the product of the loops of each pair, from `f^(2^n)`. -/
theorem millerSteps_eq_prod (s n : ℕ) (xs : List (MillerState Fp)) (f : Fp12) :
    millerSteps s n xs f = f ^ (2 ^ n) * (xs.map fun x => millerSteps s n [x] 1).prod := by
  induction n generalizing xs f with
  | zero => simp [millerSteps]
  | succ n ih =>
    simp only [millerSteps]
    rw [ih, millerLines_eq]
    have hx : ∀ x, millerSteps s n (millerLines ((s >>> n) &&& 1 = 1) [x] 1).1
        (millerLines ((s >>> n) &&& 1 = 1) [x] 1).2 =
          (millerLines ((s >>> n) &&& 1 = 1) [x] 1).2 ^ (2 ^ n) *
            ((millerLines ((s >>> n) &&& 1 = 1) [x] 1).1.map fun y => millerSteps s n [y] 1).prod :=
      fun x => ih _ _
    simp only [Fp12.square_eq, mul_one, hx]
    rw [mul_pow, mul_assoc, prod_pow_mul_flatMap]
    rw [← sq, ← pow_mul, ← pow_succ']

/-- The joint Miller loop is the product of the Miller loops of the pairs. -/
theorem millerLoopAll_eq_prod (s : ℕ) (pairs : List ((Fp2 × Fp2) × (Fp × Fp))) :
    millerLoopAll s pairs = (pairs.map fun qp => millerLoop s qp.1 qp.2).prod := by
  unfold millerLoop millerLoopAll
  rw [millerSteps_eq_prod]
  simp only [Fp12.one_eq_one, one_pow, one_mul, List.map_map, List.map_cons, List.map_nil]
  rfl

/-- The conjugate of a product is the product of the conjugates. -/
private theorem conjugate_prod (l : List Fp12) :
    l.prod.conjugate = (l.map Fp12.conjugate).prod := by
  induction l with
  | nil => apply Fp12.ext <;> simp
  | cons a l ih => rw [List.prod_cons, Fp12.conjugate_mul, ih, List.map_cons, List.prod_cons]

/-- The factors of the pairs are the conjugated loops of the finite pairs. -/
private theorem filterMap_pairFactor (l : List (G1 × G2)) :
    l.filterMap pairFactor = (l.filterMap fun pq =>
        if pq.1.isInfinity || pq.2.isInfinity then none
        else some (pq.2.toAffine, pq.1.toAffine)).map
      fun qp => (millerLoop blsX qp.1 qp.2).conjugate := by
  induction l with
  | nil => rfl
  | cons pq l ih =>
    by_cases h : (pq.1.isInfinity || pq.2.isInfinity) = true
    · simp only [List.filterMap_cons, pairFactor, h, ↓reduceIte, ih]
    · simp only [List.filterMap_cons, pairFactor, h, Bool.false_eq_true, ↓reduceIte, ih,
        List.map_cons]

/-- The pairing check is the final exponentiation of the product of the factors, in order. -/
theorem pairingCheck_eq_finalExp_prod (pairs : Array (G1 × G2)) :
    pairingCheck pairs =
      (finalExponentiation ((pairs.toList.filterMap pairFactor).foldl (· * ·) Fp12.one)).isOne := by
  unfold pairingCheck
  dsimp only
  rw [millerLoopAll_eq_prod, conjugate_prod, List.map_map, filterMap_pairFactor, Fp12.one_eq_one,
    ← List.prod_eq_foldl]
  rfl

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
