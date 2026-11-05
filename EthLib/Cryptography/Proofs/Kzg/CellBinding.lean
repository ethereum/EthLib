module

public import EthLib.Cryptography.Proofs.Kzg.CellBatchBinding
public import EthLib.Cryptography.Proofs.Bls.TargetGroup

/-!
# Proofs: two cells with different values give a bilinear strong Diffie–Hellman solution

Let two valid cells at one cell index open one commitment to different values.

Let their values first differ at the point `x` of the coset, by `δ ≠ 0`.

Let `D` be the difference of the polynomials of the two cells, and `Z = X^64 - h^64`.

Validity gives `D(τ) = (w - w') Z(τ)`, for the scalars `w` and `w'` of the two proofs.

Both `D - δ` and `Z` vanish at `x`, so they are `X - x` times quotients `q` and `z`.

Then `1 / (τ - x) = ((w - w') z(τ) - q(τ)) / δ`.

Pairings of the two proofs and of the setup points give that scalar in the target group.

So the search returns `(-x, e(g1, g2)^(1 / (τ - x)))`, a bilinear strong Diffie–Hellman solution.

The problem is Definition 2.4 of the extended KZG paper, CACR 2010-10.

The setup holds powers of `τ` in both groups, so the instance is the asymmetric variant.

The argument follows the proof of Theorem 3.4, the binding of batch openings, in Appendix C.3.

<https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr TargetGroup)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

-- Core's power instance on `Fin` hides Mathlib's power on `Fr`, as in `Proofs.Bls.FrZMod`.
attribute [-instance] Fin.instNatPow

/-! ## The points of a cell -/

/-- The points of the coset of a cell are distinct. -/
theorem cellPoint_injOn {cellIndex : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB) :
    Set.InjOn (cellPoint cellIndex) (Finset.range FIELD_ELEMENTS_PER_CELL) := by
  obtain ⟨coset, hcoset, hcsz, hcelem⟩ := cosetForCell_ok_of_lt hci
  have hdist := cosetForCell_distinct hcoset
  intro a ha b hb hab
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  by_contra hne
  refine hdist a b (by omega) (by omega) hne ?_
  rw [hcelem a ha', hcelem b hb']
  exact hab

/-- A shift times a power of an `n`th root of unity has the `n`th power of the shift. -/
private theorem shift_mul_root_pow (h ω : ZMod Fr.modulus) (k n : Nat) (hω : ω ^ n = 1) :
    (h * ω ^ k) ^ n = h ^ n := by
  rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hω, one_pow, mul_one]

/-- Each point of the coset of a cell is a root of `X^64 - h^64`. -/
theorem cellPoint_pow {cellIndex m : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB)
    (hm : m < FIELD_ELEMENTS_PER_CELL) :
    cellPoint cellIndex m ^ FIELD_ELEMENTS_PER_CELL =
      cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL := by
  obtain ⟨coset, hcoset, hcsz, hcelem⟩ := cosetForCell_ok_of_lt hci
  have h := getElem!_cosetForCell_eq_shift_mul_root hcoset m hm
  rw [hcelem m hm] at h
  have hroot := (isPrimitiveRoot_domainRoot (order := FIELD_ELEMENTS_PER_CELL)
    (Nat.dvd_of_mod_eq_zero (by decide))).pow_eq_one
  rw [cellPoint, h]
  exact shift_mul_root_pow _ _ _ _ hroot

/-- The polynomial of a cell takes the value of the cell at each point of the coset. -/
theorem eval_cellInterpolant_cellPoint {cellIndex m : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB)
    (hm : m < FIELD_ELEMENTS_PER_CELL) (evals : CosetEvals) :
    (cellInterpolant cellIndex evals).eval (cellPoint cellIndex m) = evals[m]! :=
  Lagrange.eval_interpolate_at_node _ (cellPoint_injOn hci) (Finset.mem_range.mpr hm)

/-- The polynomial of a cell has degree below 64. -/
theorem natDegree_cellInterpolant_lt {cellIndex : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB)
    (evals : CosetEvals) :
    (cellInterpolant cellIndex evals).natDegree < FIELD_ELEMENTS_PER_CELL := by
  rcases eq_or_ne (cellInterpolant cellIndex evals) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    decide
  · have h : (cellInterpolant cellIndex evals).degree < _ :=
      Lagrange.degree_interpolate_lt (r := fun m => evals[m]!) (cellPoint_injOn hci)
    rw [Finset.card_range, degree_eq_natDegree h0] at h
    exact WithBot.coe_lt_coe.mp h

/-! ## The search -/

/-- A solution `(c, x)` of the bilinear strong Diffie–Hellman problem for the secret `τ`.

The element `x` of the target group represents `1 / (τ + c)`, and `τ + c ≠ 0`. -/
def IsBsdhSolution {GT : Type} [CommMonoid GT] (M : TargetGroup GT) (τ : Fr) (sol : Fr × GT) :
    Prop :=
  τ + sol.1 ≠ 0 ∧ M.Represents sol.2 (τ + sol.1)⁻¹

/-- The first point of a cell where two arrays of values differ. -/
def firstDiff (evals evals' : CosetEvals) : Option Nat :=
  (List.range FIELD_ELEMENTS_PER_CELL).find? fun m => evals[m]! != evals'[m]!

/-- A point found by the search is in the cell, and the two values differ there. -/
theorem firstDiff_spec {evals evals' : CosetEvals} {m : Nat} (h : firstDiff evals evals' = some m) :
    m < FIELD_ELEMENTS_PER_CELL ∧ evals[m]! ≠ evals'[m]! := by
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [bne_iff_ne, ne_eq] at hp
  exact ⟨List.mem_range.mp hmem, hp⟩

/-- Two arrays of 64 values that differ have a first point where they differ. -/
theorem firstDiff_isSome {evals evals' : CosetEvals} (hs : evals.size = FIELD_ELEMENTS_PER_CELL)
    (hs' : evals'.size = FIELD_ELEMENTS_PER_CELL) (hne : evals ≠ evals') :
    (firstDiff evals evals').isSome := by
  rw [firstDiff, List.find?_isSome]
  by_contra hall
  push Not at hall
  refine hne (Array.ext (hs.trans hs'.symm) fun m hm hm' => ?_)
  have h := hall m (List.mem_range.mpr (hs ▸ hm))
  simp only [bne_iff_ne, ne_eq, not_not] at h
  rwa [getElem!_pos evals m hm, getElem!_pos evals' m hm'] at h

/-- The search finds nothing in two equal arrays of values. -/
theorem firstDiff_self (evals : CosetEvals) : firstDiff evals evals = none := by
  simp [firstDiff]

/-- A cell has no more points than the setup has monomial points in `G1`. -/
theorem cell_le_g1 : FIELD_ELEMENTS_PER_CELL ≤ FIELD_ELEMENTS_PER_BLOB := by decide

/-- A cell has fewer points than the setup has monomial points in `G2`. -/
theorem cell_le_g2 : FIELD_ELEMENTS_PER_CELL ≤ KZG_SETUP_G2_LENGTH := by decide

/-- The quotient of `p - p(x)` by `X - x`. -/
noncomputable def quotientAt (p : Fr[X]) (x : Fr) : Fr[X] := (p - C (p.eval x)) /ₘ (X - C x)

/-- The search of a bilinear strong Diffie–Hellman solution in two cells at one cell index.

The cells have values `evals` and `evals'`, and proofs `P` and `P'`.

Equal values give nothing.

Otherwise, let the values first differ at point `x` of the coset, by `δ`.

Let `D` be the difference of the two polynomials of the cells, and `Z = X^64 - h^64`.

Let `q` and `z` be the quotients of `D - δ` and `Z` by `X - x`.

The search returns `-x` and the product of the pairings that represent `((w - w') z(τ) - q(τ)) / δ`.

The pairings read only the two proofs and the points of the setup. -/
noncomputable def findBsdh {GT : Type} [CommMonoid GT] (M : TargetGroup GT) (s : TrustedSetup)
    (cellIndex : CellIndex) (evals evals' : CosetEvals) (P P' : G1) : Option (Fr × GT) :=
  (firstDiff evals evals').map fun m =>
    let x := cellPoint cellIndex m
    let δ := evals'[m]! - evals[m]!
    let q := quotientAt (cellInterpolant cellIndex evals' - cellInterpolant cellIndex evals) x
    let z := quotientAt (X ^ FIELD_ELEMENTS_PER_CELL) x
    (-x, (∏ k : Fin FIELD_ELEMENTS_PER_CELL,
        M.pair (G1.mul (G1.add P (G1.neg P')) (z.coeff k * δ⁻¹))
          s.g2Monomial[Fin.castLE cell_le_g2 k]) *
      ∏ k : Fin FIELD_ELEMENTS_PER_CELL,
        M.pair (G1.mul s.g1Monomial[Fin.castLE cell_le_g1 k] (-q.coeff k * δ⁻¹)) G2.generator)

/-- The search finds nothing in two cells with equal values. -/
theorem findBsdh_self {GT : Type} [CommMonoid GT] (M : TargetGroup GT) (s : TrustedSetup)
    (cellIndex : CellIndex) (evals : CosetEvals) (P P' : G1) :
    findBsdh M s cellIndex evals evals P P' = none := by
  simp [findBsdh, firstDiff_self]

/-- A polynomial is `X - x` times its quotient at `x`, plus its value at `x`. -/
theorem quotientAt_spec (p : Fr[X]) (x : Fr) : p = (X - C x) * quotientAt p x + C (p.eval x) := by
  have h : (X - C x) * quotientAt p x = p - C (p.eval x) :=
    mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot])
  rw [h, sub_add_cancel]

/-- The quotient at a point lowers the degree. -/
theorem natDegree_quotientAt_lt {p : Fr[X]} {n : Nat} (hp : p.natDegree ≤ n) (hn : 0 < n)
    (x : Fr) : (quotientAt p x).natDegree < n := by
  have h : (p - C (p.eval x)).natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le hp (by simp))
  rw [quotientAt, natDegree_divByMonic _ (monic_X_sub_C x), natDegree_X_sub_C]
  omega

/-- The scalar step: two valid cells with values that differ by `δ` at `x` give `1 / (τ - x)`. -/
private theorem bsdh_scalar {t x δ w w' c i i' zt qt h : ZMod Fr.modulus} (hδ : δ ≠ 0)
    (hq : i' - i = (t - x) * qt + δ) (hz : t ^ FIELD_ELEMENTS_PER_CELL - h = (t - x) * zt)
    (hv : c - i = w * (t ^ FIELD_ELEMENTS_PER_CELL - h))
    (hv' : c - i' = w' * (t ^ FIELD_ELEMENTS_PER_CELL - h)) :
    t + -x ≠ 0 ∧ (t + -x)⁻¹ = (w + -w') * δ⁻¹ * zt + -δ⁻¹ * qt := by
  have key : (t - x) * ((w - w') * zt - qt) = δ := by
    linear_combination hq - hv + hv' - (w - w') * hz
  have htx : t + -x ≠ 0 := by
    intro h0
    rw [← sub_eq_add_neg] at h0
    rw [h0, zero_mul] at key
    exact hδ key.symm
  refine ⟨htx, ?_⟩
  rw [← sub_eq_add_neg] at htx
  have hA : (w - w') * zt - qt ≠ 0 := right_ne_zero_of_mul (key ▸ hδ)
  rw [← sub_eq_add_neg, ← key]
  field_simp
  ring

/-- One term of an evaluation, over `ZMod r` where `ring` applies. -/
private theorem mul_right_comm_pow (c a t : ZMod Fr.modulus) (n : Nat) :
    c * a * t ^ n = a * (c * t ^ n) := by
  ring

/-- One term of the first product of pairings, over `ZMod r`. -/
private theorem term_one (c d w t : ZMod Fr.modulus) (n : Nat) :
    c * (w * d) * t ^ n = c * d * w * t ^ n := by
  ring

/-- One term of the second product of pairings, over `ZMod r`. -/
private theorem term_two (c d t : ZMod Fr.modulus) (n : Nat) :
    c * -d * t ^ n = -c * d * t ^ n * 1 := by
  ring

/-- A polynomial of degree below 64 is the sum of its first 64 coefficients times powers. -/
theorem sum_coeff_mul_pow {p : Fr[X]} (hp : p.natDegree < FIELD_ELEMENTS_PER_CELL) (a t : Fr) :
    ∑ k : Fin FIELD_ELEMENTS_PER_CELL, p.coeff k * a * t ^ k.val = a * p.eval t := by
  rw [eval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range]
  refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
  exact Finset.sum_congr rfl fun k _ => mul_right_comm_pow _ _ _ _

/-- **Two valid cells with different values give a bilinear strong Diffie–Hellman solution.**

Take a model of the target group and a well-formed setup of the secret `τ`.

Let two cells at one cell index have 64 values each, and let their values differ.

Let their proofs represent `w` and `w'`, and let both cells be valid for one commitment `c`.

Then the search on the two cells returns a solution for `τ`. -/
theorem findBsdh_valid {GT : Type} [CommMonoid GT] (M : TargetGroup GT) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {cellIndex : CellIndex} (hci : cellIndex < CELLS_PER_EXT_BLOB)
    {evals evals' : CosetEvals} (hsz : evals.size = FIELD_ELEMENTS_PER_CELL)
    (hsz' : evals'.size = FIELD_ELEMENTS_PER_CELL) (hne : evals ≠ evals') {c w w' : Fr}
    {P P' : G1} (hP : G1.Represents P w) (hP' : G1.Represents P' w')
    (hv : c - (cellInterpolant cellIndex evals).eval τ =
      w * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL))
    (hv' : c - (cellInterpolant cellIndex evals').eval τ =
      w' * (τ ^ FIELD_ELEMENTS_PER_CELL - cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL)) :
    ∃ sol, findBsdh M s cellIndex evals evals' P P' = some sol ∧ IsBsdhSolution M τ sol := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (firstDiff_isSome hsz hsz' hne)
  obtain ⟨hm64, hdiff⟩ := firstDiff_spec hm
  rw [findBsdh, hm, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  simp only
  -- Name the point, the difference of the values and the two quotients.
  generalize hx : cellPoint cellIndex m = x
  generalize hδ : evals'[m]! - evals[m]! = δ
  generalize hD : cellInterpolant cellIndex evals' - cellInterpolant cellIndex evals = D
  generalize hq : quotientAt D x = q
  generalize hz : quotientAt (X ^ FIELD_ELEMENTS_PER_CELL) x = z
  have hδ0 : δ ≠ 0 := hδ ▸ sub_ne_zero.mpr (Ne.symm hdiff)
  have hDx : D.eval x = δ := by
    rw [← hD, ← hx, eval_sub, eval_cellInterpolant_cellPoint hci hm64,
      eval_cellInterpolant_cellPoint hci hm64]
    exact hδ
  have hDτ : (cellInterpolant cellIndex evals').eval τ -
      (cellInterpolant cellIndex evals).eval τ = (τ - x) * q.eval τ + δ := by
    have h := congrArg (eval τ) (quotientAt_spec D x)
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_C, hDx, hq, ← hD, eval_sub] at h
    exact h
  have hZτ : τ ^ FIELD_ELEMENTS_PER_CELL - cellShift cellIndex ^ FIELD_ELEMENTS_PER_CELL =
      (τ - x) * z.eval τ := by
    have h := congrArg (eval τ) (quotientAt_spec (X ^ FIELD_ELEMENTS_PER_CELL) x)
    rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_C, hz] at h
    simp only [eval_pow, eval_X] at h
    rw [← hx, cellPoint_pow hci hm64] at h
    rw [← hx, h]
    exact add_sub_cancel_right _ _
  obtain ⟨htx, hinv⟩ := bsdh_scalar hδ0 hDτ hZτ hv hv'
  refine ⟨htx, ?_⟩
  have hzdeg : z.natDegree < FIELD_ELEMENTS_PER_CELL :=
    hz ▸ natDegree_quotientAt_lt (natDegree_X_pow_le _) (by decide) x
  have hqdeg : q.natDegree < FIELD_ELEMENTS_PER_CELL := by
    refine hq ▸ natDegree_quotientAt_lt ?_ (by decide) x
    rw [← hD]
    exact (lt_of_le_of_lt (natDegree_sub_le _ _)
      (max_lt (natDegree_cellInterpolant_lt hci _) (natDegree_cellInterpolant_lt hci _))).le
  -- Each product of pairings represents one of the two terms.
  have h1 := M.represents_prod_pair (ι := Fin FIELD_ELEMENTS_PER_CELL) Finset.univ fun k _ =>
    ⟨(hP.add hP'.neg).mul (z.coeff k * δ⁻¹), hs.monomial_g2 (Fin.castLE cell_le_g2 k)⟩
  have h2 := M.represents_prod_pair (ι := Fin FIELD_ELEMENTS_PER_CELL) Finset.univ fun k _ =>
    ⟨(hs.monomial_g1 (Fin.castLE cell_le_g1 k)).mul (-q.coeff k * δ⁻¹), G2.represents_generator⟩
  have e1 : (w + -w') * δ⁻¹ * eval τ z = ∑ k : Fin FIELD_ELEMENTS_PER_CELL,
      z.coeff k * δ⁻¹ * (w + -w') * τ ^ (Fin.castLE cell_le_g2 k).val :=
    (sum_coeff_mul_pow hzdeg _ τ).symm.trans (Finset.sum_congr rfl fun k _ => term_one _ _ _ _ _)
  have e2 : -δ⁻¹ * eval τ q = ∑ k : Fin FIELD_ELEMENTS_PER_CELL,
      -q.coeff k * δ⁻¹ * τ ^ (Fin.castLE cell_le_g1 k).val * 1 :=
    (sum_coeff_mul_pow hqdeg _ τ).symm.trans (Finset.sum_congr rfl fun k _ => term_two _ _ _ _)
  show M.Represents (_ * _) (τ + -x)⁻¹
  have key : (τ + -x)⁻¹ = _ := hinv.trans (congrArg₂ (· + ·) e1 e2)
  rw [key]
  exact h1.mul h2

/-! ## Binding of the batch check of cells -/

/-- A batch of cells that the check accepts has as many proofs as cells. -/
theorem proofs_size_of_verifyCellKzgProofBatchImpl {s : TrustedSetup}
    {commitments : Array KZGCommitment} {commitmentIndices : Array CommitmentIndex}
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    {b : Bool} (h : verifyCellKzgProofBatchImpl s commitments commitmentIndices cellIndices
      cosetsEvals proofs = .ok b) :
    proofs.size = cellIndices.size := by
  unfold verifyCellKzgProofBatchImpl at h
  by_cases h₁ : cellIndices.size ≠ commitmentIndices.size
  · simp [h₁, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₂ : cosetsEvals.size ≠ commitmentIndices.size
  · simp [h₁, h₂, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₃ : proofs.size ≠ commitmentIndices.size
  · simp [h₁, h₂, h₃, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [ne_eq, Decidable.not_not] at h₁ h₃
  rw [h₁, h₃]

/-- **Binding of the batch check of cells.**

Take a model of the target group, the pairing law and a well-formed setup of the secret `τ`.

Let an accepted batch hold two cells of 64 values at one cell index below 128.

Let their commitments represent one scalar.

Then one of three cases holds.

- The two cells have the same values.
- The search on the two cells returns a bilinear strong Diffie–Hellman solution for `τ`.
- The challenge is a root of the error polynomial of the cells, which is not zero. -/
theorem verifyCellKzgProofBatchImpl_binding {GT : Type} [CommMonoid GT] (M : TargetGroup GT)
    (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {commitments : Array KZGCommitment} {commitmentIndices : Array CommitmentIndex}
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    {commitmentsG1 proofsG1 : Array G1} {c w : Nat → Fr}
    (hCd : commitments.mapM uncompressG1 = .ok commitmentsG1)
    (hPd : proofs.mapM uncompressG1 = .ok proofsG1)
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ k < proofsG1.size, G1.Represents proofsG1[k]! (w k))
    (h : verifyCellKzgProofBatchImpl s commitments commitmentIndices cellIndices cosetsEvals
      proofs = .ok true)
    {k k' : Nat} (hk : k < cellIndices.size) (hk' : k' < cellIndices.size)
    (hc : c commitmentIndices[k]! = c commitmentIndices[k']!)
    (hj : cellIndices[k]! = cellIndices[k']!) (hci : cellIndices[k]! < CELLS_PER_EXT_BLOB)
    (hsz : cosetsEvals[k]!.size = FIELD_ELEMENTS_PER_CELL)
    (hsz' : cosetsEvals[k']!.size = FIELD_ELEMENTS_PER_CELL) :
    cosetsEvals[k]! = cosetsEvals[k']! ∨
      (∃ sol, findBsdh M s cellIndices[k]! cosetsEvals[k]! cosetsEvals[k']! proofsG1[k]!
        proofsG1[k']! = some sol ∧ IsBsdhSolution M τ sol) ∨
      (cellErrorPoly τ c w commitmentIndices cellIndices cosetsEvals ≠ 0 ∧
        (cellErrorPoly τ c w commitmentIndices cellIndices cosetsEvals).eval
          (computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices cellIndices
            cosetsEvals proofs) = 0) := by
  by_cases hne : cosetsEvals[k]! = cosetsEvals[k']!
  · exact Or.inl hne
  rcases verifyCellKzgProofBatchImpl_valid_or_root laws hs hCd hPd hC hP h with hall | hroot
  · -- The batch has as many proofs as cells, so both proofs represent their scalars.
    have hsize : proofsG1.size = cellIndices.size :=
      (array_mapM_ok hPd).1.trans (proofs_size_of_verifyCellKzgProofBatchImpl h)
    have hv := hall k hk
    have hv' := hall k' hk'
    rw [← hc, ← hj] at hv'
    exact Or.inr (Or.inl (findBsdh_valid M hs hci hsz hsz' hne (hP k (by omega))
      (hP k' (by omega)) hv hv'))
  · exact Or.inr (Or.inr hroot)

end EthLib.Cryptography.Kzg
