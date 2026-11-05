module

public import EthLib.Cryptography.Proofs.Kzg.BatchChallenge
public import EthLib.Cryptography.Proofs.Kzg.CosetInterpolation
public import EthLib.Cryptography.Proofs.Kzg.ExtendedCells

/-!
# Proofs: the batch check of cell proofs, as a root of an error polynomial

A cell `k` claims 64 values of the polynomial of commitment `i_k` on the coset of cell index `j_k`.

The coset is `h ω^m` for `m < 64`, with the shift `h` and a primitive 64th root `ω`.

Let `I_k` be the polynomial of degree below 64 with these values on the coset.

The vanishing polynomial of the coset is `X^64 - h^64`.

Let the cell have commitment `c_{i_k}` and proof `w_k`.

The cell is valid when `c_{i_k} - I_k(τ) = w_k (τ^64 - h^64)`.

Its error is the difference of the two sides.

The error polynomial is `P(X) = sum_k e_k X^k`.

Under the pairing law, the batch check accepts exactly when its challenge `r` is a root of `P`.

So an accepted batch has every cell valid, or `r` is a root of a nonzero `P`.

This file does not reduce the binding of cells to a hard problem.

Two different cells at one index would solve a bilinear variant of strong Diffie–Hellman.

That solution lies in the target group of the pairing, which EthLib does not model.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

-- Core's power instance on `Fin` hides Mathlib's power on `Fr`, as in `Proofs.Bls.FrZMod`.
attribute [-instance] Fin.instNatPow

/-! ## Valid cells -/

/-- Point `m` of the coset of cell index `j`: entry `64 j + m` of the bit-reversed domain. -/
def cellPoint (cellIndex m : Nat) : Fr :=
  (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex + m]!

/-- The shift `h` of the coset of cell index `j`, so that point `m` is `h ω^(rev m)`. -/
def cellShift (cellIndex : Nat) : Fr :=
  (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]!

/-- The polynomial of degree below 64 that takes the values of a cell on its coset. -/
noncomputable def cellInterpolant (cellIndex : Nat) (evals : CosetEvals) : Fr[X] :=
  Lagrange.interpolate (Finset.range FIELD_ELEMENTS_PER_CELL) (cellPoint cellIndex)
    fun m => evals[m]!

/-- The error of a cell: zero exactly when `c - I(τ) = w (τ^64 - h^64)`. -/
def cellError (τ c w h : Fr) (interpolant : Fr[X]) : Fr :=
  c - interpolant.eval τ - w * (τ ^ FIELD_ELEMENTS_PER_CELL - h ^ FIELD_ELEMENTS_PER_CELL)

/-- The error polynomial of a batch of cells.

Cell `k` has commitment `c (commitmentIndices[k])` and proof `w k`.

It has cell index `cellIndices[k]` and values `cosetsEvals[k]`. -/
noncomputable def cellErrorPoly (τ : Fr) (c w : Nat → Fr)
    (commitmentIndices : Array CommitmentIndex) (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals) : Fr[X] :=
  errorPoly (fun k => cellError τ (c commitmentIndices[k]!) (w k) (cellShift cellIndices[k]!)
    (cellInterpolant cellIndices[k]! cosetsEvals[k]!)) cellIndices.size

/-- The error polynomial of cells is zero exactly when every cell is valid. -/
theorem cellErrorPoly_eq_zero_iff (τ : Fr) (c w : Nat → Fr)
    (commitmentIndices : Array CommitmentIndex) (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals) :
    cellErrorPoly τ c w commitmentIndices cellIndices cosetsEvals = 0 ↔
      ∀ k < cellIndices.size,
        c commitmentIndices[k]! - (cellInterpolant cellIndices[k]! cosetsEvals[k]!).eval τ =
          w k * (τ ^ FIELD_ELEMENTS_PER_CELL -
            cellShift cellIndices[k]! ^ FIELD_ELEMENTS_PER_CELL) := by
  rw [cellErrorPoly, errorPoly_eq_zero_iff]
  exact forall₂_congr fun k _ => sub_eq_zero

/-! ## The interpolation of the check -/

/-- The interpolation of the check gives the polynomial of the cell, at every point. -/
theorem evalPolyAt_interpolateCosetEvals {cellIndex : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB)
    {evals : CosetEvals} (hevals : evals.size = FIELD_ELEMENTS_PER_CELL) {p : PolynomialCoeff}
    (hp : interpolateCosetEvals (cellShift cellIndex) evals = .ok p) (x : Fr) :
    evalPolyAt p x = (cellInterpolant cellIndex evals).eval x := by
  obtain ⟨coset, hcoset, hcsz, hcelem⟩ := cosetForCell_ok_of_lt hci
  obtain ⟨q, hq, -, hqsz, hqeval⟩ :=
    interpolateCosetEvals_eq_interpolatePolynomialcoeff hcoset hevals
  have hpq : p = q := Except.ok.inj (hp.symm.trans hq)
  subst hpq
  rw [← eval_coefficientPolynomial]
  congr 1
  have hdist := cosetForCell_distinct hcoset
  refine Lagrange.eq_interpolate_of_eval_eq _ ?_ ?_ fun m hm => ?_
  · intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    by_contra hne
    refine hdist a b (by omega) (by omega) hne ?_
    rw [hcelem a ha', hcelem b hb']
    exact hab
  · rw [Finset.card_range]
    rcases eq_or_ne (coefficientPolynomial p) 0 with h0 | h0
    · rw [h0, degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0]
      exact WithBot.coe_lt_coe.mpr
        (hqsz ▸ natDegree_coefficientPolynomial_lt (by rw [hqsz]; decide))
  · have hm' := Finset.mem_range.mp hm
    rw [eval_coefficientPolynomial, cellPoint, ← hcelem m hm',
      ← evaluatePolynomialcoeff_eq_evalPolyAt]
    exact hqeval m hm'

/-! ## Folds and maps of the check -/

/-- A successful map over an array keeps its size, and output `i` is the image of input `i`. -/
theorem array_mapM_ok {ε α β : Type} [Inhabited α] [Inhabited β] {f : α → Except ε β}
    {xs : Array α} {ys : Array β} (h : xs.mapM f = .ok ys) :
    ys.size = xs.size ∧ ∀ i < xs.size, f xs[i]! = .ok ys[i]! := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok zs =>
    rw [hl] at h
    have hys : zs.toArray = ys := Except.ok.inj h
    subst hys
    have hlen := Base.mapM_ok_length hl
    refine ⟨by simpa using hlen, fun i hi => ?_⟩
    have hi' : i < xs.toList.length := by simpa using hi
    have := Base.mapM_ok_getElem hl i hi'
    rw [getElem!_pos xs i hi, getElem!_pos zs.toArray i (by simp; omega)]
    simpa using this

/-- A sum over the pairs of two arrays of one size, as a sum over the indices. -/
theorem sum_zip_toList {α β M : Type} [Inhabited α] [Inhabited β] [AddCommMonoid M]
    (a : Array α) (b : Array β) (hab : a.size = b.size) (g : α × β → M) :
    ((a.zip b).toList.map g).sum = ∑ k ∈ Finset.range a.size, g (a[k]!, b[k]!) := by
  have hl : (a.zip b).toList = List.ofFn fun k : Fin a.size => (a[k.val]!, b[k.val]!) := by
    apply List.ext_getElem
    · simp [hab]
    · intro k h₁ h₂
      simp only [List.getElem_ofFn, Array.getElem_toList, Array.getElem_zip]
      rw [getElem!_pos a k (by simpa using h₂), getElem!_pos b k (by simp at h₂; omega)]
  rw [hl, List.map_ofFn, List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun k => g (a[k]!, b[k]!)) a.size

/-- An interpolation of the check returns 64 coefficients. -/
theorem size_of_interpolateCosetEvals {h : Fr} {evals : CosetEvals} {p : PolynomialCoeff}
    (hp : interpolateCosetEvals h evals = .ok p) : p.size = FIELD_ELEMENTS_PER_CELL ∧
      evals.size = FIELD_ELEMENTS_PER_CELL := by
  by_cases hsz : evals.size = FIELD_ELEMENTS_PER_CELL
  · unfold interpolateCosetEvals at hp
    rw [ite_eq_right (not_not.mpr hsz)] at hp
    cases hp
    exact ⟨by rw [size_shiftVals, size_fftField, size_bitReversalPermutation, hsz], hsz⟩
  · rw [interpolateCosetEvals_inputLengthMismatch hsz] at hp
    cases hp

/-- A constant polynomial evaluates to its constant. -/
theorem evalPolyAt_singleton (a x : Fr) : evalPolyAt #[a] x = a := by
  show Fr.zero + a * Fr.powNat x 0 = a
  rw [Bls.Fr.powNat_zero]
  exact (Fin.zero_add _).trans (Fin.mul_one _)

/-- Addition in `Fr` is associative, stated over `ZMod r` where the lemma of rings applies. -/
private theorem add_assoc_zmod (a b c : ZMod Fr.modulus) : a + b + c = a + (b + c) :=
  add_assoc a b c

/-- The value of an interpolation of the check at `x`, or zero if it fails. -/
def interpolationValue (x shift : Fr) (evals : CosetEvals) : Fr :=
  match interpolateCosetEvals shift evals with
  | .ok p => evalPolyAt p x
  | .error _ => 0

/-- The sum of the interpolations of the check, scaled by the powers of the challenge.

It keeps 64 coefficients, and its value at `x` is the sum of the scaled values. -/
theorem sumInterp_spec (x : Fr) :
    ∀ (L : List (Fr × CosetEvals × Fr)) (init acc : PolynomialCoeff),
      init.size = FIELD_ELEMENTS_PER_CELL →
      L.foldlM (fun sumInterp (e : Fr × CosetEvals × Fr) => do
          let interp ← interpolateCosetEvals e.1 e.2.1
          let scaled ← multiplyPolynomialcoeff #[e.2.2] interp
          pure (addPolynomialcoeff sumInterp scaled)) init = .ok acc →
      acc.size = FIELD_ELEMENTS_PER_CELL ∧
        (∀ e ∈ L, e.2.1.size = FIELD_ELEMENTS_PER_CELL) ∧
        evalPolyAt acc x =
          evalPolyAt init x + (L.map fun e => e.2.2 * interpolationValue x e.1 e.2.1).sum
  | [], init, acc, hinit, h => by
    cases h
    exact ⟨hinit, by simp, (Fin.add_zero _).symm⟩
  | e :: L, init, acc, hinit, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases hi : interpolateCosetEvals e.1 e.2.1 with
    | error err => rw [hi] at h; cases h
    | ok interp =>
    rw [hi] at h
    obtain ⟨hisz, hesz⟩ := size_of_interpolateCosetEvals hi
    obtain ⟨scaled, hs, hssz⟩ := multiplyPolynomialcoeff_ok_of_le (a := #[e.2.2]) (b := interp)
      (by simp [hisz]; decide)
    simp only [hs, pure, Except.pure] at h
    have hnext : (addPolynomialcoeff init scaled).size = FIELD_ELEMENTS_PER_CELL := by
      rw [size_addPolynomialcoeff, hinit, hssz, hisz]
      simp; decide
    obtain ⟨hacc, hall, heval⟩ := sumInterp_spec x L _ acc hnext h
    refine ⟨hacc, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hesz
      · exact hall e' he'
    · rw [heval, evalPolyAt_addPoly, evalPolyAt_mulPoly x hs, evalPolyAt_singleton,
        List.map_cons, List.sum_cons]
      simp only [interpolationValue, hi]
      exact add_assoc_zmod _ _ _

/-- Zero times an element of `Fr`, over `ZMod r` where the lemma of rings applies. -/
private theorem zero_mul_zmod (a : ZMod Fr.modulus) : 0 * a = 0 := zero_mul a

/-- Zero plus an element of `Fr`, over `ZMod r` where the lemma of rings applies. -/
private theorem zero_add_zmod (a : ZMod Fr.modulus) : 0 + a = a := zero_add a

/-- Entry `k` of two zipped arrays is the pair of their entries `k`. -/
theorem getElem!_zip' {α β : Type} [Inhabited α] [Inhabited β] {a : Array α} {b : Array β}
    {k : Nat} (ha : k < a.size) (hb : k < b.size) : (a.zip b)[k]! = (a[k]!, b[k]!) := by
  rw [getElem!_pos (a.zip b) k (by simp; omega), Array.getElem_zip, getElem!_pos a k ha,
    getElem!_pos b k hb]

/-- The sum of zero coefficients is zero. -/
theorem sum_replicate_zero_mul (m : Nat) (a : Nat → Fr) :
    ∑ i ∈ Finset.range m, (Array.replicate m Fr.zero)[i]! * a i = 0 :=
  Finset.sum_eq_zero fun j hj => by
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_replicate]
    exact zero_mul_zmod _

/-- The value of an array of coefficients, as a sum. -/
theorem evalPolyAt_eq_sum (p : PolynomialCoeff) (x : Fr) :
    evalPolyAt p x = ∑ j ∈ Finset.range p.size, p[j]! * x ^ j := by
  rw [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux_eq_sum]

/-- At a valid cell index, the interpolation of the check has the value of the cell's polynomial. -/
theorem interpolationValue_cellShift {cellIndex : Nat} (hci : cellIndex < CELLS_PER_EXT_BLOB)
    {evals : CosetEvals} (hevals : evals.size = FIELD_ELEMENTS_PER_CELL) (x : Fr) :
    interpolationValue x (cellShift cellIndex) evals =
      (cellInterpolant cellIndex evals).eval x := by
  obtain ⟨p, hp, -, -⟩ := interpolateCosetEvals_spec_of_ne_zero (cosetShift_ne_zero cellIndex hci)
    hevals
  have hp' : interpolateCosetEvals (cellShift cellIndex) evals = .ok p := hp
  rw [interpolationValue, hp']
  exact evalPolyAt_interpolateCosetEvals hci hevals hp' x

/-- The array of zero coefficients is the zero polynomial. -/
theorem evalPolyAt_replicate_zero (m : Nat) (x : Fr) :
    evalPolyAt (Array.replicate m Fr.zero) x = 0 := by
  rw [evalPolyAt_eq_sum, Array.size_replicate]
  exact sum_replicate_zero_mul m _

/-- The weights of the commitments: commitment `i` gets the sum of `r^k` over its cells `k`.

Then the sum of the weights times the commitments is the sum of `r^k c_{i_k}`. -/
theorem sum_weights {R : Type} [CommRing R] [Inhabited R] {numCommitments : Nat} (c : Nat → R) :
    ∀ (L : List (Nat × R)) (init : Array R), init.size = numCommitments →
      (∀ e ∈ L, e.1 < numCommitments) →
      let W := L.foldl (fun weights e => weights.modify e.1 (· + e.2)) init
      W.size = numCommitments ∧
        ∑ i ∈ Finset.range numCommitments, W[i]! * c i =
          ∑ i ∈ Finset.range numCommitments, init[i]! * c i + (L.map fun e => e.2 * c e.1).sum
  | [], init, hsize, _ => by simp [hsize]
  | (i, rPower) :: L, init, hsize, hL => by
    have hi : i < numCommitments := hL (i, rPower) List.mem_cons_self
    obtain ⟨hW, hsum⟩ := sum_weights c L (init.modify i (· + rPower)) (by simp [hsize])
      fun e he => hL e (List.mem_cons_of_mem _ he)
    refine ⟨hW, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at hsum ⊢
    rw [hsum, ← add_assoc]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hi),
      ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hi)]
    have hrest :
        ∑ j ∈ (Finset.range numCommitments).erase i, (init.modify i (· + rPower))[j]! * c j =
        ∑ j ∈ (Finset.range numCommitments).erase i, init[j]! * c j :=
      Finset.sum_congr rfl fun j hj => by
        have hj' := Finset.mem_erase.mp hj
        have hjn := Finset.mem_range.mp hj'.2
        rw [getElem!_pos _ j (by simp [hsize, hjn]), getElem!_pos init j (by omega),
          Array.getElem_modify, ite_eq_right (Ne.symm hj'.1)]
    rw [hrest, getElem!_pos _ i (by simp [hsize, hi]), getElem!_pos init i (by omega),
      Array.getElem_modify, ite_eq_left rfl]
    ring

/-! ## The batch check of cells -/

/-- One term of the identity of the check, over `ZMod r` where `ring` applies. -/
private theorem cell_term_identity (c i w t h x : ZMod Fr.modulus) :
    (c - i - w * (t - h)) * x = x * c - x * i + x * h * w - x * w * t := by
  ring

/-- The identity of the check, with the factor `-1` of the generator of `G2`. -/
private theorem cell_identity {ll rlc rli rlp t : ZMod Fr.modulus}
    (h : ll * t + (rlc + -rli + rlp) * -1 = 0) : rlc - rli + rlp - ll * t = 0 := by
  linear_combination -h

/-- **The batch check of cells as a scalar identity.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Let the commitments decode to points that represent `c i`.

Let the proofs decode to points that represent `w k`.

If the batch check accepts, its challenge is a root of the error polynomial of the cells. -/
theorem verifyCellKzgProofBatchImpl_root (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof} {commitmentsG1 proofsG1 : Array G1}
    {c w : Nat → Fr}
    (hCd : commitments.mapM uncompressG1 = .ok commitmentsG1)
    (hPd : proofs.mapM uncompressG1 = .ok proofsG1)
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ k < proofsG1.size, G1.Represents proofsG1[k]! (w k))
    (h : verifyCellKzgProofBatchImpl s commitments commitmentIndices cellIndices cosetsEvals
      proofs = .ok true) :
    (cellErrorPoly τ c w commitmentIndices cellIndices cosetsEvals).eval
      (computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices cellIndices
        cosetsEvals proofs) = 0 := by
  unfold verifyCellKzgProofBatchImpl at h
  by_cases h₁ : cellIndices.size ≠ commitmentIndices.size
  · simp [h₁, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₂ : cosetsEvals.size ≠ commitmentIndices.size
  · simp [h₁, h₂, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₃ : proofs.size ≠ commitmentIndices.size
  · simp [h₁, h₂, h₃, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₄ : commitmentIndices.any (· ≥ commitments.size) = true
  · simp [h₁, h₂, h₃, h₄, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [ne_eq, Decidable.not_not, Bool.not_eq_true] at h₁ h₂ h₃ h₄
  simp only [h₁, h₂, h₃, h₄, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true,
    bind, Except.bind, hPd, hCd] at h
  split at h
  · cases h
  -- Name the pieces of the check.
  set n := commitmentIndices.size with hn
  set r := computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices cellIndices
    cosetsEvals proofs
  set rp := computePowers r n
  have hrp : rp.size = n := size_computePowers r n
  obtain ⟨hPsz, -⟩ := array_mapM_ok hPd
  obtain ⟨hCsz, -⟩ := array_mapM_ok hCd
  rw [h₃] at hPsz
  have hidx : ∀ e ∈ (commitmentIndices.zip rp).toList, e.1 < commitments.size := by
    intro e he
    have he1 : e.1 ∈ commitmentIndices := (Array.of_mem_zip (Array.mem_toList_iff.mp he)).1
    have := Array.any_eq_false'.mp (show commitmentIndices.any (· ≥ commitments.size) = false
      from h₄) e.1 he1
    simpa using this
  -- The weights, and the sum of the weights times the commitments.
  obtain ⟨hWsz, hWsum⟩ := sum_weights c (commitmentIndices.zip rp).toList
    (Array.replicate commitments.size Fr.zero) (by simp) hidx
  set W := Array.foldl (fun weights (e : Nat × Fr) => weights.modify e.1 (· + e.2))
    (Array.replicate commitments.size Fr.zero) (commitmentIndices.zip rp) with hW
  have hWsz' : W.size = commitments.size := by rw [hW, ← Array.foldl_toList]; exact hWsz
  rw [g1LincombPoints_eq_msm (hPsz.trans hrp.symm),
    g1LincombPoints_eq_msm (hCsz.trans hWsz'.symm)] at h
  simp only [pure, Except.pure] at h
  -- The shifts of the cells.
  split at h
  · cases h
  rename_i shifts hshifts
  have hsh : shifts.size = n ∧ ∀ k < n,
      cellIndices[k]! < CELLS_PER_EXT_BLOB ∧ shifts[k]! = cellShift cellIndices[k]! := by
    obtain ⟨hsz, hk⟩ := array_mapM_ok hshifts
    refine ⟨hsz.trans h₁, fun k hk' => ?_⟩
    have hf := hk k (by omega)
    have h64 : FIELD_ELEMENTS_PER_CELL = 64 := rfl
    have h8192 : FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
    have h128 : CELLS_PER_EXT_BLOB = 128 := rfl
    by_cases hlt : FIELD_ELEMENTS_PER_CELL * cellIndices[k]! <
        (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB).size
    · simp only [hlt, ↓reduceDIte] at hf
      have hv := Except.ok.inj hf
      have hlt' := hlt
      rw [size_rootsOfUnityBrp, h64, h8192] at hlt'
      refine ⟨by rw [h128]; exact Nat.lt_of_mul_lt_mul_left (a := 64) (by omega), ?_⟩
      rw [← hv, cellShift]
      generalize rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB = D at hlt ⊢
      exact (getElem!_pos D _ hlt).symm
    · simp only [hlt, ↓reduceDIte] at hf
      cases hf
  -- The sum of the interpolations.
  split at h
  · cases h
  rename_i sumInterp hsum
  obtain ⟨hsisz, hevsz, hsieval⟩ := sumInterp_spec τ (shifts.zip (cosetsEvals.zip rp)).toList
    (Array.replicate FIELD_ELEMENTS_PER_CELL Fr.zero) sumInterp (by simp)
    (by rw [Array.foldlM_toList]; exact hsum)
  have hmono : (s.g1Monomial.toArray.extract 0 FIELD_ELEMENTS_PER_CELL).size = sumInterp.size := by
    rw [hsisz, Array.size_extract, Vector.size_toArray]
    rfl
  have hwrp : proofsG1.size =
      (Array.zipWith (fun rPower shift => rPower * shift ^ Fr.ofNat FIELD_ELEMENTS_PER_CELL)
        rp shifts).size := by
    rw [Array.size_zipWith, hrp, hsh.1, hPsz, Nat.min_self]
  rw [g1LincombPoints_eq_msm hmono, g1LincombPoints_eq_msm hwrp] at h
  simp only [pure, Except.pure] at h
  have hpair := Except.ok.inj h
  -- The points of the check, as combinations of the scalars.
  have hA := G1.represents_msm (scalars := rp) (hPsz.trans hrp.symm) hP
  have hCm := G1.represents_msm (scalars := W) (hCsz.trans hWsz'.symm) hC
  have hD := G1.represents_msm (a := fun j => τ ^ j) hmono fun j hj => by
    have hj' : j < FIELD_ELEMENTS_PER_CELL := by
      rw [Array.size_extract, Vector.size_toArray] at hj
      exact Nat.lt_of_lt_of_le hj (by decide)
    have hjb : j < FIELD_ELEMENTS_PER_BLOB := Nat.lt_of_lt_of_le hj' (by decide)
    have hm := hs.monomial_g1 ⟨j, hjb⟩
    rw [getElem!_pos _ j hj, Array.getElem_extract]
    simpa using hm
  have hE := G1.represents_msm (scalars := Array.zipWith
    (fun rPower shift => rPower * shift ^ Fr.ofNat FIELD_ELEMENTS_PER_CELL) rp shifts) hwrp hP
  have hs64 : G2.Represents (s.g2Monomial[FIELD_ELEMENTS_PER_CELL]'(by decide))
      (τ ^ FIELD_ELEMENTS_PER_CELL) := by
    have hm := hs.monomial_g2 ⟨FIELD_ELEMENTS_PER_CELL, by decide⟩
    simpa using hm
  have hs0 : G2.Represents (s.g2Monomial[0]'(by decide)) (τ ^ 0) := by
    have hm := hs.monomial_g2 ⟨0, by decide⟩
    simpa only [Fin.getElem_fin] using hm
  have hid := (laws.two_pairs hA hs64 ((hCm.add hD.neg).add hE) hs0.neg).mp hpair
  -- Each sum of the identity, as a sum over the cells.
  have hpow : ∀ k < n, rp[k]! = r ^ k := fun k hk => by
    rw [getElem!_pos rp k (by rw [hrp]; exact hk), getElem_computePowers, Bls.Fr.powNat_eq_pow]
  have hzsz : (cosetsEvals.zip rp).size = n := by simp [h₂, hrp]
  have hev : ∀ k < n, cosetsEvals[k]!.size = FIELD_ELEMENTS_PER_CELL := fun k hk => by
    have hmem :
        (shifts.zip (cosetsEvals.zip rp))[k]! ∈ (shifts.zip (cosetsEvals.zip rp)).toList := by
      rw [getElem!_pos _ k (by simp [hsh.1, hzsz]; exact hk)]
      exact Array.getElem_mem_toList _
    have := hevsz _ hmem
    rwa [getElem!_zip' (by rw [hsh.1]; exact hk) (by rw [hzsz]; exact hk),
      getElem!_zip' (by rw [h₂]; exact hk) (by rw [hrp]; exact hk)] at this
  have hcsum : ∑ j ∈ Finset.range commitmentsG1.size, W[j]! * c j =
      ∑ k ∈ Finset.range n, r ^ k * c commitmentIndices[k]! := by
    rw [hCsz, hW, ← Array.foldl_toList]
    refine hWsum.trans ((congrArg (· + _) (sum_replicate_zero_mul _ c)).trans
      ((zero_add_zmod _).trans ?_))
    refine (sum_zip_toList (M := Fr) commitmentIndices rp hrp.symm (fun e => e.2 * c e.1)).trans ?_
    exact Finset.sum_congr rfl fun k hk => by rw [hpow k (Finset.mem_range.mp hk)]
  have hdsum : ∑ j ∈ Finset.range (s.g1Monomial.toArray.extract 0 FIELD_ELEMENTS_PER_CELL).size,
      sumInterp[j]! * τ ^ j =
      ∑ k ∈ Finset.range n, r ^ k * (cellInterpolant cellIndices[k]! cosetsEvals[k]!).eval τ := by
    rw [hmono, ← evalPolyAt_eq_sum, hsieval]
    refine (congrArg (· + _) (evalPolyAt_replicate_zero _ τ)).trans ((zero_add_zmod _).trans ?_)
    refine (sum_zip_toList (M := Fr) shifts (cosetsEvals.zip rp) (hsh.1.trans hzsz.symm)
      (fun e => e.2.2 * interpolationValue τ e.1 e.2.1)).trans ?_
    rw [hsh.1]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [getElem!_zip' (by rw [h₂]; exact hk') (by rw [hrp]; exact hk'), (hsh.2 k hk').2,
      interpolationValue_cellShift (hsh.2 k hk').1 (hev k hk'), hpow k hk']
  have hesum : ∑ j ∈ Finset.range proofsG1.size,
      (Array.zipWith (fun rPower shift => rPower * shift ^ Fr.ofNat FIELD_ELEMENTS_PER_CELL)
        rp shifts)[j]! * w j =
      ∑ k ∈ Finset.range n, r ^ k * cellShift cellIndices[k]! ^ FIELD_ELEMENTS_PER_CELL * w k := by
    rw [hPsz]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [getElem!_pos _ k (by rw [Array.size_zipWith, hrp, hsh.1, Nat.min_self]; exact hk'),
      Array.getElem_zipWith, ← getElem!_pos rp k (by rw [hrp]; exact hk'),
      ← getElem!_pos shifts k (by rw [hsh.1]; exact hk'), hpow k hk', (hsh.2 k hk').2,
      Bls.Fr.hpow_ofNat_eq_pow _ (by decide)]
  have hasum : ∑ j ∈ Finset.range proofsG1.size, rp[j]! * w j =
      ∑ k ∈ Finset.range n, r ^ k * w k := by
    rw [hPsz]
    exact Finset.sum_congr rfl fun k hk => by rw [hpow k (Finset.mem_range.mp hk)]
  rw [hcsum, hdsum, hesum, hasum] at hid
  -- The value of the error polynomial at `r` is the left side of the identity of the check.
  rw [cellErrorPoly, eval_errorPoly, h₁]
  have key : ∑ k ∈ Finset.range n, cellError τ (c commitmentIndices[k]!) (w k)
        (cellShift cellIndices[k]!) (cellInterpolant cellIndices[k]! cosetsEvals[k]!) * r ^ k =
      ∑ k ∈ Finset.range n, (r ^ k * c commitmentIndices[k]! -
        r ^ k * (cellInterpolant cellIndices[k]! cosetsEvals[k]!).eval τ +
        r ^ k * cellShift cellIndices[k]! ^ FIELD_ELEMENTS_PER_CELL * w k -
        r ^ k * w k * τ ^ FIELD_ELEMENTS_PER_CELL) :=
    Finset.sum_congr rfl fun k _ => cell_term_identity _ _ _ _ _ _
  rw [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  exact cell_identity hid

/-- **An accepted batch of cells is valid, or its challenge is a root.**

Under the hypotheses of the scalar identity, every cell of an accepted batch is valid.

Otherwise the error polynomial of the cells is not zero, and the challenge is one of its roots. -/
theorem verifyCellKzgProofBatchImpl_valid_or_root (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof} {commitmentsG1 proofsG1 : Array G1}
    {c w : Nat → Fr}
    (hCd : commitments.mapM uncompressG1 = .ok commitmentsG1)
    (hPd : proofs.mapM uncompressG1 = .ok proofsG1)
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ k < proofsG1.size, G1.Represents proofsG1[k]! (w k))
    (h : verifyCellKzgProofBatchImpl s commitments commitmentIndices cellIndices cosetsEvals
      proofs = .ok true) :
    (∀ k < cellIndices.size,
        c commitmentIndices[k]! - (cellInterpolant cellIndices[k]! cosetsEvals[k]!).eval τ =
          w k * (τ ^ FIELD_ELEMENTS_PER_CELL -
            cellShift cellIndices[k]! ^ FIELD_ELEMENTS_PER_CELL)) ∨
      (cellErrorPoly τ c w commitmentIndices cellIndices cosetsEvals ≠ 0 ∧
        (cellErrorPoly τ c w commitmentIndices cellIndices cosetsEvals).eval
          (computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices cellIndices
            cosetsEvals proofs) = 0) := by
  by_cases hzero : cellErrorPoly τ c w commitmentIndices cellIndices cosetsEvals = 0
  · exact Or.inl ((cellErrorPoly_eq_zero_iff τ c w _ _ _).mp hzero)
  · exact Or.inr ⟨hzero, verifyCellKzgProofBatchImpl_root laws hs hCd hPd hC hP h⟩

/-! ## The challenge from a random oracle -/

/-- The inputs of the hash of a batch of cells. -/
structure CellBatch where
  commitments : Array KZGCommitment
  commitmentIndices : Array CommitmentIndex
  cellIndices : Array CellIndex
  cosetsEvals : Array CosetEvals
  proofs : Array KZGProof
deriving DecidableEq

/-- **The bound for batches of at most `n` cells.**

The hash of the batch check is a random oracle on its inputs.

In a batch `x`, let commitment `i` represent `c x i`, and proof `k` represent `w x k`.

The adversary makes `q` queries, then outputs a batch of at most `n` cells.

The event is that the challenge of that batch is a root of its error polynomial, which is not zero.

Its probability is at most `(q + 1) (n - 1) / r`. -/
theorem prEvent_cellErrorPoly_root_le (τ : Fr) (c w : CellBatch → Nat → Fr) {n : Nat}
    (adversary : OracleComp (CellBatch →ₒ Fr) CellBatch) {q : Nat}
    (hq : OracleComp.IsTotalQueryBound adversary q) :
    Pr{let p ← (simulateQ OracleSpec.randomOracle (batchRomExperiment adversary)).run' ∅}[
        p.1.cellIndices.size ≤ n ∧
        cellErrorPoly τ (c p.1) (w p.1) p.1.commitmentIndices p.1.cellIndices p.1.cosetsEvals ≠ 0 ∧
        (cellErrorPoly τ (c p.1) (w p.1) p.1.commitmentIndices p.1.cellIndices
          p.1.cosetsEvals).eval p.2 = 0] ≤
      (q + 1) * ((n - 1 : Nat) / Fr.modulus) :=
  prEvent_batchRomRoot_le
    (fun x => cellErrorPoly τ (c x) (w x) x.commitmentIndices x.cellIndices x.cosetsEvals)
    (fun x => x.cellIndices.size ≤ n)
    (fun _ hx => (natDegree_errorPoly_le _ _).trans (Nat.sub_le_sub_right hx 1)) adversary hq

end EthLib.Cryptography.Kzg
