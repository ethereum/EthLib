import EthLib.Cryptography.Proofs.Kzg.Polynomials
import EthLib.Cryptography.Proofs.Bls.FrZMod
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Coefficient interpolation correctness

Source: consensus-specs v1.6.0, Fulu polynomial-commitments-sampling,
`interpolate_polynomialcoeff`.
The theorem applies to every successful interpolation at pairwise distinct nodes.
-/
namespace EthLib.Cryptography.Kzg
open Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr

private theorem eval_singleton (y x : Fr) : evalPolyAt #[y] x = y := by
  simp [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux, Fr.powNat_zero,
    Fr.zero_def, Fr.one_def]
  exact mul_one y

private theorem linear_identity {R : Type*} [CommRing R] (w a x : R) :
    -(w*a*1) + w*(x*1) = w*(x-a) := by ring

private theorem eval_linear (w a x : Fr) :
    evalPolyAt #[(-w)*a,w] x = w * (x-a) := by
  simp [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux, Fr.powNat_zero,
    Fr.powNat_succ, Fr.zero_def, Fr.one_def]
  exact linear_identity w a x

private def interpolationStep (xs : Array Fr) (i : Nat)
    (s : PolynomialCoeff) (j : Nat) : Except KzgError PolynomialCoeff :=
  if j ≠ i then
    let w := (xs[i]! - xs[j]!).inverse
    multiplyPolynomialcoeff s #[(-w)*xs[j]!,w]
  else pure s

private def weight (xs : Array Fr) (i j : Nat) (x : Fr) : Fr :=
  if j ≠ i then (xs[i]! - xs[j]!).inverse * (x - xs[j]!) else 1

private theorem inner_eval (xs : Array Fr) (i : Nat) (js : List Nat)
    (s out : PolynomialCoeff) (x : Fr)
    (h : js.foldlM (interpolationStep xs i) s = .ok out) :
    evalPolyAt out x = evalPolyAt s x * (js.map (fun j => weight xs i j x)).prod := by
  induction js generalizing s with
  | nil => cases h; exact (mul_one _).symm
  | cons j js ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i next hn
      rw [ih next h, List.map_cons, List.prod_cons, ← mul_assoc]
      congr 1
      by_cases hji : j ≠ i
      · unfold interpolationStep at hn
        rw [ite_eq_left hji] at hn
        rw [evalPolyAt_mulPoly x hn, eval_linear]
        unfold weight
        rw [ite_eq_left hji]
      · simp only [interpolationStep, hji, ↓reduceIte, pure, Except.pure] at hn
        cases hn
        unfold weight
        rw [ite_eq_right hji]
        exact (mul_one _).symm

private theorem weight_self (xs : Array Fr) (i j : Nat)
    (hne : i ≠ j → xs[i]! ≠ xs[j]!) : weight xs i j xs[i]! = 1 := by
  unfold weight
  split
  · rename_i hji
    rw [Fr.inverse_eq_inv]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne (Ne.symm hji)))
  · rfl

private theorem weight_other (xs : Array Fr) (i k : Nat) (hik : i ≠ k) :
    weight xs i k xs[k]! = 0 := by
  simp [weight, Ne.symm hik, Fin.mul_zero]

private theorem inner_at_node (xs ys : Array Fr) (i k : Nat)
    (hi : i < xs.size) (hk : k < xs.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (out : PolynomialCoeff)
    (h : (List.range xs.size).foldlM (interpolationStep xs i) #[ys[i]!] = .ok out) :
    evalPolyAt out xs[k]! = if i = k then ys[k]! else 0 := by
  rw [inner_eval xs i _ _ out _ h, eval_singleton]
  by_cases hik : i = k
  · subst k
    rw [ite_eq_left rfl]
    have hp : ((List.range xs.size).map (fun j => weight xs i j xs[i]!)).prod = 1 := by
      apply List.prod_eq_one
      intro v hv
      rcases List.mem_map.mp hv with ⟨j,hj,rfl⟩
      exact weight_self xs i j (hdistinct i j hi (List.mem_range.mp hj))
    rw [hp]
    exact mul_one _
  · rw [ite_eq_right hik]
    have hp : ((List.range xs.size).map (fun j => weight xs i j xs[k]!)).prod = 0 := by
      apply List.prod_eq_zero
      exact List.mem_map.mpr ⟨k,List.mem_range.mpr hk,weight_other xs i k hik⟩
    -- The `0` is `Fin`'s, which core's `Fin.mul_zero` matches and Mathlib's `mul_zero` does not.
    rw [hp, Fin.mul_zero]

private def outerStep (xs ys : Array Fr) (r : PolynomialCoeff) (i : Nat) :
    Except KzgError PolynomialCoeff := do
  let summand ← (Array.range ys.size).foldlM (interpolationStep xs i) #[ys[i]!]
  return addPolynomialcoeff r summand

private theorem outer_step_eval (xs ys : Array Fr) (r out : PolynomialCoeff)
    (i k : Nat) (hi : i < xs.size) (hk : k < xs.size) (hsz : xs.size = ys.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (h : outerStep xs ys r i = .ok out) :
    evalPolyAt out xs[k]! = evalPolyAt r xs[k]! + (if i = k then ys[k]! else 0) := by
  unfold outerStep at h
  cases hs : (Array.range ys.size).foldlM (interpolationStep xs i) #[ys[i]!] with
  | error e =>
    simp only [hs, bind, Except.bind] at h
    cases h
  | ok s =>
    simp only [hs, bind, Except.bind, pure, Except.pure] at h
    cases h
    rw [evalPolyAt_addPoly]
    congr 1
    rw [← Array.foldlM_toList, Array.toList_range, ← hsz] at hs
    exact inner_at_node xs ys i k hi hk hdistinct s hs

private theorem outer_eval (xs ys : Array Fr) (k : Nat)
    (hk : k < xs.size) (hsz : xs.size = ys.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (is : List Nat) (r out : PolynomialCoeff)
    (hbounds : ∀ i ∈ is, i < xs.size)
    (h : is.foldlM (outerStep xs ys) r = .ok out) :
    evalPolyAt out xs[k]! = evalPolyAt r xs[k]! +
      (is.map (fun i => if i = k then ys[k]! else 0)).sum := by
  induction is generalizing r with
  | nil => cases h; exact (add_zero _).symm
  | cons i rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i next hn
      rw [ih next (fun j hj => hbounds j (List.mem_cons_of_mem _ hj)) h,
        outer_step_eval xs ys r next i k (hbounds i (List.mem_cons_self)) hk hsz hdistinct hn,
        List.map_cons, List.sum_cons]
      exact add_assoc _ _ _

private theorem sum_delta {R : Type*} [AddCommMonoid R] (is : List Nat) (k : Nat)
    (v : R) (hnd : is.Nodup) :
    (is.map (fun i => if i = k then v else 0)).sum = if k ∈ is then v else 0 := by
  induction is with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.sum_cons, ih hnd]
    by_cases hik : i = k
    · subst i
      simp [hnot]
    · simp [hik, Ne.symm hik]

/-- Successful coefficient interpolation agrees with every supplied sample
when the nodes are pairwise distinct.
Size-limit failures are excluded by the success hypothesis, not silently ignored. -/
theorem interpolatePolynomialcoeff_eval_at_of_distinct
    {xs ys out : Array Fr} (hsz : xs.size = ys.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (h : interpolatePolynomialcoeff xs ys = .ok out)
    {k : Nat} (hk : k < xs.size) :
    evalPolyAt out xs[k]! = ys[k]! := by
  have hfold : (List.range xs.size).foldlM (outerStep xs ys) #[Fr.zero] = .ok out := by
    unfold interpolatePolynomialcoeff at h
    rw [ite_eq_right (by omega)] at h
    change (Array.range xs.size).foldlM (outerStep xs ys) #[Fr.zero] = .ok out at h
    simpa only [← Array.foldlM_toList, Array.toList_range] using h
  rw [outer_eval xs ys k hk hsz hdistinct (List.range xs.size) #[Fr.zero] out
    (fun i hi => List.mem_range.mp hi) hfold, eval_singleton]
  -- The `0` in this sum is `Fin`'s, not the monoid's, so `sum_delta` goes in by `erw`.
  erw [sum_delta _ k _ List.nodup_range]
  rw [ite_eq_left (List.mem_range.mpr hk)]
  exact Fin.zero_add _

private theorem except_bind_eq_ok_interp {ε α β : Type _} {x : Except ε α}
    {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [Bind.bind, Except.bind])
  | ok a => exact ⟨a, rfl, by simpa [Bind.bind, Except.bind] using h⟩

private theorem inner_range_size_and_bound (xs : Array Fr) (i : Nat)
    (init : PolynomialCoeff) (hinit : init.size = 1) :
    ∀ (k : Nat) (out : PolynomialCoeff),
      (List.range k).foldlM (interpolationStep xs i) init = .ok out →
        out.size = (if i < k then k else k + 1) ∧
          ∀ j < k, j ≠ i →
            (if i < j then j else j + 1) + 2 ≤ FIELD_ELEMENTS_PER_EXT_BLOB := by
  intro k
  induction k with
  | zero =>
    intro out h
    cases h
    exact ⟨by simp [hinit], fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro out h
    rw [List.range_succ, List.foldlM_append] at h
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at h
    obtain ⟨q, hq, hstep⟩ := except_bind_eq_ok_interp h
    obtain ⟨hq_sz, hq_bd⟩ := ih q hq
    by_cases hki : k ≠ i
    · unfold interpolationStep at hstep
      rw [ite_eq_left hki] at hstep
      have hle := multiplyPolynomialcoeff_le_of_ok hstep
      have hsz := size_multiplyPolynomialcoeff hstep
      have hq_ne : q.isEmpty = false := by
        rw [Bool.eq_false_iff, ne_eq, Array.isEmpty_iff_size_eq_zero, hq_sz]
        split <;> omega
      rw [ite_eq_right (by simp [hq_ne])] at hsz
      have hbin : (#[-((xs[i]! - xs[k]!).inverse) * xs[k]!, (xs[i]! - xs[k]!).inverse] :
          PolynomialCoeff).size = 2 := rfl
      refine ⟨?_, fun j hj hji => ?_⟩
      · rw [hsz, hq_sz, hbin]
        split <;> split <;> omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · exact hq_bd j hlt hji
        · simpa [hq_sz, hbin] using hle
    · have hkeq : k = i := Decidable.of_not_not hki
      subst hkeq
      simp only [interpolationStep, ne_eq, not_true_eq_false, ↓reduceIte,
        pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      refine ⟨?_, fun j hj hji => ?_⟩
      · rw [hq_sz]
        split <;> split <;> omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · exact hq_bd j hlt hji
        · exact absurd rfl hji

private theorem inner_range_ok (xs : Array Fr) (i : Nat) (hi : i < xs.size)
    (hbound : xs.size < FIELD_ELEMENTS_PER_EXT_BLOB)
    (init : PolynomialCoeff) (hinit : init.size = 1) :
    ∀ k ≤ xs.size,
      ∃ out, (List.range k).foldlM (interpolationStep xs i) init = .ok out ∧
        out.size = (if i < k then k else k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨init, rfl, by simp [hinit]⟩
  | succ k ih =>
    intro hk
    obtain ⟨q, hq, hq_sz⟩ := ih (by omega)
    rw [List.range_succ, List.foldlM_append]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    by_cases hki : k ≠ i
    · have hle : q.size +
          (#[-((xs[i]! - xs[k]!).inverse) * xs[k]!, (xs[i]! - xs[k]!).inverse] :
            PolynomialCoeff).size ≤ FIELD_ELEMENTS_PER_EXT_BLOB := by
        have hbin : (#[-((xs[i]! - xs[k]!).inverse) * xs[k]!, (xs[i]! - xs[k]!).inverse] :
            PolynomialCoeff).size = 2 := rfl
        rw [hq_sz, hbin]
        split <;> omega
      obtain ⟨out, hout, hout_sz⟩ := multiplyPolynomialcoeff_ok_of_le hle
      have hq_ne : q.isEmpty = false := by
        rw [Bool.eq_false_iff, ne_eq, Array.isEmpty_iff_size_eq_zero, hq_sz]
        split <;> omega
      rw [ite_eq_right (by simp [hq_ne])] at hout_sz
      refine ⟨out, ?_, ?_⟩
      · simp only [Bind.bind, Except.bind, hq, interpolationStep, ite_eq_left hki, hout]
      · have hbin : (#[-((xs[i]! - xs[k]!).inverse) * xs[k]!, (xs[i]! - xs[k]!).inverse] :
            PolynomialCoeff).size = 2 := rfl
        rw [hout_sz, hq_sz, hbin]
        split <;> split <;> omega
    · have hkeq : k = i := Decidable.of_not_not hki
      subst hkeq
      refine ⟨q, ?_, ?_⟩
      · simp only [Bind.bind, Except.bind, hq, interpolationStep, ne_eq,
          not_true_eq_false, ↓reduceIte, pure, Except.pure]
      · rw [hq_sz]
        split <;> split <;> omega

private theorem outer_range_size_and_bound (xs ys : Array Fr)
    (hsz : xs.size = ys.size) :
    ∀ (k : Nat), k ≤ xs.size →
      ∀ (out : PolynomialCoeff),
        (List.range k).foldlM (outerStep xs ys) #[Fr.zero] = .ok out →
        out.size = (if k = 0 then 1 else xs.size) ∧
          (0 < k → xs.size < Constants.FIELD_ELEMENTS_PER_EXT_BLOB) := by
  intro k
  induction k with
  | zero =>
    intro _ out h
    cases h
    exact ⟨rfl, fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩
  | succ k ih =>
    intro hk out h
    rw [List.range_succ, List.foldlM_append] at h
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at h
    obtain ⟨q, hq, hstep⟩ := except_bind_eq_ok_interp h
    obtain ⟨hq_sz, _⟩ := ih (by omega) q hq
    unfold outerStep at hstep
    obtain ⟨summand, hs, hadd⟩ := except_bind_eq_ok_interp hstep
    simp only [pure, Except.pure, Except.ok.injEq] at hadd
    subst hadd
    rw [← Array.foldlM_toList, Array.toList_range, ← hsz] at hs
    obtain ⟨hs_sz, hs_bd⟩ := inner_range_size_and_bound xs k #[ys[k]!] rfl xs.size summand hs
    rw [ite_eq_left (by omega)] at hs_sz
    refine ⟨?_, fun _ => ?_⟩
    · rw [size_addPolynomialcoeff, hq_sz, hs_sz]
      by_cases hk0 : k = 0
      · simp [hk0]; omega
      · simp [hk0]
    · by_cases hgt1 : 1 < xs.size
      · by_cases hk0 : k = 0
        · subst hk0
          have hbd := hs_bd (xs.size - 1) (by omega) (by omega)
          rw [ite_eq_left (by omega)] at hbd
          omega
        · have hbd := hs_bd 0 (by omega) (by omega)
          rw [ite_eq_right (by omega)] at hbd
          have : Constants.FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
          omega
      · have : Constants.FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
        omega

private theorem outer_range_ok (xs ys : Array Fr)
    (hsz : xs.size = ys.size)
    (hbound : xs.size < Constants.FIELD_ELEMENTS_PER_EXT_BLOB) :
    ∀ (k : Nat), k ≤ xs.size →
      ∃ out, (List.range k).foldlM (outerStep xs ys) #[Fr.zero] = .ok out ∧
        out.size = (if k = 0 then 1 else xs.size) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨#[Fr.zero], rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨q, hq, hq_sz⟩ := ih (by omega)
    obtain ⟨summand, hs, hs_sz⟩ :=
      inner_range_ok xs k (by omega) hbound #[ys[k]!] rfl xs.size (Nat.le_refl _)
    rw [ite_eq_left (by omega)] at hs_sz
    have hs_arr : (Array.range ys.size).foldlM (interpolationStep xs k) #[ys[k]!] = .ok summand := by
      rw [← Array.foldlM_toList, Array.toList_range, ← hsz]
      exact hs
    have hstep : outerStep xs ys q k = .ok (addPolynomialcoeff q summand) := by
      unfold outerStep
      simp only [Bind.bind, Except.bind, hs_arr, pure, Except.pure]
    refine ⟨addPolynomialcoeff q summand, ?_, ?_⟩
    · rw [List.range_succ, List.foldlM_append]
      simp only [List.foldlM_cons, List.foldlM_nil, Bind.bind,
        Except.bind, hq, hstep, pure, Except.pure]
    · rw [size_addPolynomialcoeff, hq_sz, hs_sz]
      by_cases hk0 : k = 0
      · simp [hk0]; omega
      · simp [hk0]

/-- Any successful `interpolatePolynomialcoeff xs ys = .ok out` satisfies
`xs.size = ys.size`, `xs.size < FIELD_ELEMENTS_PER_EXT_BLOB`, and
`out.size = max xs.size 1`. -/
theorem size_interpolatePolynomialcoeff {xs ys out : Array Fr}
    (h : interpolatePolynomialcoeff xs ys = .ok out) :
    xs.size = ys.size ∧ xs.size < Constants.FIELD_ELEMENTS_PER_EXT_BLOB ∧
      out.size = max xs.size 1 := by
  unfold interpolatePolynomialcoeff at h
  by_cases hne : xs.size ≠ ys.size
  · rw [ite_eq_left hne] at h
    cases h
  · have hsz : xs.size = ys.size := Decidable.of_not_not hne
    rw [ite_eq_right hne] at h
    change (Array.range xs.size).foldlM (outerStep xs ys) #[Fr.zero] = .ok out at h
    rw [← Array.foldlM_toList, Array.toList_range] at h
    obtain ⟨hout_sz, hbd⟩ := outer_range_size_and_bound xs ys hsz xs.size (Nat.le_refl _) out h
    refine ⟨hsz, ?_, ?_⟩
    · by_cases hx0 : xs.size = 0
      · rw [hx0]; decide
      · exact hbd (Nat.pos_of_ne_zero hx0)
    · rw [hout_sz]
      split <;> omega

/-- `interpolatePolynomialcoeff xs ys` succeeds whenever `xs.size = ys.size` and
`xs.size < FIELD_ELEMENTS_PER_EXT_BLOB`, returning a coefficient array of size
`max xs.size 1`. -/
theorem interpolatePolynomialcoeff_ok_of_lt {xs ys : Array Fr}
    (hsz : xs.size = ys.size)
    (hbound : xs.size < Constants.FIELD_ELEMENTS_PER_EXT_BLOB) :
    ∃ out, interpolatePolynomialcoeff xs ys = .ok out ∧
      out.size = max xs.size 1 := by
  obtain ⟨out, hout, hout_sz⟩ := outer_range_ok xs ys hsz hbound xs.size (Nat.le_refl _)
  refine ⟨out, ?_, ?_⟩
  · unfold interpolatePolynomialcoeff
    rw [ite_eq_right (by omega)]
    change (Array.range xs.size).foldlM (outerStep xs ys) #[Fr.zero] = .ok out
    rw [← Array.foldlM_toList, Array.toList_range]
    exact hout
  · rw [hout_sz]
    split <;> omega

/-- `interpolatePolynomialcoeff xs ys` succeeds iff `xs.size = ys.size` and
`xs.size < FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem interpolatePolynomialcoeff_ok_iff {xs ys : Array Fr} :
    (∃ out, interpolatePolynomialcoeff xs ys = .ok out) ↔
      xs.size = ys.size ∧ xs.size < Constants.FIELD_ELEMENTS_PER_EXT_BLOB :=
  ⟨fun ⟨_, hout⟩ =>
    let ⟨hsz, hbd, _⟩ := size_interpolatePolynomialcoeff hout
    ⟨hsz, hbd⟩,
   fun ⟨hsz, hbd⟩ =>
    let ⟨out, hout, _⟩ := interpolatePolynomialcoeff_ok_of_lt hsz hbd
    ⟨out, hout⟩⟩

/-- Unconditional specification of `interpolatePolynomialcoeff`: for equal-sized
arrays below `FIELD_ELEMENTS_PER_EXT_BLOB` with pairwise distinct nodes `xs`,
interpolation succeeds with size `max xs.size 1` and evaluates to `ys[k]!` at
every node `xs[k]!`. -/
theorem interpolatePolynomialcoeff_spec_of_distinct {xs ys : Array Fr}
    (hsz : xs.size = ys.size)
    (hbound : xs.size < Constants.FIELD_ELEMENTS_PER_EXT_BLOB)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!) :
    ∃ out, interpolatePolynomialcoeff xs ys = .ok out ∧
      out.size = max xs.size 1 ∧
      ∀ k < xs.size, evalPolyAt out xs[k]! = ys[k]! := by
  obtain ⟨out, hout, hout_sz⟩ := interpolatePolynomialcoeff_ok_of_lt hsz hbound
  exact ⟨out, hout, hout_sz,
    fun k hk => interpolatePolynomialcoeff_eval_at_of_distinct hsz hdistinct hout hk⟩

end EthLib.Cryptography.Kzg
