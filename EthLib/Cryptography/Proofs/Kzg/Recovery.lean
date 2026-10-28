import EthLib.Cryptography.Kzg.Recovery
import EthLib.Cryptography.Proofs.Kzg.Fft
import EthLib.Cryptography.Proofs.Kzg.Polynomials

/-!
# Proofs: `Recovery`

Shape properties of the recovery pipeline (the recovered polynomial has
exactly `FIELD_ELEMENTS_PER_BLOB` coefficients) and the validation
surface of `recoverCellsAndKzgProofs`: each malformed input is rejected
with exactly the documented error.
-/

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants

/-- A `foldl` whose step preserves array size preserves array size. -/
private theorem size_foldl_of_size_step {α β : Type _} (xs : Array β)
    (init : Array α) (f : Array α → β → Array α)
    (hf : ∀ acc b, (f acc b).size = acc.size) :
    (xs.foldl f init).size = init.size :=
  Array.foldl_induction (motive := fun _ acc => acc.size = init.size) rfl
    (fun i acc h => (hf acc xs[i]).trans h)

/-- Split a successful `Except` bind into its two successful stages.
Cases on the opaque first stage, so nothing forces evaluation of the
(expensive) underlying computation. -/
private theorem except_bind_eq_ok {ε α β : Type _} {x : Except ε α}
    {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [Bind.bind, Except.bind])
  | ok a => exact ⟨a, rfl, by simpa [Bind.bind, Except.bind] using h⟩

/-- `constructVanishingPolynomial` rejects inputs where all cells are missing. -/
theorem constructVanishingPolynomial_tooManyMissingCells
    {missingCellIndices : Array CellIndex}
    (h : missingCellIndices.size ≥ CELLS_PER_EXT_BLOB) :
    constructVanishingPolynomial missingCellIndices =
      .error .tooManyMissingCells := by
  simp [constructVanishingPolynomial, h, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- The extended vanishing polynomial spans the full extended domain. -/
theorem size_constructVanishingPolynomial
    {missingCellIndices : Array CellIndex} {p : PolynomialCoeff}
    (h : constructVanishingPolynomial missingCellIndices = .ok p) :
    p.size = FIELD_ELEMENTS_PER_EXT_BLOB := by
  simp only [constructVanishingPolynomial,
    bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals cases h
  rw [size_foldl_of_size_step]
  · simp
  · exact fun acc b => Array.size_setIfInBounds

private theorem getElem!_set!_self (arr : Array Fr) (i : Nat) (v : Fr)
    (hi : i < arr.size) : (arr.set! i v)[i]! = v := by
  show (arr.setIfInBounds i v)[i]! = v
  rw [getElem!_pos (arr.setIfInBounds i v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      Array.getElem_setIfInBounds_self]

private theorem getElem!_set!_ne (arr : Array Fr) {i j : Nat} (v : Fr)
    (hij : i ≠ j) (hj : j < arr.size) : (arr.set! i v)[j]! = arr[j]! := by
  show (arr.setIfInBounds i v)[j]! = arr[j]!
  rw [getElem!_pos (arr.setIfInBounds i v) j
        (by rw [Array.size_setIfInBounds]; exact hj),
      getElem!_pos arr j hj,
      Array.getElem_setIfInBounds_ne hj hij]

private theorem size_set! (arr : Array Fr) (i : Nat) (v : Fr) :
    (arr.set! i v).size = arr.size :=
  Array.size_setIfInBounds

private theorem foldl_vanishing_extend_size_and_getElem!
    (shortZeroPoly : PolynomialCoeff) (init : PolynomialCoeff)
    (hinit : init.size = FIELD_ELEMENTS_PER_EXT_BLOB)
    (k : Nat) (hk : k ≤ CELLS_PER_EXT_BLOB) :
    let res := (List.range k).foldl
      (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
      init
    res.size = FIELD_ELEMENTS_PER_EXT_BLOB ∧
      ∀ j < k, res[j * FIELD_ELEMENTS_PER_CELL]! = shortZeroPoly[j]! := by
  induction k with
  | zero =>
    refine ⟨hinit, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    obtain ⟨hsz, hget⟩ := ih (by omega)
    have hstep_sz :
        (((List.range (k + 1)).foldl
          (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
          init)).size = FIELD_ELEMENTS_PER_EXT_BLOB := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          size_set!, hsz]
    refine ⟨hstep_sz, fun j hj => ?_⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hcell_pos : FIELD_ELEMENTS_PER_CELL = 64 := rfl
    have hext_eq : FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
    have hcells_eq : CELLS_PER_EXT_BLOB = 128 := rfl
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hlt
    · apply getElem!_set!_self
      rw [hsz, hext_eq, hcell_pos]
      omega
    · rw [getElem!_set!_ne _ _ (by rw [hcell_pos]; omega) (by rw [hsz, hext_eq, hcell_pos]; omega)]
      exact hget j hlt

/-- On success, `constructVanishingPolynomial missingCellIndices` has fewer than
`CELLS_PER_EXT_BLOB` missing cells and has coefficient `Fr.one` (hence non-zero)
at degree `missingCellIndices.size * FIELD_ELEMENTS_PER_CELL`. -/
theorem leadingCoeff_constructVanishingPolynomial
    {missingCellIndices : Array CellIndex} {p : PolynomialCoeff}
    (h : constructVanishingPolynomial missingCellIndices = .ok p) :
    missingCellIndices.size < CELLS_PER_EXT_BLOB ∧
      p[missingCellIndices.size * FIELD_ELEMENTS_PER_CELL]! = Fr.one ∧
      p[missingCellIndices.size * FIELD_ELEMENTS_PER_CELL]!.isZero = false := by
  simp only [constructVanishingPolynomial,
    bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  · rename_i hlt
    have hlt' : missingCellIndices.size < CELLS_PER_EXT_BLOB :=
      Nat.lt_of_not_le hlt
    split at h
    · cases h
    · rename_i shortZeroPoly hshort
      injection h with hp
      subst hp
      obtain ⟨hshort_sz, hshort_lead⟩ :=
        size_and_leadingCoeff_vanishingPolynomialcoeff hshort
      simp only [Array.size_map] at hshort_sz hshort_lead
      have hfold :
          (Array.range shortZeroPoly.size).foldl
            (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
            (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) =
          (List.range shortZeroPoly.size).foldl
            (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
            (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) := by
        rw [← Array.foldl_toList, Array.toList_range]
      rw [hfold]
      obtain ⟨_, hget⟩ := foldl_vanishing_extend_size_and_getElem!
        shortZeroPoly (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
        (by simp) shortZeroPoly.size (by omega)
      have hval := hget missingCellIndices.size (by omega)
      rw [hshort_lead] at hval
      exact ⟨hlt', hval, by rw [hval]; rfl⟩

/-- `constructVanishingPolynomial` succeeds whenever fewer than
`CELLS_PER_EXT_BLOB` cell indices are missing, returning a polynomial of size
`FIELD_ELEMENTS_PER_EXT_BLOB` with coefficient `Fr.one` at degree
`missingCellIndices.size * FIELD_ELEMENTS_PER_CELL`. -/
theorem constructVanishingPolynomial_ok_of_lt
    {missingCellIndices : Array CellIndex}
    (h : missingCellIndices.size < CELLS_PER_EXT_BLOB) :
    ∃ p, constructVanishingPolynomial missingCellIndices = .ok p ∧
      p.size = FIELD_ELEMENTS_PER_EXT_BLOB ∧
      p[missingCellIndices.size * FIELD_ELEMENTS_PER_CELL]! = Fr.one := by
  let rouReduced := computeRootsOfUnity CELLS_PER_EXT_BLOB
  let xs : Array Fr := missingCellIndices.map fun mci =>
    rouReduced[BitReversal.reverseBits mci CELLS_PER_EXT_BLOB]!
  have hxs_lt : xs.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB := by
    have h1 : CELLS_PER_EXT_BLOB = 128 := rfl
    have h2 : FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
    simp only [xs, Array.size_map]
    omega
  obtain ⟨shortZeroPoly, hshort, _, _⟩ := vanishingPolynomialcoeff_ok_of_lt hxs_lt
  let p := (Array.range shortZeroPoly.size).foldl
    (init := Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    fun zeroPoly i =>
      zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!
  have hp : constructVanishingPolynomial missingCellIndices = .ok p := by
    unfold constructVanishingPolynomial
    rw [ite_eq_right (by omega)]
    simp only [Bind.bind, Except.bind, xs, rouReduced, hshort, pure, Except.pure, p]
  exact ⟨p, hp, size_constructVanishingPolynomial hp,
    (leadingCoeff_constructVanishingPolynomial hp).2.1⟩

/-- `constructVanishingPolynomial missingCellIndices` succeeds iff
`missingCellIndices.size < CELLS_PER_EXT_BLOB`. -/
theorem constructVanishingPolynomial_ok_iff
    {missingCellIndices : Array CellIndex} :
    (∃ p, constructVanishingPolynomial missingCellIndices = .ok p) ↔
      missingCellIndices.size < CELLS_PER_EXT_BLOB :=
  ⟨fun ⟨_, hp⟩ => (leadingCoeff_constructVanishingPolynomial hp).1,
   fun h => let ⟨p, hp, _, _⟩ := constructVanishingPolynomial_ok_of_lt h; ⟨p, hp⟩⟩

private theorem foldl_vanishing_extend_getElem!_all
    (shortZeroPoly : PolynomialCoeff)
    (k : Nat) (hk : k ≤ CELLS_PER_EXT_BLOB) (m : Nat) :
    ((List.range k).foldl
      (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
      (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero))[m]! =
      if m % FIELD_ELEMENTS_PER_CELL = 0 ∧ m / FIELD_ELEMENTS_PER_CELL < k then
        shortZeroPoly[m / FIELD_ELEMENTS_PER_CELL]!
      else
        Fr.zero := by
  have hcell : FIELD_ELEMENTS_PER_CELL = 64 := rfl
  have hext : FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
  have hcells : CELLS_PER_EXT_BLOB = 128 := rfl
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, and_false, ↓reduceIte]
    by_cases hm : m < FIELD_ELEMENTS_PER_EXT_BLOB
    · rw [getElem!_pos _ m (by simp [hm]), Array.getElem_replicate]
    · rw [getElem!_neg _ m (by simp [hm])]; rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let prev := (List.range k).foldl
      (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
      (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    have hprev_sz : prev.size = FIELD_ELEMENTS_PER_EXT_BLOB :=
      (foldl_vanishing_extend_size_and_getElem! shortZeroPoly
        (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) (by simp) k (by omega)).1
    by_cases hmk : m = k * FIELD_ELEMENTS_PER_CELL
    · subst hmk
      rw [getElem!_set!_self prev (k * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[k]!
        (by rw [hprev_sz, hext, hcell]; omega)]
      have hmod : (k * FIELD_ELEMENTS_PER_CELL) % FIELD_ELEMENTS_PER_CELL = 0 :=
        Nat.mul_mod_left k FIELD_ELEMENTS_PER_CELL
      have hdiv : (k * FIELD_ELEMENTS_PER_CELL) / FIELD_ELEMENTS_PER_CELL = k :=
        Nat.mul_div_cancel k (by rw [hcell]; decide)
      rw [ite_eq_left ⟨hmod, by omega⟩, hdiv]
    · by_cases hm : m < FIELD_ELEMENTS_PER_EXT_BLOB
      · rw [getElem!_set!_ne prev shortZeroPoly[k]! (Ne.symm hmk) (by rw [hprev_sz]; exact hm),
            ih (by omega)]
        have heq_cond : (m % FIELD_ELEMENTS_PER_CELL = 0 ∧ m / FIELD_ELEMENTS_PER_CELL < k) ↔
            (m % FIELD_ELEMENTS_PER_CELL = 0 ∧ m / FIELD_ELEMENTS_PER_CELL < k + 1) := by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            rw [hcell] at h1 h2 hmk ⊢
            omega
        by_cases hc : m % FIELD_ELEMENTS_PER_CELL = 0 ∧ m / FIELD_ELEMENTS_PER_CELL < k
        · rw [ite_eq_left hc, ite_eq_left (heq_cond.mp hc)]
        · rw [ite_eq_right hc, ite_eq_right (fun hc' => hc (heq_cond.mpr hc'))]
      · rw [getElem!_neg _ m (by rw [size_set!, hprev_sz]; exact hm)]
        have hnot : ¬ (m % FIELD_ELEMENTS_PER_CELL = 0 ∧ m / FIELD_ELEMENTS_PER_CELL < k + 1) := by
          rintro ⟨_, hlt⟩
          rw [hcell] at hlt
          rw [hext] at hm
          omega
        rw [ite_eq_right hnot]
        rfl

private theorem fr_powNat_mul (x : Fr) (c i : Nat) :
    Fr.powNat x (i * c) = Fr.powNat (Fr.powNat x c) i := by
  induction i with
  | zero =>
    simp [Fr.powNat_zero]
  | succ i ih =>
    have hadd : (i + 1) * c = i * c + c := Nat.succ_mul i c
    rw [hadd, Fr.powNat_succ]
    have hpow_add : ∀ a b : Nat, Fr.powNat x (a + b) = Fr.powNat x a * Fr.powNat x b := by
      intro a b
      induction b with
      | zero => rw [Nat.add_zero, Fr.powNat_zero]; exact (Fin.mul_one _).symm
      | succ b ihb =>
        rw [Nat.add_succ, Fr.powNat_succ, Fr.powNat_succ, ihb,
            ← Fr.mul_assoc, Fr.mul_comm x (Fr.powNat x a), Fr.mul_assoc]
    rw [hpow_add, ih, Fr.mul_comm]

private theorem evalCoeffPolyAux_extend_block
    (shortZeroPoly : PolynomialCoeff) (k : Nat) (hk : k ≤ CELLS_PER_EXT_BLOB)
    (x : Fr) (i : Nat) (hi : i < k) :
    let p := (List.range k).foldl
      (fun zeroPoly j => zeroPoly.set! (j * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[j]!)
      (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    ∀ r : Nat, 1 ≤ r → r ≤ FIELD_ELEMENTS_PER_CELL →
      evalCoeffPolyAux p x (i * FIELD_ELEMENTS_PER_CELL + r) =
        evalCoeffPolyAux p x (i * FIELD_ELEMENTS_PER_CELL) +
          shortZeroPoly[i]! * Fr.powNat (Fr.powNat x FIELD_ELEMENTS_PER_CELL) i := by
  intro p r hr1 hr2
  have hcell : FIELD_ELEMENTS_PER_CELL = 64 := rfl
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by omega⟩
  induction d with
  | zero =>
    simp only [evalCoeffPolyAux]
    congr 1
    have hget := foldl_vanishing_extend_getElem!_all shortZeroPoly k hk (i * FIELD_ELEMENTS_PER_CELL)
    have hmod : (i * FIELD_ELEMENTS_PER_CELL) % FIELD_ELEMENTS_PER_CELL = 0 :=
      Nat.mul_mod_left i FIELD_ELEMENTS_PER_CELL
    have hdiv : (i * FIELD_ELEMENTS_PER_CELL) / FIELD_ELEMENTS_PER_CELL = i :=
      Nat.mul_div_cancel i (by rw [hcell]; decide)
    rw [ite_eq_left ⟨hmod, by omega⟩, hdiv] at hget
    rw [hget, fr_powNat_mul]
  | succ d ih =>
    have hstep : i * FIELD_ELEMENTS_PER_CELL + (d + 1 + 1) =
        (i * FIELD_ELEMENTS_PER_CELL + (d + 1)) + 1 := by omega
    rw [hstep, evalCoeffPolyAux, ih (by omega) (by omega)]
    have hget := foldl_vanishing_extend_getElem!_all shortZeroPoly k hk
      (i * FIELD_ELEMENTS_PER_CELL + (d + 1))
    have hmod : (i * FIELD_ELEMENTS_PER_CELL + (d + 1)) % FIELD_ELEMENTS_PER_CELL ≠ 0 := by
      rw [hcell] at hr2 ⊢
      omega
    rw [ite_eq_right (fun h => hmod h.1)] at hget
    have h0mul (y : Fr) : Fr.zero * y = Fr.zero := Fin.zero_mul y
    have hadd0 (y : Fr) : y + Fr.zero = y := Fin.add_zero y
    change evalCoeffPolyAux p x (i * FIELD_ELEMENTS_PER_CELL) +
        shortZeroPoly[i]! * (x.powNat FIELD_ELEMENTS_PER_CELL).powNat i +
        p[i * FIELD_ELEMENTS_PER_CELL + (d + 1)]! * x.powNat (i * FIELD_ELEMENTS_PER_CELL + (d + 1)) = _
    rw [hget, h0mul, hadd0]

private theorem evalCoeffPolyAux_extend_prefix
    (shortZeroPoly : PolynomialCoeff) (k : Nat) (hk : k ≤ CELLS_PER_EXT_BLOB)
    (x : Fr) :
    let p := (List.range k).foldl
      (fun zeroPoly j => zeroPoly.set! (j * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[j]!)
      (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    ∀ i ≤ k,
      evalCoeffPolyAux p x (i * FIELD_ELEMENTS_PER_CELL) =
        evalCoeffPolyAux shortZeroPoly (Fr.powNat x FIELD_ELEMENTS_PER_CELL) i := by
  intro p i
  induction i with
  | zero => simp [evalCoeffPolyAux]
  | succ i ih =>
    intro hi
    have hmul : (i + 1) * FIELD_ELEMENTS_PER_CELL =
        i * FIELD_ELEMENTS_PER_CELL + FIELD_ELEMENTS_PER_CELL := Nat.succ_mul i _
    rw [hmul, evalCoeffPolyAux_extend_block shortZeroPoly k hk x i (by omega)
        FIELD_ELEMENTS_PER_CELL (by decide) (Nat.le_refl _),
        ih (by omega), evalCoeffPolyAux]

private theorem evalCoeffPolyAux_extend_tail
    (shortZeroPoly : PolynomialCoeff) (k : Nat) (hk : k ≤ CELLS_PER_EXT_BLOB)
    (x : Fr) :
    let p := (List.range k).foldl
      (fun zeroPoly j => zeroPoly.set! (j * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[j]!)
      (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)
    ∀ d : Nat,
      evalCoeffPolyAux p x (k * FIELD_ELEMENTS_PER_CELL + d) =
        evalCoeffPolyAux p x (k * FIELD_ELEMENTS_PER_CELL) := by
  intro p d
  have hcell : FIELD_ELEMENTS_PER_CELL = 64 := rfl
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, evalCoeffPolyAux, ih]
    have hget := foldl_vanishing_extend_getElem!_all shortZeroPoly k hk
      (k * FIELD_ELEMENTS_PER_CELL + d)
    have hnot : ¬ ((k * FIELD_ELEMENTS_PER_CELL + d) % FIELD_ELEMENTS_PER_CELL = 0 ∧
        (k * FIELD_ELEMENTS_PER_CELL + d) / FIELD_ELEMENTS_PER_CELL < k) := by
      rintro ⟨_, hlt⟩
      rw [hcell] at hlt
      omega
    rw [ite_eq_right hnot] at hget
    have h0mul (y : Fr) : Fr.zero * y = Fr.zero := Fin.zero_mul y
    have hadd0 (y : Fr) : y + Fr.zero = y := Fin.add_zero y
    change evalCoeffPolyAux p x (k * FIELD_ELEMENTS_PER_CELL) +
        p[k * FIELD_ELEMENTS_PER_CELL + d]! * x.powNat (k * FIELD_ELEMENTS_PER_CELL + d) = _
    rw [hget, h0mul, hadd0]

/-- Evaluating the extended vanishing polynomial `p` constructed from
`missingCellIndices` at `x` equals evaluating the reduced vanishing polynomial
at `x ^ FIELD_ELEMENTS_PER_CELL`. -/
theorem evalPolyAt_constructVanishingPolynomial
    {missingCellIndices : Array CellIndex} {p : PolynomialCoeff}
    (h : constructVanishingPolynomial missingCellIndices = .ok p) (x : Fr) :
    ∃ shortZeroPoly,
      vanishingPolynomialcoeff (missingCellIndices.map fun mci =>
        (computeRootsOfUnity CELLS_PER_EXT_BLOB)[BitReversal.reverseBits mci CELLS_PER_EXT_BLOB]!) =
          .ok shortZeroPoly ∧
      evalPolyAt p x = evalPolyAt shortZeroPoly (Fr.powNat x FIELD_ELEMENTS_PER_CELL) := by
  have hcell : FIELD_ELEMENTS_PER_CELL = 64 := rfl
  have hext : FIELD_ELEMENTS_PER_EXT_BLOB = 8192 := rfl
  have hcells : CELLS_PER_EXT_BLOB = 128 := rfl
  simp only [constructVanishingPolynomial, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i hlt
    have hlt' : missingCellIndices.size < CELLS_PER_EXT_BLOB := Nat.lt_of_not_le hlt
    split at h
    · cases h
    · rename_i shortZeroPoly hshort
      injection h with hp
      subst hp
      obtain ⟨hshort_sz, _⟩ := size_and_leadingCoeff_vanishingPolynomialcoeff hshort
      simp only [Array.size_map] at hshort_sz
      have hk : shortZeroPoly.size ≤ CELLS_PER_EXT_BLOB := by omega
      refine ⟨shortZeroPoly, hshort, ?_⟩
      have hfold :
          (Array.range shortZeroPoly.size).foldl
            (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
            (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) =
          (List.range shortZeroPoly.size).foldl
            (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
            (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) := by
        rw [← Array.foldl_toList, Array.toList_range]
      unfold evalPolyAt evalCoeffPoly
      rw [hfold]
      have hp_sz : ((List.range shortZeroPoly.size).foldl
          (fun zeroPoly i => zeroPoly.set! (i * FIELD_ELEMENTS_PER_CELL) shortZeroPoly[i]!)
          (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero)).size =
          FIELD_ELEMENTS_PER_EXT_BLOB :=
        (foldl_vanishing_extend_size_and_getElem! shortZeroPoly
          (Array.replicate FIELD_ELEMENTS_PER_EXT_BLOB Fr.zero) (by simp) shortZeroPoly.size hk).1
      have hsplit : FIELD_ELEMENTS_PER_EXT_BLOB =
          shortZeroPoly.size * FIELD_ELEMENTS_PER_CELL +
            (FIELD_ELEMENTS_PER_EXT_BLOB - shortZeroPoly.size * FIELD_ELEMENTS_PER_CELL) := by
        rw [hcell, hext]
        rw [hcells] at hk
        omega
      have htail := evalCoeffPolyAux_extend_tail shortZeroPoly shortZeroPoly.size hk x
        (FIELD_ELEMENTS_PER_EXT_BLOB - shortZeroPoly.size * FIELD_ELEMENTS_PER_CELL)
      rw [← hsplit] at htail
      rw [hp_sz, htail,
          evalCoeffPolyAux_extend_prefix shortZeroPoly shortZeroPoly.size hk x
            shortZeroPoly.size (Nat.le_refl _)]

/-- `constructVanishingPolynomial missingCellIndices` vanishes at every point `x`
whose `FIELD_ELEMENTS_PER_CELL`-th power is the bit-reversed root corresponding
to a missing cell index `mci ∈ missingCellIndices.toList`. -/
theorem constructVanishingPolynomial_eval_eq_zero
    {missingCellIndices : Array CellIndex} {p : PolynomialCoeff}
    (h : constructVanishingPolynomial missingCellIndices = .ok p)
    {mci : CellIndex} (hmci : mci ∈ missingCellIndices.toList)
    {x : Fr}
    (hx : Fr.powNat x FIELD_ELEMENTS_PER_CELL =
      (computeRootsOfUnity CELLS_PER_EXT_BLOB)[BitReversal.reverseBits mci CELLS_PER_EXT_BLOB]!) :
    evalPolyAt p x = Fr.zero := by
  obtain ⟨shortZeroPoly, hshort, heval⟩ := evalPolyAt_constructVanishingPolynomial h x
  rw [heval]
  apply vanishingPolynomialcoeff_eval_root hshort
  rw [Array.toList_map, hx]
  exact List.mem_map_of_mem hmci

/-- `recoverPolynomialcoeff` rejects mismatched `cellIndices` and `cosetsEvals`
lengths. -/
theorem recoverPolynomialcoeff_length_mismatch
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals}
    (h : cosetsEvals.size ≠ cellIndices.size) :
    recoverPolynomialcoeff cellIndices cosetsEvals =
      .error (.inputLengthMismatch "cosetsEvals" cellIndices.size cosetsEvals.size) := by
  simp [recoverPolynomialcoeff, h, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

set_option maxRecDepth 4096 in
/-- On success, the recovered polynomial has exactly
`FIELD_ELEMENTS_PER_BLOB` coefficients, whatever the inputs. -/
theorem size_recoverPolynomialcoeff
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals}
    {p : PolynomialCoeff}
    (h : recoverPolynomialcoeff cellIndices cosetsEvals = .ok p) :
    p.size = FIELD_ELEMENTS_PER_BLOB := by
  rw [recoverPolynomialcoeff] at h
  split at h
  · exact absurd h (by simp [Bind.bind, Except.bind])
  · obtain ⟨u, hu, h⟩ := except_bind_eq_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [FIELD_ELEMENTS_PER_EXT_BLOB]
    omega

private theorem list_length_filter_lt_iff {α : Type _} (l : List α) (f : α → Bool) :
    (l.filter f).length < l.length ↔ ∃ x ∈ l, f x = false := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.filter_cons, List.length_cons, List.mem_cons, exists_eq_or_imp]
    by_cases hfa : f a = true
    · rw [ite_eq_left hfa, List.length_cons]
      have hne : f a ≠ false := by rw [hfa]; decide
      simp [hne, ih]
    · have hfa' : f a = false := Bool.eq_false_iff.mpr hfa
      rw [ite_eq_right hfa, hfa']
      have hle : (as.filter f).length ≤ as.length := List.length_filter_le f as
      exact ⟨fun _ => Or.inl rfl, fun _ => by omega⟩

private theorem missing_size_lt_iff (cellIndices : Array CellIndex) :
    ((Array.range CELLS_PER_EXT_BLOB).filter (fun ci => !cellIndices.contains ci)).size <
        CELLS_PER_EXT_BLOB ↔
      ∃ ci < CELLS_PER_EXT_BLOB, cellIndices.contains ci = true := by
  rw [← Array.length_toList, Array.toList_filter, Array.toList_range]
  have hiff := list_length_filter_lt_iff (List.range CELLS_PER_EXT_BLOB)
    (fun ci => !cellIndices.contains ci)
  rw [List.length_range] at hiff
  rw [hiff]
  simp only [List.mem_range, Bool.not_eq_false']

/-- `recoverPolynomialcoeff` succeeds whenever `cosetsEvals.size = cellIndices.size`
and `cellIndices` contains at least one valid cell index `< CELLS_PER_EXT_BLOB`,
returning a coefficient array of size `FIELD_ELEMENTS_PER_BLOB`. -/
theorem recoverPolynomialcoeff_ok_of_contains
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals}
    (hlen : cosetsEvals.size = cellIndices.size)
    (hci : ∃ ci < CELLS_PER_EXT_BLOB, cellIndices.contains ci = true) :
    ∃ p, recoverPolynomialcoeff cellIndices cosetsEvals = .ok p ∧
      p.size = FIELD_ELEMENTS_PER_BLOB := by
  have hmissing :
      ((Array.range CELLS_PER_EXT_BLOB).filter (fun ci => !cellIndices.contains ci)).size <
        CELLS_PER_EXT_BLOB :=
    (missing_size_lt_iff cellIndices).mpr hci
  obtain ⟨z, hz, _, _⟩ := constructVanishingPolynomial_ok_of_lt hmissing
  have hok : ∃ p, recoverPolynomialcoeff cellIndices cosetsEvals = .ok p := by
    unfold recoverPolynomialcoeff
    rw [ite_eq_right (by omega)]
    simp only [Bind.bind, Except.bind, pure, Except.pure, hz]
    exact ⟨_, rfl⟩
  rcases hok with ⟨p, hp⟩
  exact ⟨p, hp, size_recoverPolynomialcoeff hp⟩

/-- `recoverPolynomialcoeff cellIndices cosetsEvals` succeeds iff
`cosetsEvals.size = cellIndices.size` and `cellIndices` contains at least one
cell index `< CELLS_PER_EXT_BLOB`. -/
theorem recoverPolynomialcoeff_ok_iff
    {cellIndices : Array CellIndex} {cosetsEvals : Array CosetEvals} :
    (∃ p, recoverPolynomialcoeff cellIndices cosetsEvals = .ok p) ↔
      cosetsEvals.size = cellIndices.size ∧
        ∃ ci < CELLS_PER_EXT_BLOB, cellIndices.contains ci = true := by
  constructor
  · rintro ⟨p, h⟩
    rw [recoverPolynomialcoeff] at h
    by_cases hne : cosetsEvals.size ≠ cellIndices.size
    · rw [ite_eq_left hne] at h
      exact absurd h (by simp [Bind.bind, Except.bind])
    · have hlen : cosetsEvals.size = cellIndices.size := Decidable.of_not_not hne
      rw [ite_eq_right hne] at h
      obtain ⟨z, hz, _⟩ := except_bind_eq_ok h
      have hlt := (leadingCoeff_constructVanishingPolynomial hz).1
      exact ⟨hlen, (missing_size_lt_iff cellIndices).mp hlt⟩
  · rintro ⟨hlen, hci⟩
    obtain ⟨p, hp, _⟩ := recoverPolynomialcoeff_ok_of_contains hlen hci
    exact ⟨p, hp⟩

/-- `recoverCellsAndKzgProofs` rejects a cells array whose length does
not match the indices array. -/
theorem recoverCellsAndKzgProofs_length_mismatch
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (h : cells.size ≠ cellIndices.size) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw (.inputLengthMismatch "cells" cellIndices.size cells.size) := by
  simp [recoverCellsAndKzgProofs, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects fewer than 50% of the cells. -/
theorem recoverCellsAndKzgProofs_notEnoughCells
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (h : cellIndices.size < CELLS_PER_EXT_BLOB / 2) :
    recoverCellsAndKzgProofs cellIndices cells = throw .notEnoughCells := by
  simp [recoverCellsAndKzgProofs, hlen, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects more cells than exist. -/
theorem recoverCellsAndKzgProofs_tooManyCells
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (h : cellIndices.size > CELLS_PER_EXT_BLOB) :
    recoverCellsAndKzgProofs cellIndices cells = throw .tooManyCells := by
  simp [recoverCellsAndKzgProofs, hlen, hmin, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects an out-of-bounds cell index. -/
theorem recoverCellsAndKzgProofs_cellIndexOutOfBounds
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw .cellIndexOutOfBounds := by
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects cell indices that are not
strictly ascending. -/
theorem recoverCellsAndKzgProofs_indicesNotAscending
    {cellIndices : Array CellIndex} {cells : Array Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (h : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = true) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw .indicesNotAscending := by
  simp only [Array.size_range] at h
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, hbound, h]
  rfl

/-- `recoverCellsAndKzgProofs` rejects a wrongly-sized cell, reporting
the first offender's size. -/
theorem recoverCellsAndKzgProofs_badCellSize
    {cellIndices : Array CellIndex} {cells : Array Cell} {c : Cell}
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hasc : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = false)
    (h : cells.find? (fun c => c.size != BYTES_PER_CELL) = some c) :
    recoverCellsAndKzgProofs cellIndices cells
      = throw (.badCellSize c.size) := by
  simp only [Array.size_range] at hasc
  simp [recoverCellsAndKzgProofs, hlen, hmin, hmax, hbound, hasc, h]
  rfl

/-- The recovery vanishing polynomial has no coefficient above its mathematical degree bound. -/
theorem constructVanishingPolynomial_high_zero
    {missing : Array CellIndex} {p : PolynomialCoeff}
    (hp : constructVanishingPolynomial missing = .ok p)
    (i : Nat) (hi : missing.size * FIELD_ELEMENTS_PER_CELL < i) : p[i]! = Fr.zero := by
  simp only [constructVanishingPolynomial, bind, Except.bind, pure, Except.pure] at hp
  split at hp
  · cases hp
  · rename_i hlt
    split at hp
    · cases hp
    · rename_i q hq
      injection hp with he
      subst he
      obtain ⟨hsz, _⟩ := size_and_leadingCoeff_vanishingPolynomialcoeff hq
      simp only [Array.size_map] at hsz
      rw [← Array.foldl_toList, Array.toList_range,
        foldl_vanishing_extend_getElem!_all q q.size (by omega)]
      rw [ite_eq_right]
      rintro ⟨hmod, hdiv⟩
      have hc : FIELD_ELEMENTS_PER_CELL = 64 := rfl
      rw [hc] at hi hmod hdiv
      omega

end EthLib.Cryptography.Kzg
