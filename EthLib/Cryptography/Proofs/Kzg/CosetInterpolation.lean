module

public import EthLib.Cryptography.Proofs.Kzg.ExtendedCells
public import EthLib.Cryptography.Proofs.Kzg.Interpolation
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Proofs: cell interpolation via inverse coset FFT

Each cell holds 64 evaluations on a shifted roots-of-unity coset in bit-reversed order.

The Fulu sampling specification recovers the cell polynomial with general Lagrange interpolation.

See `consensus-specs` `specs/fulu/polynomial-commitments-sampling.md` at `8a3df1d79d70000801407e33d660171be9cd06d1`.

Lagrange interpolation computes `64 * 63` field inversions per cell.

`interpolateCosetEvals` exploits the coset structure instead.

It bit-reverses the evaluations, runs one inverse FFT of size 64, and scales coefficient `i` by `h^(-i)`.

```text
    coset[j] = h * v^(rev_6(j))      v = domainRoot 64, h = coset shift
    evals  --brp-->  IFFT_64  --shift by h^(-1)-->  coefficients I
```

This file proves:

- `interpolateCosetEvals` rejects wrong-sized inputs and succeeds on 64 elements.
- Every coset point of cell `cellIndex` factors as `h * domainRoot 64 ^ reverseBits j 64`.
- The output polynomial evaluates to `evals[j]!` at every coset point `coset[j]!`.
- The output equals `interpolatePolynomialcoeff coset evals` coefficient by coefficient.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

private theorem fr_pow_add (a : Fr) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := pow_add a m n
private theorem fr_pow_mul (a : Fr) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := pow_mul a m n
private theorem fr_one_mul (a : Fr) : 1 * a = a := one_mul a
private theorem fr_inv_mul_cancel {a : Fr} (ha : a ≠ 0) : a⁻¹ * a = 1 := inv_mul_cancel₀ ha

/-- Bit `t` of `a * 2^k + b` comes from `b` below `k` and from `a` above it when `b < 2^k`. -/
private theorem testBit_mul_two_pow_add {a b k : Nat} (hb : b < 2 ^ k) (t : Nat) :
    (a * 2 ^ k + b).testBit t = if t < k then b.testBit t else a.testBit (t - k) := by
  by_cases htk : t < k
  · rw [ite_eq_left htk]
    have hmod : (a * 2 ^ k + b) % 2 ^ k = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    have htb := congrArg (fun x => x.testBit t) hmod
    rw [Nat.testBit_mod_two_pow, decide_eq_true htk, Bool.true_and] at htb
    exact htb
  · rw [ite_eq_right htk]
    have hdiv : (a * 2 ^ k + b) / 2 ^ k = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hb,
        Nat.zero_add]
    have htb := congrArg (fun x => x.testBit (t - k)) hdiv
    rw [Nat.testBit_div_two_pow, show t - k + k = t by omega] at htb
    exact htb

/-! ## Bit-reversal splitting and cell coset factorization -/

/-- Reversing `64 * ci + j` across 13 bits splits into 7 bits of `ci` and 6 shifted bits of `j`. -/
theorem reverseBits_cell_index_offset (ci j : Nat)
    (hj : j < FIELD_ELEMENTS_PER_CELL) :
    reverseBits (FIELD_ELEMENTS_PER_CELL * ci + j) FIELD_ELEMENTS_PER_EXT_BLOB =
      reverseBits ci CELLS_PER_EXT_BLOB +
        CELLS_PER_EXT_BLOB * reverseBits j FIELD_ELEMENTS_PER_CELL := by
  have hj' : j < 2 ^ 6 := hj
  change reverseBits (2 ^ 6 * ci + j) (2 ^ 13) =
    reverseBits ci (2 ^ 7) + 2 ^ 7 * reverseBits j (2 ^ 6)
  have hlow_lt : reverseBits ci (2 ^ 7) < 2 ^ 7 := reverseBits_lt_two_pow ci 7
  -- Write a * 2^k + b with the low k bits disjoint from the shifted upper part.
  rw [Nat.mul_comm (2 ^ 6) ci, Nat.mul_comm (2 ^ 7) (reverseBits j (2 ^ 6))]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [testBit_reverseBits, Nat.add_comm (reverseBits ci (2 ^ 7)), testBit_mul_two_pow_add hlow_lt]
  by_cases ht7 : t < 7
  · -- Low 7 bits come from the upper 7 bits of `ci * 2^6 + j`, which are bits of `ci`.
    rw [ite_eq_left (by omega : t < 13), ite_eq_left ht7,
      testBit_reverseBits, ite_eq_left ht7,
      testBit_mul_two_pow_add hj', ite_eq_right (by omega : ¬ 13 - 1 - t < 6)]
    congr 1
    omega
  · by_cases ht13 : t < 13
    · -- Bits 7..12 come from the low 6 bits of `ci * 2^6 + j`, which are bits of `j`.
      rw [ite_eq_left ht13, ite_eq_right ht7,
        testBit_reverseBits, ite_eq_left (by omega : t - 7 < 6),
        testBit_mul_two_pow_add hj', ite_eq_left (by omega : 13 - 1 - t < 6)]
      congr 1
      omega
    · -- Bits 13 and above are zero on both sides.
      rw [ite_eq_right ht13, ite_eq_right ht7,
        testBit_reverseBits, ite_eq_right (by omega : ¬ t - 7 < 6)]

/-- The extended-domain generator to the 128th power is the 64-element cell-domain generator. -/
theorem domainRoot_extended_pow_cells :
    domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ CELLS_PER_EXT_BLOB =
      domainRoot FIELD_ELEMENTS_PER_CELL := by
  unfold domainRoot
  rw [Bls.Fr.hpow_eq_pow, Bls.Fr.hpow_eq_pow]
  have h1 : (Fr.ofNat ((BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_EXT_BLOB)).val =
      (BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_EXT_BLOB := by decide
  have h2 : (Fr.ofNat ((BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_CELL)).val =
      (BLS_MODULUS - 1) / FIELD_ELEMENTS_PER_CELL := by decide
  rw [h1, h2, ← fr_pow_mul]
  congr 1

/-- Each point of `cosetForCell cellIndex` is the coset shift times a bit-reversed 64th root. -/
theorem getElem!_cosetForCell_eq_shift_mul_root
    {cellIndex : CellIndex} {coset : Coset}
    (hcoset : cosetForCell cellIndex = .ok coset)
    (j : Nat) (hj : j < FIELD_ELEMENTS_PER_CELL) :
    coset[j]! =
      (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]! *
        domainRoot FIELD_ELEMENTS_PER_CELL ^ reverseBits j FIELD_ELEMENTS_PER_CELL := by
  have hci : cellIndex < CELLS_PER_EXT_BLOB :=
    cosetForCell_ok_iff.mp ⟨coset, hcoset⟩
  obtain ⟨c', hc', _, hcelem⟩ := cosetForCell_ok_of_lt hci
  have hceq : coset = c' := Except.ok.inj (hcoset.symm.trans hc')
  subst hceq
  have hdom_idx (m : Nat) (hm : m < FIELD_ELEMENTS_PER_EXT_BLOB) :
      (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[m]! =
        domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ reverseBits m FIELD_ELEMENTS_PER_EXT_BLOB := by
    rw [rootsOfUnityBrp, getElem!_bitReversalPermutation _ m (by
        rw [size_computeRootsOfUnity]; exact hm),
      size_computeRootsOfUnity,
      getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) _ (by
        rw [size_computeRootsOfUnity]; exact reverseBits_lt_two_pow m 13),
      getElem_computeRootsOfUnity]
  have hm_lt : FIELD_ELEMENTS_PER_CELL * cellIndex + j < FIELD_ELEMENTS_PER_EXT_BLOB := by
    have hstop : FIELD_ELEMENTS_PER_CELL * (cellIndex + 1) ≤ FIELD_ELEMENTS_PER_EXT_BLOB := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right FIELD_ELEMENTS_PER_CELL (Nat.succ_le_of_lt hci)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rwa [Nat.mul_succ] at hstop)
  have h0_lt : FIELD_ELEMENTS_PER_CELL * cellIndex < FIELD_ELEMENTS_PER_EXT_BLOB :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ j) hm_lt
  rw [hcelem j hj, hdom_idx _ hm_lt, hdom_idx _ h0_lt]
  have h0_rev := reverseBits_cell_index_offset cellIndex 0 (by decide)
  have hj_rev := reverseBits_cell_index_offset cellIndex j hj
  have hrev0 : reverseBits 0 FIELD_ELEMENTS_PER_CELL = 0 := by decide
  rw [Nat.add_zero, hrev0, Nat.mul_zero, Nat.add_zero] at h0_rev
  rw [hj_rev, h0_rev, fr_pow_add, fr_pow_mul, domainRoot_extended_pow_cells]

/-- The coset shift of any valid cell is nonzero because it is a root of unity. -/
theorem cosetShift_ne_zero (cellIndex : CellIndex) (hci : cellIndex < CELLS_PER_EXT_BLOB) :
    (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]! ≠ 0 := by
  have hm : FIELD_ELEMENTS_PER_CELL * cellIndex < FIELD_ELEMENTS_PER_EXT_BLOB := by
    have hle := Nat.mul_le_mul_left FIELD_ELEMENTS_PER_CELL (Nat.succ_le_of_lt hci)
    have hcap : FIELD_ELEMENTS_PER_CELL * CELLS_PER_EXT_BLOB = FIELD_ELEMENTS_PER_EXT_BLOB := rfl
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < FIELD_ELEMENTS_PER_CELL))
      (by rwa [Nat.mul_succ, hcap] at hle)
  rw [rootsOfUnityBrp, getElem!_bitReversalPermutation _ _ (by
      rw [size_computeRootsOfUnity]; exact hm),
    size_computeRootsOfUnity,
    getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) _ (by
      rw [size_computeRootsOfUnity]; exact reverseBits_lt_two_pow _ 13),
    getElem_computeRootsOfUnity]
  exact pow_ne_zero _ ((isPrimitiveRoot_domainRoot
    (Nat.dvd_of_mod_eq_zero (by decide) : FIELD_ELEMENTS_PER_EXT_BLOB ∣ BLS_MODULUS - 1)).ne_zero
      (by decide))

/-- Points within a cell's coset are pairwise distinct. -/
theorem cosetForCell_distinct {cellIndex : CellIndex} {coset : Coset}
    (hcoset : cosetForCell cellIndex = .ok coset) :
    ∀ i j, i < coset.size → j < coset.size → i ≠ j → coset[i]! ≠ coset[j]! := by
  have hci : cellIndex < CELLS_PER_EXT_BLOB :=
    cosetForCell_ok_iff.mp ⟨coset, hcoset⟩
  obtain ⟨c', hc', hcsz, hcelem⟩ := cosetForCell_ok_of_lt hci
  have hceq : coset = c' := Except.ok.inj (hcoset.symm.trans hc')
  subst hceq
  intro i j hi hj hij heq
  rw [hcsz] at hi hj
  rw [hcelem i hi, hcelem j hj] at heq
  have hbound (k : Nat) (hk : k < FIELD_ELEMENTS_PER_CELL) :
      FIELD_ELEMENTS_PER_CELL * cellIndex + k < FIELD_ELEMENTS_PER_EXT_BLOB := by
    have hle := Nat.mul_le_mul_left FIELD_ELEMENTS_PER_CELL (Nat.succ_le_of_lt hci)
    have hcap : FIELD_ELEMENTS_PER_CELL * CELLS_PER_EXT_BLOB = FIELD_ELEMENTS_PER_EXT_BLOB := rfl
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (by rwa [Nat.mul_succ, hcap] at hle)
  have hinj := getElem_rootsOfUnityBrp_inj (n := FIELD_ELEMENTS_PER_EXT_BLOB) (k := 13) rfl
    (Nat.dvd_of_mod_eq_zero (by decide)) (hbound i hi) (hbound j hj) heq
  exact hij (Nat.add_left_cancel hinj)

/-! ## Correctness of `interpolateCosetEvals` -/

/-- `interpolateCosetEvals` rejects an array whose size differs from `FIELD_ELEMENTS_PER_CELL`. -/
theorem interpolateCosetEvals_inputLengthMismatch {h : Fr} {evals : CosetEvals}
    (hsz : evals.size ≠ FIELD_ELEMENTS_PER_CELL) :
    interpolateCosetEvals h evals =
      .error (.inputLengthMismatch "ys" FIELD_ELEMENTS_PER_CELL evals.size) := by
  simp [interpolateCosetEvals, hsz, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

private theorem cell_roots (i : Nat) (hi : i < 2 ^ 6) :
    (computeRootsOfUnity FIELD_ELEMENTS_PER_CELL)[i]! =
      domainRoot FIELD_ELEMENTS_PER_CELL ^ i := by
  rw [getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_CELL) i
    (by rw [size_computeRootsOfUnity]; exact hi), getElem_computeRootsOfUnity]

/-- On 64 evaluations and nonzero shift `h`, `interpolateCosetEvals` returns 64 coefficients.

Those coefficients evaluate to `evals[j]!` at `h * domainRoot 64 ^ reverseBits j 64`.
-/
theorem interpolateCosetEvals_spec_of_ne_zero {h : Fr} {evals : CosetEvals}
    (hh : h ≠ 0) (hevals : evals.size = FIELD_ELEMENTS_PER_CELL) :
    ∃ p, interpolateCosetEvals h evals = .ok p ∧
      p.size = FIELD_ELEMENTS_PER_CELL ∧
      ∀ j < FIELD_ELEMENTS_PER_CELL,
        evalPolyAt p (h * domainRoot FIELD_ELEMENTS_PER_CELL ^ reverseBits j FIELD_ELEMENTS_PER_CELL) =
          evals[j]! := by
  let coeffJ := fftField (bitReversalPermutation evals)
    (computeRootsOfUnity FIELD_ELEMENTS_PER_CELL) true
  let p := shiftVals coeffJ h.inverse
  have hp_ok : interpolateCosetEvals h evals = .ok p := by
    unfold interpolateCosetEvals
    rw [ite_eq_right (not_not.mpr hevals)]
    rfl
  have hp_sz : p.size = FIELD_ELEMENTS_PER_CELL := by
    rw [size_shiftVals, size_fftField, size_bitReversalPermutation, hevals]
  refine ⟨p, hp_ok, hp_sz, fun j hj => ?_⟩
  -- Scaling the evaluation point by h^(-1) cancels the coset shift h.
  rw [evalPolyAt_shiftVals, Bls.Fr.inverse_eq_inv]
  have hcancel : h⁻¹ * (h * domainRoot FIELD_ELEMENTS_PER_CELL ^ reverseBits j FIELD_ELEMENTS_PER_CELL) =
      domainRoot FIELD_ELEMENTS_PER_CELL ^ reverseBits j FIELD_ELEMENTS_PER_CELL := by
    rw [← Bls.Fr.mul_assoc, fr_inv_mul_cancel hh, fr_one_mul]
  rw [hcancel]
  -- Evaluate coeffJ via the forward FFT, then cancel IFFT followed by FFT.
  have hrev_lt : reverseBits j FIELD_ELEMENTS_PER_CELL < FIELD_ELEMENTS_PER_CELL :=
    reverseBits_lt_two_pow j 6
  have hj_sz : coeffJ.size = 2 ^ 6 := by
    rw [size_fftField, size_bitReversalPermutation, hevals]; rfl
  have hω : IsPrimitiveRoot (domainRoot FIELD_ELEMENTS_PER_CELL) (2 ^ 6) :=
    isPrimitiveRoot_domainRoot (Nat.dvd_of_mod_eq_zero (by decide))
  rw [← getElem!_fftField_eval hω coeffJ (computeRootsOfUnity FIELD_ELEMENTS_PER_CELL)
      hj_sz (size_computeRootsOfUnity _) cell_roots
      (reverseBits j FIELD_ELEMENTS_PER_CELL) hrev_lt]
  have hbrp_sz : (bitReversalPermutation evals).size = 2 ^ 6 := by
    rw [size_bitReversalPermutation, hevals]; rfl
  rw [fftField_inv_fftField hω (bitReversalPermutation evals)
      (computeRootsOfUnity FIELD_ELEMENTS_PER_CELL) hbrp_sz
      (size_computeRootsOfUnity _) cell_roots]
  -- Undo the 6-bit reversal to recover evals[j]!.
  rw [getElem!_bitReversalPermutation evals _ (by rw [hevals]; exact hrev_lt),
    hevals]
  have hback : reverseBits (reverseBits j FIELD_ELEMENTS_PER_CELL) FIELD_ELEMENTS_PER_CELL = j :=
    reverseBits_reverseBits (k := 6) hj
  rw [hback]

/-- Equal-size coefficient arrays agreeing on `size` distinct nodes are identical. -/
theorem polynomialCoeff_eq_of_eval_eq_on {p q : PolynomialCoeff} {xs : Array Fr}
    (hpsz : p.size = xs.size) (hqsz : q.size = xs.size)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (heval : ∀ k < xs.size, evalPolyAt p xs[k]! = evalPolyAt q xs[k]!) :
    p = q := by
  by_cases h0 : xs.size = 0
  · apply Array.ext (hpsz.trans hqsz.symm)
    intro i hi _
    omega
  · have hpos : 0 < xs.size := Nat.pos_of_ne_zero h0
    let f : Fin xs.size → Fr := fun k => xs[k.val]!
    have hfinj : Function.Injective f := by
      intro a b hab
      by_contra hne
      exact hdistinct a.val b.val a.isLt b.isLt (Fin.val_ne_of_ne hne) hab
    -- Both arrays represent polynomials of degree below `xs.size` that agree on `xs`.
    have hp_deg : (coefficientPolynomial p).degree < (Finset.univ : Finset (Fin xs.size)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      rcases eq_or_ne (coefficientPolynomial p) 0 with hp0 | hp0
      · rw [hp0, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe xs.size
      · rw [Polynomial.degree_eq_natDegree hp0]
        exact WithBot.coe_lt_coe.mpr
          (hpsz ▸ natDegree_coefficientPolynomial_lt (hpsz.symm ▸ hpos))
    have hq_deg : (coefficientPolynomial q).degree < (Finset.univ : Finset (Fin xs.size)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      rcases eq_or_ne (coefficientPolynomial q) 0 with hq0 | hq0
      · rw [hq0, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe xs.size
      · rw [Polynomial.degree_eq_natDegree hq0]
        exact WithBot.coe_lt_coe.mpr
          (hqsz ▸ natDegree_coefficientPolynomial_lt (hqsz.symm ▸ hpos))
    have hpoly_eq : coefficientPolynomial p = coefficientPolynomial q :=
      Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hfinj.injOn hp_deg hq_deg fun k _ => by
        rw [eval_coefficientPolynomial, eval_coefficientPolynomial]
        exact heval k.val k.isLt
    apply Array.ext (hpsz.trans hqsz.symm)
    intro i hi1 hi2
    rw [← getElem!_pos p i hi1, ← getElem!_pos q i hi2,
      ← coeff_coefficientPolynomial, ← coeff_coefficientPolynomial, hpoly_eq]

/-- On a valid cell, `interpolateCosetEvals` and `interpolatePolynomialcoeff` return the same polynomial.

Let `cosetForCell cellIndex = .ok coset` and `h = (rootsOfUnityBrp 8192)[64 * cellIndex]!`.

For any 64-element vector `evals`, both methods succeed with one 64-coefficient polynomial `p`.

Moreover `evaluatePolynomialcoeff p coset[j]! = evals[j]!` for every `j < 64`.
-/
theorem interpolateCosetEvals_eq_interpolatePolynomialcoeff
    {cellIndex : CellIndex} {coset : Coset} {evals : CosetEvals}
    (hcoset : cosetForCell cellIndex = .ok coset)
    (hevals : evals.size = FIELD_ELEMENTS_PER_CELL) :
    ∃ p,
      interpolateCosetEvals
        (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]!
        evals = .ok p ∧
      interpolatePolynomialcoeff coset evals = .ok p ∧
      p.size = FIELD_ELEMENTS_PER_CELL ∧
      ∀ j < FIELD_ELEMENTS_PER_CELL, evaluatePolynomialcoeff p coset[j]! = evals[j]! := by
  have hci : cellIndex < CELLS_PER_EXT_BLOB :=
    cosetForCell_ok_iff.mp ⟨coset, hcoset⟩
  have hcsz : coset.size = FIELD_ELEMENTS_PER_CELL := size_cosetForCell hcoset
  have hh_ne :
      (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]! ≠ 0 :=
    cosetShift_ne_zero cellIndex hci
  obtain ⟨p, hp_ok, hp_sz, hp_eval⟩ := interpolateCosetEvals_spec_of_ne_zero hh_ne hevals
  have hbound : coset.size < FIELD_ELEMENTS_PER_EXT_BLOB := by
    rw [hcsz]; decide
  have hdist := cosetForCell_distinct hcoset
  obtain ⟨q, hq_ok, hq_sz, hq_eval⟩ :=
    interpolatePolynomialcoeff_spec_of_distinct (hcsz.trans hevals.symm) hbound hdist
  have hq_sz' : q.size = FIELD_ELEMENTS_PER_CELL := by
    rw [hq_sz, hcsz]; decide
  have hp_coset_eval : ∀ j < FIELD_ELEMENTS_PER_CELL, evalPolyAt p coset[j]! = evals[j]! := by
    intro j hj
    rw [getElem!_cosetForCell_eq_shift_mul_root hcoset j hj]
    exact hp_eval j hj
  have hpq : p = q :=
    polynomialCoeff_eq_of_eval_eq_on
      (hp_sz.trans hcsz.symm) (hq_sz'.trans hcsz.symm) hdist
      (fun j hj => by
        rw [hcsz] at hj
        rw [hp_coset_eval j hj, hq_eval j (by rwa [hcsz])])
  subst hpq
  refine ⟨p, hp_ok, hq_ok, hp_sz, fun j hj => ?_⟩
  rw [evaluatePolynomialcoeff_eq_evalPolyAt]
  exact hp_coset_eval j hj

end EthLib.Cryptography.Kzg
