module

public import EthLib.Cryptography.Proofs.Kzg.FftG1
public import EthLib.Cryptography.Proofs.Kzg.ExtendedCells
public import EthLib.Cryptography.Proofs.Kzg.CosetInterpolation
public import EthLib.Cryptography.Proofs.Kzg.Core
public import EthLib.Cryptography.Proofs.Kzg.Division
public import EthLib.Cryptography.Proofs.Kzg.RecoveryDomain
public import EthLib.Cryptography.Proofs.Kzg.RecoveryReconstruction
public import EthLib.Cryptography.Proofs.Bls.G1Msm
public import EthLib.Cryptography.Proofs.Bls.Compress
-- Lifted successful results are simplified with the public monad laws.
import Batteries.Lean.LawfulMonad
import Init.Control.Lawful.Instances

/-!
# Proofs: FK20 cell proofs equal per-cell quotient commitments

The Fulu sampling specification proves each cell `k` on its own.

See `consensus-specs` `specs/fulu/polynomial-commitments-sampling.md` at `8a3df1d79d70000801407e33d660171be9cd06d1`.

- Build the vanishing polynomial `Z_k(X)` over the 64 points of `cosetForCell k`.
- Divide `f(X)` by `Z_k(X)` in coefficient form to obtain quotient `q_k(X)`.
- Commit to `q_k` with one multi-scalar multiplication against `setup.g1Monomial` and compress.

`computeCellsAndKzgProofsPolynomialcoeff` computes all 128 cell proofs together via the Toeplitz structure of FK20.

See Feist and Khovratovich, "Fast amortized KZG proofs", ePrint 2023/033.

```text
    coset k  : h_k * mu_64,  c_k = h_k^64 = omega_128^(rev_7(k))
    Z_k(X)   : X^64 - c_k
    q_k[t]   : sum_{e < shifts, t + 64*(e+1) < size} c_k^e * f[t + 64*(e+1)]
    H_d      : sum_{t < size - 64*d} f[t + 64*d] * setup.g1Monomial[t]
    proof_k  : compress( sum_{e < shifts} c_k^e * H_(e+1) )
```

`TrustedSetup.globalRef` is an opaque module-init `IO.Ref`.

`computeCellsAndKzgProofsPolynomialcoeff` is stated through its pure body `fk20CellsAndProofs setup polynomialCoeff`.

`computeCellsAndKzgProofsPolynomialcoeff_eq_bind` equates the `IO` wrapper to binding `TrustedSetup.get!`.

This file proves:

- Valid `G1` points representing the same curve element compress to the same 48 bytes.
- Every cell coset's vanishing polynomial `vanishingPolynomialcoeff coset` equals `X^64 - h_k^64`.
- Dividing `polynomialCoeff` by `vanishingPolynomialcoeff coset` gives the Toeplitz series `q_k`.
- Cell `k` of `fk20CellsAndProofs` equals `cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff))`.
- Proof `k` of `fk20CellsAndProofs` equals the compressed MSM of `setup.g1Monomial` by `quotient`.
- Given at least 64 valid cells of a polynomial, `recoverCellsAndKzgProofs` recovers all 128 cells and proofs.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr G1)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

/-- A successful lifted result passes its value to the continuation.
This is `pure_bind` from Lean v4.35.0, `Init.Control.Lawful.Basic`. -/
private theorem bind_mk_ok {α β : Type} (value : α) (next : α → KzgM β) :
    (ExceptT.mk (pure (Except.ok value)) >>= next) = next value := by
  change (pure value >>= next) = next value
  exact pure_bind value next

private theorem fr_pow_zero (a : Fr) : a ^ 0 = 1 := pow_zero a
private theorem fr_pow_succ (a : Fr) (n : Nat) : a ^ (n + 1) = a ^ n * a := pow_succ a n
private theorem fr_pow_add (a : Fr) (m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := pow_add a m n
private theorem fr_pow_mul (a : Fr) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := pow_mul a m n
private theorem fr_mul_pow (a b : Fr) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n := mul_pow a b n
private theorem fr_one_pow (n : Nat) : (1 : Fr) ^ n = 1 := one_pow n
private theorem fr_mul_one (a : Fr) : a * 1 = a := mul_one a
private theorem fr_one_mul (a : Fr) : 1 * a = a := one_mul a
private theorem fr_zero_mul (a : Fr) : (0 : Fr) * a = 0 := zero_mul a
private theorem fr_mul_zero (a : Fr) : a * (0 : Fr) = 0 := mul_zero a
private theorem fr_add_zero (a : Fr) : a + (0 : Fr) = a := add_zero a
private theorem fr_zero_add (a : Fr) : (0 : Fr) + a = a := zero_add a
private theorem fr_sub_mul (a b c : Fr) : (a - b) * c = a * c - b * c := sub_mul a b c
private theorem fr_sub_self (a : Fr) : a - a = 0 := sub_self a
private theorem fr_sub_zero (a : Fr) : a - 0 = a := sub_zero a
private theorem fr_zero_sub (a : Fr) : 0 - a = -a := zero_sub a
private theorem fr_add_sub_cancel_right (a b : Fr) : a + b - b = a := add_sub_cancel_right a b
private theorem fr_add_sub_cancel_left (a b : Fr) : a + b - a = b := add_sub_cancel_left a b
private theorem fr_sub_cancel_top (s₁ s₂ top : Fr) : s₁ - s₂ = (s₁ + top) - (s₂ + top) :=
  (add_sub_add_right_eq_sub s₁ s₂ top).symm

/-! ## Canonical compression of equal `G1` curve points -/

/-- Valid `G1` points with the same `toPoint` image compress to identical 48-byte strings.

`uncompress` maps compressed bytes to a canonical `z = 1` point (or `G1.zero`) with the same `toPoint`.

`compress_uncompress` then rebuilds the original compressed bytes from that canonical point.
-/
theorem compress_eq_of_toPoint_eq {p₁ p₂ : G1}
    (hv₁ : G1.Valid p₁) (hv₂ : G1.Valid p₂)
    (heq : G1.toPoint p₁ = G1.toPoint p₂) :
    G1.compress p₁ = G1.compress p₂ := by
  obtain ⟨q₁, hunc₁, hpt₁⟩ := G1.uncompress_compress hv₁
  obtain ⟨q₂, hunc₂, hpt₂⟩ := G1.uncompress_compress hv₂
  rw [← G1.compress_uncompress hunc₁, ← G1.compress_uncompress hunc₂]
  -- Extract the canonical z = 1 representatives produced by `uncompress`.
  have hrep : q₁ = q₂ := by
    have hpt : G1.toPoint q₁ = G1.toPoint q₂ := hpt₁.trans (heq.trans hpt₂.symm)
    -- Unfold `uncompress` on both sides to see either `zero` or `(x, y, 1)`.
    have hshape (b : ByteArray) (q : G1) (hu : G1.uncompress b = .ok q) :
        q = G1.zero ∨ (q.z = Bls.Fp.one ∧ ¬ q.isInfinity = true) := by
      rw [G1.uncompress] at hu
      split at hu
      · cases hu
      · dsimp only at hu
        split at hu
        · cases hu
        · split at hu
          · split at hu
            · cases hu
            · cases hu
              exact Or.inl rfl
          · split at hu
            · cases hu
            · split at hu
              · cases hu
              · cases hu
                refine Or.inr ⟨rfl, ?_⟩
                change ¬ Bls.Fp.one.isZero = true
                decide
    rcases hshape _ _ hunc₁ with rfl | ⟨hz₁, hni₁⟩ <;>
      rcases hshape _ _ hunc₂ with rfl | ⟨hz₂, hni₂⟩
    · rfl
    · exfalso
      rw [G1.toPoint_zero] at hpt
      have hz2 : (q₂.z : ZMod Bls.Fp.modulus) ≠ 0 :=
        fun h0 => hni₂ (G1.isZero_iff.mpr h0)
      have hvq₂ : G1.Valid q₂ := G1.uncompress_valid hunc₂
      rw [G1.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hvq₂ hz2] at hpt
      cases hpt
    · exfalso
      rw [G1.toPoint_zero] at hpt
      have hz1 : (q₁.z : ZMod Bls.Fp.modulus) ≠ 0 :=
        fun h0 => hni₁ (G1.isZero_iff.mpr h0)
      have hvq₁ : G1.Valid q₁ := G1.uncompress_valid hunc₁
      rw [G1.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hvq₁ hz1] at hpt
      cases hpt
    · have hz1 : (q₁.z : ZMod Bls.Fp.modulus) ≠ 0 :=
        fun h0 => hni₁ (G1.isZero_iff.mpr h0)
      have hz2 : (q₂.z : ZMod Bls.Fp.modulus) ≠ 0 :=
        fun h0 => hni₂ (G1.isZero_iff.mpr h0)
      have hvq₁ : G1.Valid q₁ := G1.uncompress_valid hunc₁
      have hvq₂ : G1.Valid q₂ := G1.uncompress_valid hunc₂
      rw [G1.toPoint, G1.toPoint,
        WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hvq₁ hz1,
        WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hvq₂ hz2] at hpt
      injection hpt with hx hy
      have hdiv1 (a : ZMod Bls.Fp.modulus) (m : Nat) :
          a / (1 : ZMod Bls.Fp.modulus) ^ m = a := by
        rw [one_pow, div_one]
      have hx' : (q₁.x : ZMod Bls.Fp.modulus) = (q₂.x : ZMod Bls.Fp.modulus) := by
        have h := hx
        rw [G1.rep_x, G1.rep_z, G1.rep_x, G1.rep_z, hz₁, hz₂] at h
        exact (hdiv1 q₁.x 2).symm.trans (h.trans (hdiv1 q₂.x 2))
      have hy' : (q₁.y : ZMod Bls.Fp.modulus) = (q₂.y : ZMod Bls.Fp.modulus) := by
        have h := hy
        rw [G1.rep_y, G1.rep_z, G1.rep_y, G1.rep_z, hz₁, hz₂] at h
        exact (hdiv1 q₁.y 3).symm.trans (h.trans (hdiv1 q₂.y 3))
      cases q₁; cases q₂
      dsimp only at hz₁ hz₂ hx' hy'
      rw [G1.mk.injEq]
      exact ⟨hx', hy', hz₁.trans hz₂.symm⟩
  rw [hrep]

/-! ## Cell coset vanishing polynomial: `Z_k(X) = X^64 - c_k` -/

/-- Coefficient representation of `X^n - c`: `-c` at index `0`, `0` through `n - 1`, and `1` at `n`. -/
def binomialVanishing (n : Nat) (c : Fr) : PolynomialCoeff :=
  Array.ofFn (n := n + 1) fun i =>
    if i.val = 0 then -c
    else if i.val = n then Fr.one
    else Fr.zero

@[simp] theorem size_binomialVanishing (n : Nat) (c : Fr) :
    (binomialVanishing n c).size = n + 1 := by
  simp [binomialVanishing]

theorem getElem!_binomialVanishing (n : Nat) (c : Fr) (i : Nat) (hi : i < n + 1) :
    (binomialVanishing n c)[i]! =
      if i = 0 then -c else if i = n then Fr.one else Fr.zero := by
  rw [binomialVanishing, getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]

/-- `binomialVanishing n c` evaluates to `x^n - c` at every `x` when `0 < n`. -/
theorem evalPolyAt_binomialVanishing {n : Nat} (hn : 0 < n) (c x : Fr) :
    evalPolyAt (binomialVanishing n c) x = x ^ n - c := by
  rw [evalPolyAt, evalCoeffPoly, size_binomialVanishing, evalCoeffPolyAux_eq_sum]
  -- Split off the top term i = n.
  rw [Finset.sum_range_succ, getElem!_binomialVanishing n c n (by omega),
    ite_eq_right (Nat.ne_of_gt hn), ite_eq_left rfl]
  -- Split off the constant term i = 0 from the remaining range n.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', getElem!_binomialVanishing (m + 1) c 0 (by omega), ite_eq_left rfl]
  have hmid :
      (∑ k ∈ Finset.range m, (binomialVanishing (m + 1) c)[k + 1]! * x ^ (k + 1)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [getElem!_binomialVanishing (m + 1) c (k + 1) (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]
    exact fr_zero_mul _
  rw [hmid, fr_zero_add, fr_pow_zero, fr_mul_one,
    show (Fr.one : Fr) = 1 from rfl, fr_one_mul]
  exact (add_comm (-c) (x ^ (m + 1))).trans (sub_eq_add_neg (x ^ (m + 1)) c).symm

/-- Raised to the 64-th power, coset shift `cellIndex` is `(computeRootsOfUnity 128)[rev_7(cellIndex)]!`. -/
theorem cosetShift_pow_cell (cellIndex : CellIndex) (hci : cellIndex < CELLS_PER_EXT_BLOB) :
    (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]! ^
        FIELD_ELEMENTS_PER_CELL =
      (computeRootsOfUnity CELLS_PER_EXT_BLOB)[reverseBits cellIndex CELLS_PER_EXT_BLOB]! := by
  have hm : FIELD_ELEMENTS_PER_CELL * cellIndex < FIELD_ELEMENTS_PER_EXT_BLOB := by
    have hle := Nat.mul_le_mul_left FIELD_ELEMENTS_PER_CELL (Nat.succ_le_of_lt hci)
    have hcap : FIELD_ELEMENTS_PER_CELL * CELLS_PER_EXT_BLOB = FIELD_ELEMENTS_PER_EXT_BLOB := rfl
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < FIELD_ELEMENTS_PER_CELL))
      (by rwa [Nat.mul_succ, hcap] at hle)
  have hdom :
      (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]! =
        domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ reverseBits cellIndex CELLS_PER_EXT_BLOB := by
    have h0_rev := reverseBits_cell_index_offset cellIndex 0 (by decide)
    have hrev0 : reverseBits 0 FIELD_ELEMENTS_PER_CELL = 0 := by decide
    rw [Nat.add_zero, hrev0, Nat.mul_zero, Nat.add_zero] at h0_rev
    rw [rootsOfUnityBrp,
      getElem!_bitReversalPermutation _ _ (by rw [size_computeRootsOfUnity]; exact hm),
      size_computeRootsOfUnity, h0_rev,
      getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) _
        (by rw [size_computeRootsOfUnity]; exact Nat.lt_trans (reverseBits_lt_two_pow cellIndex 7) (by decide)),
      getElem_computeRootsOfUnity]
  rw [hdom, ← fr_pow_mul, Nat.mul_comm (reverseBits cellIndex CELLS_PER_EXT_BLOB),
    fr_pow_mul, domainRoot_extended_pow_cell,
    getElem!_pos (computeRootsOfUnity CELLS_PER_EXT_BLOB) _
      (by rw [size_computeRootsOfUnity]; exact reverseBits_lt_two_pow cellIndex 7),
    getElem_computeRootsOfUnity]

/-- Two monic polynomials of size `n + 1` vanishing on `n` distinct points are equal. -/
private theorem monic_poly_eq_of_roots {z b xs : Array Fr} {n : Nat}
    (hxs : xs.size = n)
    (hz_sz : z.size = n + 1) (hb_sz : b.size = n + 1)
    (hz_top : z[n]! = 1) (hb_top : b[n]! = 1)
    (hdistinct : ∀ i j, i < xs.size → j < xs.size → i ≠ j → xs[i]! ≠ xs[j]!)
    (hz_root : ∀ k < xs.size, evalPolyAt z xs[k]! = 0)
    (hb_root : ∀ k < xs.size, evalPolyAt b xs[k]! = 0) :
    z = b := by
  let diff : PolynomialCoeff := Array.ofFn (n := n) fun i => z[i.val]! - b[i.val]!
  have hdiff_sz : diff.size = n := Array.size_ofFn
  have hdiff_get (j : Nat) (hj : j < n) : diff[j]! = z[j]! - b[j]! := by
    rw [getElem!_pos diff j (hdiff_sz ▸ hj)]
    exact Array.getElem_ofFn _
  have hsplit (x : Fr) : evalPolyAt diff x = evalPolyAt z x - evalPolyAt b x := by
    rw [evalPolyAt, evalPolyAt, evalPolyAt, evalCoeffPoly, evalCoeffPoly, evalCoeffPoly,
      hz_sz, hb_sz, hdiff_sz,
      evalCoeffPolyAux_eq_sum, evalCoeffPolyAux_eq_sum, evalCoeffPolyAux_eq_sum,
      Finset.sum_range_succ, Finset.sum_range_succ, hz_top, hb_top]
    have hsub_sum :
        (∑ j ∈ Finset.range n, diff[j]! * x ^ j) =
          (∑ j ∈ Finset.range n, z[j]! * x ^ j) -
            ∑ j ∈ Finset.range n, b[j]! * x ^ j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [hdiff_get j hj, fr_sub_mul]
    rw [hsub_sum]
    exact fr_sub_cancel_top _ _ _
  let zeroN : PolynomialCoeff := Array.replicate xs.size 0
  have hzN_sz : zeroN.size = xs.size := Array.size_replicate
  have hzero_poly : diff = zeroN := by
    refine polynomialCoeff_eq_of_eval_eq_on (hdiff_sz.trans hxs.symm) hzN_sz hdistinct fun k hk => ?_
    rw [hsplit, hz_root k hk, hb_root k hk, fr_sub_zero,
      evalPolyAt, evalCoeffPoly, hzN_sz, evalCoeffPolyAux_eq_sum]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    rw [Finset.mem_range] at hj
    rw [getElem!_pos zeroN j (hzN_sz ▸ hj), Array.getElem_replicate, fr_zero_mul]
  apply Array.ext (hz_sz.trans hb_sz.symm)
  intro i hi1 hi2
  rw [← getElem!_pos z i hi1, ← getElem!_pos b i hi2]
  by_cases hin : i < n
  · have hdi : diff[i]! = 0 := by
      rw [hzero_poly, getElem!_pos zeroN i (by rw [hzN_sz, hxs]; exact hin), Array.getElem_replicate]
    exact sub_eq_zero.mp ((hdiff_get i hin).symm.trans hdi)
  · have hi_eq : i = n := by
      rw [hb_sz] at hi2
      omega
    subst hi_eq
    exact hz_top.trans hb_top.symm

/-- On any valid cell coset `coset` with shift `h`, `vanishingPolynomialcoeff coset` equals `X^64 - h^64`. -/
theorem vanishingPolynomialcoeff_cosetForCell
    {cellIndex : CellIndex} {coset : Coset}
    (hcoset : cosetForCell cellIndex = .ok coset) :
    vanishingPolynomialcoeff coset =
      .ok (binomialVanishing FIELD_ELEMENTS_PER_CELL
        ((rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex]! ^
          FIELD_ELEMENTS_PER_CELL)) := by
  have hcsz : coset.size = FIELD_ELEMENTS_PER_CELL := size_cosetForCell hcoset
  have h64_lt : coset.size + 1 < FIELD_ELEMENTS_PER_EXT_BLOB := by
    rw [hcsz]; decide
  obtain ⟨z, hz, hz_sz, hz_lead⟩ :=
    vanishingPolynomialcoeff_ok_of_lt (xs := coset) h64_lt
  rw [hz]
  apply congrArg Except.ok
  have hprim64 : domainRoot FIELD_ELEMENTS_PER_CELL ^ FIELD_ELEMENTS_PER_CELL = 1 :=
    (isPrimitiveRoot_domainRoot
      (Nat.dvd_of_mod_eq_zero (by decide) : FIELD_ELEMENTS_PER_CELL ∣ BLS_MODULUS - 1)).pow_eq_one
  refine monic_poly_eq_of_roots hcsz (hcsz ▸ hz_sz) (size_binomialVanishing _ _)
    (by rw [← hcsz, hz_lead]; rfl)
    (by
      rw [getElem!_binomialVanishing FIELD_ELEMENTS_PER_CELL _ FIELD_ELEMENTS_PER_CELL (by decide),
        ite_eq_right (by decide : FIELD_ELEMENTS_PER_CELL ≠ 0), ite_eq_left rfl]
      rfl)
    (cosetForCell_distinct hcoset)
    (fun k hk => ?_)
    (fun k hk => ?_)
  · have hmem : coset[k]! ∈ coset.toList := by
      rw [getElem!_pos coset k hk]
      exact Array.getElem_mem_toList hk
    exact vanishingPolynomialcoeff_eval_root hz hmem
  · have hk64 : k < FIELD_ELEMENTS_PER_CELL := hcsz ▸ hk
    rw [evalPolyAt_binomialVanishing (by decide : 0 < FIELD_ELEMENTS_PER_CELL),
      getElem!_cosetForCell_eq_shift_mul_root hcoset k hk64, fr_mul_pow]
    have hroot : (domainRoot FIELD_ELEMENTS_PER_CELL ^ reverseBits k FIELD_ELEMENTS_PER_CELL) ^
        FIELD_ELEMENTS_PER_CELL = 1 := by
      rw [← fr_pow_mul, Nat.mul_comm, fr_pow_mul, hprim64, fr_one_pow]
    rw [hroot, fr_mul_one]
    exact fr_sub_self _

/-! ## Toeplitz quotient formula for division by `X^n - c` -/

/-- Toeplitz quotient array for dividing `f` by `X^n - c`.

When `f.size <= n`, the quotient is empty `#[]`.

When `n < f.size`, it has `f.size - n` coefficients.

Index `t` sums `c^e * f[t + n * (e + 1)]!` over all `e < shifts` with `t + n * (e + 1) < f.size`.
-/
def toeplitzQuotient (f : PolynomialCoeff) (n : Nat) (c : Fr) : PolynomialCoeff :=
  let size := f.size
  let shifts := (size + n - 1) / n - 1
  Array.ofFn (n := size - n) fun t =>
    ∑ e ∈ Finset.range shifts,
      if t.val + n * (e + 1) < size then
        c ^ e * f[t.val + n * (e + 1)]!
      else
        0

@[simp] theorem size_toeplitzQuotient (f : PolynomialCoeff) (n : Nat) (c : Fr) :
    (toeplitzQuotient f n c).size = f.size - n :=
  Array.size_ofFn

theorem getElem!_toeplitzQuotient (f : PolynomialCoeff) (n : Nat) (c : Fr)
    {t : Nat} (ht : t < f.size - n) :
    (toeplitzQuotient f n c)[t]! =
      ∑ e ∈ Finset.range ((f.size + n - 1) / n - 1),
        if t + n * (e + 1) < f.size then
          c ^ e * f[t + n * (e + 1)]!
        else
          0 := by
  rw [toeplitzQuotient, getElem!_pos _ t (by simp [ht])]
  exact Array.getElem_ofFn _

/-- When `t + n * (e + 1) < size` and `0 < n`, shift `e` is below `(size + n - 1) / n - 1`. -/
private theorem shift_lt_shifts {size n t e : Nat} (hn : 0 < n)
    (hlt : t + n * (e + 1) < size) :
    e < (size + n - 1) / n - 1 := by
  have hmul : n * (e + 2) ≤ size + n - 1 := by
    have h1 : n * (e + 1) + 1 ≤ size := by omega
    have h2 : n * (e + 2) = n * (e + 1) + n := by rw [Nat.mul_succ]
    omega
  have hdiv : e + 2 ≤ (size + n - 1) / n := by
    rw [Nat.le_div_iff_mul_le hn]
    rwa [Nat.mul_comm]
  omega

/-- Coefficient identity `(toeplitzQuotient f n c * (X^n - c)).coeff j + r_j = f[j]!`. -/
private theorem coeff_toeplitzQuotient_mul_binomial (f : PolynomialCoeff) {n : Nat}
    (hn : 0 < n) (c : Fr) :
    ∃ r : _root_.Polynomial Fr,
      r.degree < (n : WithBot Nat) ∧
      coefficientPolynomial f =
        coefficientPolynomial (toeplitzQuotient f n c) *
          coefficientPolynomial (binomialVanishing n c) + r := by
  -- Define remainder `r` from the telescoping residue at `j < n`.
  let remArr : PolynomialCoeff := Array.ofFn (n := n) fun j =>
    f[j.val]! + c * (toeplitzQuotient f n c)[j.val]!
  refine ⟨coefficientPolynomial remArr, ?_, ?_⟩
  · rcases eq_or_ne (coefficientPolynomial remArr) 0 with hr0 | hr0
    · rw [hr0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe n
    · rw [Polynomial.degree_eq_natDegree hr0]
      exact WithBot.coe_lt_coe.mpr
        (by simpa [remArr] using natDegree_coefficientPolynomial_lt (p := remArr) (by simp [remArr, hn]))
  · -- Identify `binomialVanishing n c` with `X^n - C c` in `Polynomial Fr`.
    have hbin_poly :
        coefficientPolynomial (binomialVanishing n c) =
          Polynomial.X ^ n - Polynomial.C c := by
      apply Polynomial.ext
      intro k
      rw [coeff_coefficientPolynomial, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, Polynomial.coeff_C]
      by_cases hk : k < n + 1
      · rw [getElem!_binomialVanishing n c k hk]
        by_cases hk0 : k = 0
        · subst hk0
          rw [ite_eq_left rfl, ite_eq_right (Nat.ne_of_lt hn), ite_eq_left rfl]
          exact (fr_zero_sub c).symm
        · rw [ite_eq_right hk0, ite_eq_right hk0]
          by_cases hkn : k = n
          · subst hkn; rw [ite_eq_left rfl, ite_eq_left rfl]; exact (fr_sub_zero 1).symm
          · rw [ite_eq_right hkn, ite_eq_right hkn]; exact (fr_sub_zero 0).symm
      · rw [getElem!_neg _ k (by rw [size_binomialVanishing]; exact hk),
          ite_eq_right (by omega : ¬ k = n), ite_eq_right (by omega : ¬ k = 0)]
        exact (fr_sub_zero 0).symm
    rw [hbin_poly]
    -- Check coefficient by coefficient for every degree `j`.
    apply Polynomial.ext
    intro j
    set q := toeplitzQuotient f n c
    rw [Polynomial.coeff_add, coeff_coefficientPolynomial f, coeff_coefficientPolynomial remArr,
      mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow',
      mul_comm (coefficientPolynomial q) (Polynomial.C c),
      Polynomial.coeff_C_mul, coeff_coefficientPolynomial q]
    by_cases hj : j < n
    · -- Below `n`, `coeff_mul_X_pow'` is `0` and `remArr[j]` cancels `- c * q[j]!`.
      rw [ite_eq_right (by omega : ¬ n ≤ j),
        getElem!_pos remArr j (by simp [remArr, hj])]
      have hrem : remArr[j]'(by simp [remArr, hj]) = f[j]! + c * q[j]! := Array.getElem_ofFn _
      rw [hrem, show (coefficientPolynomial q).coeff j = q[j]! from coeff_coefficientPolynomial q j]
      refine ((sub_add_eq_add_sub (0 : Fr) (c * q[j]!) (f[j]! + c * q[j]!)).trans ?_).symm
      rw [fr_zero_add, fr_add_sub_cancel_right]
    · -- At or above `n`, `remArr[j]! = 0` and `q[j - n]! - c * q[j]!` telescopes to `f[j]!`.
      have hge : n ≤ j := Nat.le_of_not_gt hj
      rw [ite_eq_left hge, coeff_coefficientPolynomial q,
        getElem!_neg remArr j (by simp [remArr]; omega)]
      change f[j]! = q[j - n]! - c * q[j]! + 0
      rw [fr_add_zero]
      by_cases hjf : j < f.size
      · -- `j - n < f.size - n`, so `q[j - n]!` is in bounds.
        have hjn : j - n < f.size - n := by omega
        rw [getElem!_toeplitzQuotient f n c hjn]
        have hshifts_pos : 0 < (f.size + n - 1) / n - 1 :=
          shift_lt_shifts hn (t := j - n) (e := 0) (by omega)
        obtain ⟨m, hm⟩ : ∃ m, (f.size + n - 1) / n - 1 = m + 1 :=
          ⟨(f.size + n - 1) / n - 1 - 1, by omega⟩
        rw [hm, Finset.sum_range_succ', fr_pow_zero, fr_one_mul,
          show j - n + n * (0 + 1) = j by omega, ite_eq_left hjf]
        by_cases hj2 : j < f.size - n
        · -- Both `q[j - n]!` and `q[j]!` are in bounds, and the `e = m` term of `q[j]!` vanishes.
          rw [getElem!_toeplitzQuotient f n c hj2, hm, Finset.sum_range_succ]
          have htop_oob : ¬ (j + n * (m + 1) < f.size) := by
            intro hbad
            have hlt_s : m + 1 < (f.size + n - 1) / n - 1 :=
              shift_lt_shifts hn (t := j - n) (e := m + 1) (by rw [Nat.mul_succ]; omega)
            exact Nat.lt_irrefl (m + 1) (hm ▸ hlt_s)
          rw [ite_eq_right htop_oob, fr_add_zero, Finset.mul_sum]
          have hmatch :
              (∑ k ∈ Finset.range m,
                if j - n + n * (k + 1 + 1) < f.size then
                  c ^ (k + 1) * f[j - n + n * (k + 1 + 1)]!
                else 0) =
              ∑ x ∈ Finset.range m,
                c * (if j + n * (x + 1) < f.size then c ^ x * f[j + n * (x + 1)]! else 0) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hidx : j - n + n * (k + 1 + 1) = j + n * (k + 1) := by
              rw [Nat.mul_succ, Nat.mul_succ]
              omega
            rw [hidx]
            by_cases hk_in : j + n * (k + 1) < f.size
            · rw [ite_eq_left hk_in, ite_eq_left hk_in, fr_pow_succ,
                Bls.Fr.mul_comm (c ^ k) c, Bls.Fr.mul_assoc]
            · rw [ite_eq_right hk_in, ite_eq_right hk_in, fr_mul_zero]
          rw [hmatch]
          exact (fr_add_sub_cancel_left _ (f[j]!)).symm
        · -- Here `q[j]! = 0` and every shifted term `k + 1` in `q[j - n]!` is out of range.
          rw [getElem!_neg q j (by rw [size_toeplitzQuotient]; exact hj2)]
          change f[j]! = _ - c * 0
          rw [fr_mul_zero, fr_sub_zero]
          have htail :
              (∑ k ∈ Finset.range m,
                if j - n + n * (k + 1 + 1) < f.size then
                  c ^ (k + 1) * f[j - n + n * (k + 1 + 1)]!
                else 0) = 0 := by
            refine Finset.sum_eq_zero fun k _ => ?_
            have hidx : ¬ (j - n + n * (k + 1 + 1) < f.size) := by
              have : n * (k + 1 + 1) ≥ 2 * n := by
                have : 2 ≤ k + 1 + 1 := by omega
                calc 2 * n = n * 2 := Nat.mul_comm 2 n
                  _ ≤ n * (k + 1 + 1) := Nat.mul_le_mul_left n this
              omega
            rw [ite_eq_right hidx]
          rw [htail, fr_zero_add]
      · -- Above `f.size`, all three entries `f[j]!`, `q[j - n]!`, and `q[j]!` are zero.
        rw [getElem!_neg f j hjf,
          getElem!_neg q (j - n) (by rw [size_toeplitzQuotient]; omega),
          getElem!_neg q j (by rw [size_toeplitzQuotient]; omega)]
        change (0 : Fr) = 0 - c * 0
        rw [fr_mul_zero, fr_sub_zero]

/-- Exact size of `dividePolynomialcoeff a b` when `b` has a nonzero leading coefficient. -/
private theorem size_dividePolynomialcoeff {a b q : PolynomialCoeff}
    (hb : 0 < b.size) (h : dividePolynomialcoeff a b = .ok q) :
    q.size = if a.size < b.size then 0 else a.size + 1 - b.size := by
  by_cases hlt : a.size < b.size
  · rw [dividePolynomialcoeff_lt_size hlt] at h
    injection h with hq
    subst hq
    rw [ite_eq_left hlt]
    rfl
  · have hab : b.size ≤ a.size := Nat.le_of_not_lt hlt
    rw [ite_eq_right hlt]
    have hlead : b[b.size - 1]!.isZero = false := by
      cases hz : b[b.size - 1]!.isZero with
      | false => rfl
      | true =>
        rw [dividePolynomialcoeff_zero_divisor a b (Or.inr ⟨hab, hz⟩)] at h
        cases h
    have hb0 : ¬ b.size = 0 := by omega
    have hmax : max b.size 1 = b.size := by omega
    unfold dividePolynomialcoeff at h
    rw [ite_eq_right hb0, ite_eq_right hlt, ite_eq_right (by simp [hlead])] at h
    change Except.ok _ = Except.ok q at h
    injection h with hq
    subst hq
    let stepFn := fun (st : PolynomialCoeff × PolynomialCoeff) (t : Nat) =>
      let apos := st.1.size - 1 - t
      let diff := apos - (b.size - 1)
      let quot := st.1[apos]! * b[b.size - 1]!.inverse
      let a' := (Array.range b.size).foldl
        (fun a i => a.set! (diff + i) (a[diff + i]! - b[i]! * quot)) st.1
      (a', #[quot] ++ st.2)
    change ((Array.range (a.size + 1 - max b.size 1)).foldl stepFn (a, #[])).2.size = _
    rw [hmax, ← Array.foldl_toList, Array.toList_range]
    -- Each step of `List.range steps` prepends one element to `o`.
    suffices ∀ steps (init_a : PolynomialCoeff),
        (((List.range steps).foldl stepFn (init_a, #[])).2).size = steps by
      exact this (a.size + 1 - b.size) a
    intro steps init_a
    induction steps with
    | zero => rfl
    | succ s ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        stepFn, Array.size_append]
      rw [ih]
      simp [Nat.add_comm]

/-- Dividing `f` by `binomialVanishing n c` produces `toeplitzQuotient f n c`.

Evaluation agreement over `Fr` pins down polynomials of degree below `Fr.modulus`, so `f.size < Fr.modulus` suffices.
-/
theorem dividePolynomialcoeff_binomialVanishing {f : PolynomialCoeff} {n : Nat}
    (hn : 0 < n) (hf : f.size < Fr.modulus) (c : Fr) :
    dividePolynomialcoeff f (binomialVanishing n c) = .ok (toeplitzQuotient f n c) := by
  set b := binomialVanishing n c
  have hb_sz : b.size = n + 1 := size_binomialVanishing n c
  have hb_pos : 0 < b.size := by omega
  have hb_lead_one : b[b.size - 1]! = 1 := by
    rw [hb_sz, Nat.add_sub_cancel, getElem!_binomialVanishing n c n (by omega),
      ite_eq_right (Nat.ne_of_gt hn), ite_eq_left rfl]
    rfl
  have hb_lead_ne : b[b.size - 1]! ≠ 0 := by
    rw [hb_lead_one]; decide
  have hb_lead_isZero : b[b.size - 1]!.isZero = false := by
    rw [hb_lead_one]; decide
  by_cases hlt : f.size < b.size
  · rw [dividePolynomialcoeff_lt_size hlt]
    apply congrArg Except.ok
    have h0 : (toeplitzQuotient f n c).size = 0 := by
      rw [size_toeplitzQuotient]; omega
    exact (Array.size_eq_zero_iff.mp h0).symm
  · have hnf : n < f.size := by omega
    have hdiv_ok : ∃ q, dividePolynomialcoeff f b = .ok q := by
      have hb0 : ¬ b.size = 0 := by omega
      unfold dividePolynomialcoeff
      rw [ite_eq_right hb0, ite_eq_right hlt, ite_eq_right (by simp [hb_lead_isZero])]
      exact ⟨_, rfl⟩
    obtain ⟨q, hq⟩ := hdiv_ok
    rw [hq]
    apply congrArg Except.ok
    have hq_sz : q.size = f.size - n := by
      rw [size_dividePolynomialcoeff hb_pos hq, ite_eq_right hlt, hb_sz]
      omega
    obtain ⟨r₁, hr₁_eval, hr₁_deg_coeff⟩ :=
      dividePolynomialcoeff_quotient_remainder_spec hb_pos hb_lead_ne hq
    obtain ⟨r₂, hr₂_deg, hr₂_eq⟩ := coeff_toeplitzQuotient_mul_binomial f hn c
    -- Bound the degrees of `r_1`, `q * b`, and `f` strictly below `Fr.modulus`.
    have hr₁_deg_n : (coefficientPolynomial r₁).degree < (n : WithBot Nat) := by
      rcases eq_or_ne (coefficientPolynomial r₁) 0 with hr0 | hr0
      · rw [hr0, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe n
      · rw [Polynomial.degree_eq_natDegree hr0]
        refine WithBot.coe_lt_coe.mpr ?_
        by_contra hge
        have hge_n : n ≤ (coefficientPolynomial r₁).natDegree := Nat.le_of_not_lt hge
        have hge' : b.size - 1 ≤ (coefficientPolynomial r₁).natDegree := by
          rw [hb_sz, Nat.add_sub_cancel]
          exact hge_n
        have hcoeff0 : (coefficientPolynomial r₁).coeff (coefficientPolynomial r₁).natDegree = 0 := by
          rw [coeff_coefficientPolynomial]
          exact hr₁_deg_coeff _ hge'
        exact Polynomial.leadingCoeff_ne_zero.mpr hr0 hcoeff0
    have hcard_fr : Fintype.card Fr = Fr.modulus := ZMod.card Fr.modulus
    have hf_deg : (coefficientPolynomial f).degree < ((Finset.univ : Finset Fr).card : WithBot Nat) := by
      rw [Finset.card_univ, hcard_fr]
      rcases eq_or_ne (coefficientPolynomial f) 0 with hf0 | hf0
      · rw [hf0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
      · rw [Polynomial.degree_eq_natDegree hf0]
        exact WithBot.coe_lt_coe.mpr (Nat.lt_trans (natDegree_coefficientPolynomial_lt (by omega)) hf)
    have hqb_deg :
        (coefficientPolynomial q * coefficientPolynomial b + coefficientPolynomial r₁).degree <
          ((Finset.univ : Finset Fr).card : WithBot Nat) := by
      rw [Finset.card_univ, hcard_fr]
      have hmul_deg : (coefficientPolynomial q * coefficientPolynomial b).degree < (f.size : WithBot Nat) := by
        rcases eq_or_ne (coefficientPolynomial q) 0 with hq0 | hq0
        · rw [hq0, zero_mul, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe _
        · rcases eq_or_ne (coefficientPolynomial b) 0 with hb0' | hb0'
          · rw [hb0', mul_zero, Polynomial.degree_zero]
            exact WithBot.bot_lt_coe _
          · rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hq0,
              Polynomial.degree_eq_natDegree hb0']
            have hqd : (coefficientPolynomial q).natDegree < f.size - n :=
              hq_sz ▸ natDegree_coefficientPolynomial_lt (p := q) (by omega)
            have hbd : (coefficientPolynomial b).natDegree < n + 1 :=
              hb_sz ▸ natDegree_coefficientPolynomial_lt hb_pos
            have hsum_lt : (coefficientPolynomial q).natDegree + (coefficientPolynomial b).natDegree < f.size := by
              omega
            exact (WithBot.coe_add (coefficientPolynomial q).natDegree
              (coefficientPolynomial b).natDegree).symm ▸ WithBot.coe_lt_coe.mpr hsum_lt
      exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
        (max_lt (lt_trans hmul_deg (WithBot.coe_lt_coe.mpr hf))
          (lt_trans hr₁_deg_n (WithBot.coe_lt_coe.mpr (Nat.lt_trans hnf hf))))
    have hr₁_eq :
        coefficientPolynomial f =
          coefficientPolynomial q * coefficientPolynomial b + coefficientPolynomial r₁ := by
      refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := id) Finset.univ
        Function.injective_id.injOn hf_deg hqb_deg fun x _ => ?_
      dsimp only [id]
      rw [eval_coefficientPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        eval_coefficientPolynomial, eval_coefficientPolynomial, eval_coefficientPolynomial]
      exact hr₁_eval x
    -- Compare degrees in `(q - toeplitzQuotient) * b = r_2 - r_1`.
    have hb_deg_eq : (coefficientPolynomial b).degree = (n : WithBot Nat) := by
      have hle : (coefficientPolynomial b).degree ≤ (n : WithBot Nat) := by
        rcases eq_or_ne (coefficientPolynomial b) 0 with hb0' | hb0'
        · rw [hb0', Polynomial.degree_zero]; exact bot_le
        · rw [Polynomial.degree_eq_natDegree hb0']
          have hbd : (coefficientPolynomial b).natDegree < n + 1 :=
            hb_sz ▸ natDegree_coefficientPolynomial_lt hb_pos
          exact WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ hbd)
      have hge : (n : WithBot Nat) ≤ (coefficientPolynomial b).degree := by
        refine Polynomial.le_degree_of_ne_zero ?_
        rw [coeff_coefficientPolynomial, ← Nat.add_sub_cancel n 1, ← hb_sz]
        exact hb_lead_ne
      exact le_antisymm hle hge
    have hb_ne_zero : coefficientPolynomial b ≠ 0 := by
      intro h0
      rw [h0, Polynomial.degree_zero] at hb_deg_eq
      exact WithBot.bot_ne_coe hb_deg_eq
    have hdiff_mul :
        (coefficientPolynomial q - coefficientPolynomial (toeplitzQuotient f n c)) *
            coefficientPolynomial b =
          r₂ - coefficientPolynomial r₁ := by
      have h1 := hr₁_eq.symm.trans hr₂_eq
      linear_combination h1
    have hq_poly_eq :
        coefficientPolynomial q = coefficientPolynomial (toeplitzQuotient f n c) := by
      by_contra hne
      have hsub_ne : coefficientPolynomial q - coefficientPolynomial (toeplitzQuotient f n c) ≠ 0 :=
        sub_ne_zero.mpr hne
      have hlhs_ge : (n : WithBot Nat) ≤
          ((coefficientPolynomial q - coefficientPolynomial (toeplitzQuotient f n c)) *
            coefficientPolynomial b).degree := by
        rw [Polynomial.degree_mul, hb_deg_eq]
        have h0_le : (0 : WithBot Nat) ≤
            (coefficientPolynomial q - coefficientPolynomial (toeplitzQuotient f n c)).degree :=
          Polynomial.zero_le_degree_iff.mpr hsub_ne
        calc (n : WithBot Nat) = 0 + (n : WithBot Nat) := (zero_add _).symm
          _ ≤ (coefficientPolynomial q - coefficientPolynomial (toeplitzQuotient f n c)).degree +
                (n : WithBot Nat) := add_le_add h0_le le_rfl
      have hrhs_lt : (r₂ - coefficientPolynomial r₁).degree < (n : WithBot Nat) :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr₂_deg hr₁_deg_n)
      rw [hdiff_mul] at hlhs_ge
      exact not_lt_of_ge hlhs_ge hrhs_lt
    apply Array.ext (hq_sz.trans (size_toeplitzQuotient f n c).symm)
    intro i hi1 hi2
    rw [← getElem!_pos q i hi1, ← getElem!_pos (toeplitzQuotient f n c) i hi2,
      ← coeff_coefficientPolynomial, ← coeff_coefficientPolynomial, hq_poly_eq]

/-! ## FK20 quotient commitment equivalence -/

/-- Pure body of `computeCellsAndKzgProofsPolynomialcoeff`, parameterized by `setup`.

`Task.spawn` and `Task.get` reduce to the identity, so the `IO` wrapper binds `TrustedSetup.get!` into this function.
-/
def fk20CellsAndProofs (setup : TrustedSetup) (polynomialCoeff : PolynomialCoeff) :
    Array Cell × Array KZGProof :=
  let n := FIELD_ELEMENTS_PER_CELL
  let size := polynomialCoeff.size
  let cells := cellsOfExtendedEvaluations (extendedEvaluations polynomialCoeff)
  let shifts := (size + n - 1) / n - 1
  let proofs := (Task.spawn fun _ =>
    let tasks := (Array.range shifts).map fun e => Task.spawn fun _ =>
      let d := e + 1
      Bls.G1.msm (setup.g1Monomial.extract 0 (size - n * d)) (polynomialCoeff.extract (n * d) size)
    let hs := tasks.map Task.get
    let padded := hs ++ Array.replicate (CELLS_PER_EXT_BLOB - hs.size) Bls.G1.zero
    bitReversalPermutation (fftG1 padded (computeRootsOfUnity CELLS_PER_EXT_BLOB))).get
  (cells, proofs.map Bls.G1.compress)

/-- `computeCellsAndKzgProofsPolynomialcoeff` reads `TrustedSetup.get!` and returns `fk20CellsAndProofs`. -/
theorem computeCellsAndKzgProofsPolynomialcoeff_eq_bind (polynomialCoeff : PolynomialCoeff) :
    computeCellsAndKzgProofsPolynomialcoeff polynomialCoeff =
      (do
        let setup ← TrustedSetup.get!
        return fk20CellsAndProofs setup polynomialCoeff) :=
  rfl

/-- On a valid blob, `computeCellsAndKzgProofs` decodes `blob` and runs `fk20CellsAndProofs` on `TrustedSetup.get!`. -/
theorem computeCellsAndKzgProofs_ok_eq_bind {blob : Blob} {poly : Polynomial}
    (hblob : blobToPolynomial blob = .ok poly) :
    computeCellsAndKzgProofs blob =
      (do
        let setup ← TrustedSetup.get!
        return fk20CellsAndProofs setup (polynomialEvalToCoeff poly)) := by
  have hbsize : blob.size = BYTES_PER_BLOB := by
    by_contra hne
    have herr := (blobToPolynomial_error_badBlobSize blob blob.size).mpr ⟨hne, rfl⟩
    rw [hblob] at herr
    cases herr
  unfold computeCellsAndKzgProofs
  rw [ite_eq_right (not_not.mpr hbsize)]
  change (ExceptT.mk (pure (blobToPolynomial blob)) >>= fun polynomial =>
    computeCellsAndKzgProofsPolynomialcoeff (polynomialEvalToCoeff polynomial)) = _
  rw [hblob, bind_mk_ok]
  rfl

private theorem getElem!_extract {α : Type} [Inhabited α] (xs : Array α)
    (start stop i : Nat) (hstop : stop ≤ xs.size) (hi : i < stop - start) :
    (xs.extract start stop)[i]! = xs[start + i]! := by
  have hex : (xs.extract start stop).size = stop - start := by
    rw [Array.size_extract, Nat.min_eq_left hstop]
  have hi_ex : i < (xs.extract start stop).size := hex.symm ▸ hi
  have hi_xs : start + i < xs.size := by omega
  rw [getElem!_pos (xs.extract start stop) i hi_ex, Array.getElem_extract,
    getElem!_pos xs (start + i) hi_xs]

/-- Toeplitz-to-MSM identity in `G1`.

Let `hs[e]` commit to `f[t + n * (e + 1)]` against `pts[t]` for each `e < shifts`.

Padding `hs` with zeros to length `N` and summing `c^i * padded[i]` gives the MSM of `toeplitzQuotient f n c`.
-/
private theorem sum_padded_msm_eq_msm_toeplitz
    {pts : Array G1} {f : PolynomialCoeff} {n N : Nat}
    (hshifts_le : (f.size + n - 1) / n - 1 ≤ N)
    (hpts_sz : f.size - n ≤ pts.size)
    (hvalid : ∀ t < f.size - n, G1.Valid pts[t]!)
    (htor : ∀ t < f.size - n, Fr.modulus • G1.toPoint pts[t]! = 0)
    (c : Fr) :
    let shifts := (f.size + n - 1) / n - 1
    let hs := (Array.range shifts).map fun e =>
      Bls.G1.msm (pts.extract 0 (f.size - n * (e + 1))) (f.extract (n * (e + 1)) f.size)
    let padded := hs ++ Array.replicate (N - hs.size) G1.zero
    (∀ i < N, G1.Valid padded[i]!) ∧
    (∀ i < N, Fr.modulus • G1.toPoint padded[i]! = 0) ∧
    G1.Valid (Bls.G1.msm (pts.extract 0 (f.size - n)) (toeplitzQuotient f n c)) ∧
    (∑ i ∈ Finset.range N, (c ^ i).val • G1.toPoint padded[i]!) =
      G1.toPoint (Bls.G1.msm (pts.extract 0 (f.size - n)) (toeplitzQuotient f n c)) := by
  intro shifts hs padded
  have hhs_sz : hs.size = shifts := by
    simp [hs]
  have hpad_sz : padded.size = N := by
    rw [Array.size_append, hhs_sz, Array.size_replicate]
    omega
  -- Helper characterizing each shift MSM `hs[e]!`.
  have hhs_spec : ∀ e < shifts,
      G1.Valid hs[e]! ∧
      G1.toPoint hs[e]! =
        ∑ t ∈ Finset.range (f.size - n),
          (if t + n * (e + 1) < f.size then (f[t + n * (e + 1)]!).val else 0) •
            G1.toPoint pts[t]! := by
    intro e he
    let d := e + 1
    let L := f.size - n * d
    have hL_le_fn : L ≤ f.size - n := by
      have hnd : n ≤ n * d := Nat.le_mul_of_pos_right n (Nat.succ_pos e)
      omega
    have hL_le_pts : L ≤ pts.size := le_trans hL_le_fn hpts_sz
    have hex_pts_sz : (pts.extract 0 L).size = L := by
      rw [Array.size_extract]
      omega
    have hex_f_sz : (f.extract (n * d) f.size).size = L := by
      rw [Array.size_extract]
      omega
    have hmin_eq :
        (if (pts.extract 0 L).size ≤ (f.extract (n * d) f.size).size
          then (pts.extract 0 L).size
          else (f.extract (n * d) f.size).size) = L := by
      rw [hex_pts_sz, hex_f_sz, ite_eq_left le_rfl]
    have hget_hs : hs[e]! = Bls.G1.msm (pts.extract 0 L) (f.extract (n * d) f.size) := by
      rw [getElem!_pos hs e (hhs_sz ▸ he)]
      simp [hs, d, L]
    have hv_slice : ∀ t < (if (pts.extract 0 L).size ≤ (f.extract (n * d) f.size).size
        then (pts.extract 0 L).size else (f.extract (n * d) f.size).size),
        G1.Valid (pts.extract 0 L)[t]! := by
      intro t ht
      rw [hmin_eq] at ht
      rw [getElem!_extract pts 0 L t hL_le_pts (by omega), Nat.zero_add]
      exact hvalid t (lt_of_lt_of_le ht hL_le_fn)
    obtain ⟨hv_msm, hpt_msm⟩ := G1.toPoint_msm (pts.extract 0 L) (f.extract (n * d) f.size) hv_slice
    rw [hget_hs]
    refine ⟨hv_msm, ?_⟩
    rw [hpt_msm, hmin_eq]
    -- Rewrite each term in `range L` and pad `range L` up to `range (f.size - n)` with zeros.
    have hrewrite_L :
        (∑ t ∈ Finset.range L,
            ((f.extract (n * d) f.size)[t]!).val • G1.toPoint (pts.extract 0 L)[t]!) =
          ∑ t ∈ Finset.range L,
            (if t + n * d < f.size then (f[t + n * d]!).val else 0) • G1.toPoint pts[t]! := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_range] at ht
      have hlt_f : t + n * d < f.size := by omega
      rw [ite_eq_left hlt_f,
        getElem!_extract pts 0 L t hL_le_pts (by omega), Nat.zero_add,
        getElem!_extract f (n * d) f.size t le_rfl ht,
        show n * d + t = t + n * d by omega]
    rw [hrewrite_L]
    exact Finset.sum_subset (Finset.range_mono hL_le_fn) fun t ht hnot => by
      rw [Finset.mem_range] at ht hnot
      have hge_f : ¬ (t + n * d < f.size) := by omega
      rw [ite_eq_right hge_f, zero_nsmul]
  -- Validity of every padded entry.
  have hpad_valid : ∀ i < N, G1.Valid padded[i]! := by
    intro i hi
    rw [getElem!_pos padded i (hpad_sz ▸ hi)]
    by_cases his : i < shifts
    · rw [Array.getElem_append_left (hhs_sz ▸ his), ← getElem!_pos hs i (hhs_sz ▸ his)]
      exact (hhs_spec i his).1
    · rw [Array.getElem_append_right (by rw [hhs_sz]; omega), Array.getElem_replicate]
      exact G1.valid_zero
  -- Torsion of every padded entry.
  have hpad_tor : ∀ i < N, Fr.modulus • G1.toPoint padded[i]! = 0 := by
    intro i hi
    rw [getElem!_pos padded i (hpad_sz ▸ hi)]
    by_cases his : i < shifts
    · rw [Array.getElem_append_left (hhs_sz ▸ his), ← getElem!_pos hs i (hhs_sz ▸ his),
        (hhs_spec i his).2, Finset.smul_sum]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [Finset.mem_range] at ht
      rw [nsmul_left_comm, htor t ht, nsmul_zero]
    · rw [Array.getElem_append_right (by rw [hhs_sz]; omega), Array.getElem_replicate,
        G1.toPoint_zero, nsmul_zero]
  refine ⟨hpad_valid, hpad_tor, ?_⟩
  -- Truncate the sum from `range N` to `range shifts` since `padded[i] = G1.zero` above `shifts`.
  have htrunc :
      (∑ i ∈ Finset.range N, (c ^ i).val • G1.toPoint padded[i]!) =
        ∑ e ∈ Finset.range shifts, (c ^ e).val • G1.toPoint hs[e]! := by
    symm
    have hsub := Finset.sum_subset (Finset.range_mono hshifts_le)
      (f := fun i => (c ^ i).val • G1.toPoint padded[i]!) fun i hi hnot => by
        rw [Finset.mem_range] at hi hnot
        rw [getElem!_pos padded i (hpad_sz ▸ hi),
          Array.getElem_append_right (by rw [hhs_sz]; omega), Array.getElem_replicate,
          G1.toPoint_zero, nsmul_zero]
    refine (Finset.sum_congr rfl fun e he => ?_).trans hsub
    rw [Finset.mem_range] at he
    rw [getElem!_pos padded e (hpad_sz ▸ lt_of_lt_of_le he hshifts_le),
      Array.getElem_append_left (hhs_sz ▸ he), ← getElem!_pos hs e (hhs_sz ▸ he)]
  rw [htrunc]
  -- Expand `G1.toPoint hs[e]!`, distribute `(c^e).val`, and swap the two sums.
  have hexpand :
      (∑ e ∈ Finset.range shifts, (c ^ e).val • G1.toPoint hs[e]!) =
        ∑ e ∈ Finset.range shifts,
          ∑ t ∈ Finset.range (f.size - n),
            (if t + n * (e + 1) < f.size then c ^ e * f[t + n * (e + 1)]! else 0).val •
              G1.toPoint pts[t]! := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_range] at he
    rw [(hhs_spec e he).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    by_cases hlt : t + n * (e + 1) < f.size
    · rw [ite_eq_left hlt, ite_eq_left hlt, ← nsmul_val_mul_of_torsion (htor t ht)]
    · rw [ite_eq_right hlt, ite_eq_right hlt, zero_nsmul, nsmul_zero]
      exact (zero_nsmul _).symm
  rw [hexpand, Finset.sum_comm]
  -- Collapse the inner `e` sum into `(toeplitzQuotient f n c)[t]!` via `r`-torsion linearity.
  have hcollapse :
      (∑ t ∈ Finset.range (f.size - n),
          ∑ e ∈ Finset.range shifts,
            (if t + n * (e + 1) < f.size then c ^ e * f[t + n * (e + 1)]! else 0).val •
              G1.toPoint pts[t]!) =
        ∑ t ∈ Finset.range (f.size - n),
          ((toeplitzQuotient f n c)[t]!).val • G1.toPoint pts[t]! := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    rw [getElem!_toeplitzQuotient f n c ht]
    have hsum_val : ∀ (m : Nat) (g : Nat → Fr),
        (∑ e ∈ Finset.range m, (g e).val • G1.toPoint pts[t]!) =
          (∑ e ∈ Finset.range m, g e).val • G1.toPoint pts[t]! := by
      intro m g
      induction m with
      | zero =>
        rw [Finset.range_zero, Finset.sum_empty, Finset.sum_empty]
        exact (zero_nsmul _).symm
      | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
          ← nsmul_val_add_of_torsion (htor t ht)]
    exact hsum_val shifts _
  rw [hcollapse]
  -- Match the RHS `G1.toPoint (Bls.G1.msm (pts.extract 0 (f.size - n)) (toeplitzQuotient f n c))`.
  have hex0_sz : (pts.extract 0 (f.size - n)).size = f.size - n := by
    rw [Array.size_extract]; omega
  have hq_sz : (toeplitzQuotient f n c).size = f.size - n := size_toeplitzQuotient f n c
  have hmin0 :
      (if (pts.extract 0 (f.size - n)).size ≤ (toeplitzQuotient f n c).size
        then (pts.extract 0 (f.size - n)).size
        else (toeplitzQuotient f n c).size) = f.size - n := by
    rw [hex0_sz, hq_sz, ite_eq_left le_rfl]
  have hv0 : ∀ t < (if (pts.extract 0 (f.size - n)).size ≤ (toeplitzQuotient f n c).size
      then (pts.extract 0 (f.size - n)).size
      else (toeplitzQuotient f n c).size),
      G1.Valid (pts.extract 0 (f.size - n))[t]! := by
    intro t ht
    rw [hmin0] at ht
    rw [getElem!_extract pts 0 (f.size - n) t hpts_sz (by omega), Nat.zero_add]
    exact hvalid t ht
  obtain ⟨hv_msm0, hpt0⟩ := G1.toPoint_msm (pts.extract 0 (f.size - n)) (toeplitzQuotient f n c) hv0
  refine ⟨hv_msm0, ?_⟩
  rw [hpt0, hmin0]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [getElem!_extract pts 0 (f.size - n) t hpts_sz (by omega), Nat.zero_add]

/-- With at most `FIELD_ELEMENTS_PER_EXT_BLOB` coefficients, FK20 needs at most `CELLS_PER_EXT_BLOB` shifts. -/
private theorem shifts_le_cells_per_ext_blob {sz : Nat}
    (hsz : sz ≤ FIELD_ELEMENTS_PER_EXT_BLOB) :
    (sz + FIELD_ELEMENTS_PER_CELL - 1) / FIELD_ELEMENTS_PER_CELL - 1 ≤ CELLS_PER_EXT_BLOB := by
  have hbound : sz ≤ 8192 := hsz
  show (sz + 64 - 1) / 64 - 1 ≤ 128
  omega

/-- `fk20CellsAndProofs` outputs 128 cells and 128 proofs when `polynomialCoeff.size <= FIELD_ELEMENTS_PER_EXT_BLOB`. -/
theorem size_fk20CellsAndProofs (setup : TrustedSetup) {polynomialCoeff : PolynomialCoeff}
    (hp : polynomialCoeff.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB) :
    (fk20CellsAndProofs setup polynomialCoeff).1.size = CELLS_PER_EXT_BLOB ∧
    (fk20CellsAndProofs setup polynomialCoeff).2.size = CELLS_PER_EXT_BLOB := by
  refine ⟨size_cellsOfExtendedEvaluations _, ?_⟩
  have hshifts_le := shifts_le_cells_per_ext_blob hp
  dsimp only [fk20CellsAndProofs]
  rw [Array.size_map]
  change (bitReversalPermutation (fftG1 _ (computeRootsOfUnity CELLS_PER_EXT_BLOB))).size =
    CELLS_PER_EXT_BLOB
  rw [size_bitReversalPermutation, size_fftG1, Array.size_append, Array.size_replicate]
  simp only [Array.size_map, Array.size_range]
  omega

/-- `fk20CellsAndProofs` matches the Fulu per-cell specification on every cell.

Assume `polynomialCoeff.size <= FIELD_ELEMENTS_PER_EXT_BLOB`.

Assume `setup.g1Monomial` holds at least `polynomialCoeff.size - FIELD_ELEMENTS_PER_CELL` valid `r`-torsion points.

Then for every cell `cosetForCell cellIndex = .ok coset`:

- `vanishingPolynomialcoeff coset` returns `vanishing`.
- `dividePolynomialcoeff polynomialCoeff vanishing` returns `quotient`.
- `g1LincombPoints` on `setup.g1Monomial.extract 0 quotient.size` and `quotient` returns `Bls.G1.msm`.
- Cell `cellIndex` equals `cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff))`.
- Proof `cellIndex` equals `Bls.G1.compress (Bls.G1.msm (setup.g1Monomial.extract 0 quotient.size) quotient)`.
-/
theorem fk20CellsAndProofs_eq_perCellSpec
    {setup : TrustedSetup} {polynomialCoeff : PolynomialCoeff}
    {cellIndex : CellIndex} {coset : Coset}
    (hp : polynomialCoeff.size ≤ FIELD_ELEMENTS_PER_EXT_BLOB)
    (hsetup_sz : polynomialCoeff.size - FIELD_ELEMENTS_PER_CELL ≤ setup.g1Monomial.size)
    (hsetup_valid : ∀ t < polynomialCoeff.size - FIELD_ELEMENTS_PER_CELL,
      G1.Valid setup.g1Monomial[t]!)
    (hsetup_tor : ∀ t < polynomialCoeff.size - FIELD_ELEMENTS_PER_CELL,
      Fr.modulus • G1.toPoint setup.g1Monomial[t]! = 0)
    (hcoset : cosetForCell cellIndex = .ok coset) :
    ∃ vanishing quotient,
      vanishingPolynomialcoeff coset = .ok vanishing ∧
      dividePolynomialcoeff polynomialCoeff vanishing = .ok quotient ∧
      g1LincombPoints (setup.g1Monomial.extract 0 quotient.size) quotient =
        pure (Bls.G1.msm (setup.g1Monomial.extract 0 quotient.size) quotient) ∧
      (fk20CellsAndProofs setup polynomialCoeff).1[cellIndex]! =
        cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff)) ∧
      (fk20CellsAndProofs setup polynomialCoeff).2[cellIndex]! =
        Bls.G1.compress (Bls.G1.msm (setup.g1Monomial.extract 0 quotient.size) quotient) := by
  have hci : cellIndex < CELLS_PER_EXT_BLOB := cosetForCell_ok_iff.mp ⟨coset, hcoset⟩
  let n := FIELD_ELEMENTS_PER_CELL
  let N := CELLS_PER_EXT_BLOB
  let r := reverseBits cellIndex N
  let ω := domainRoot N
  let c := (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[n * cellIndex]! ^ n
  have hn_pos : 0 < n := by decide
  have hf_mod : polynomialCoeff.size < Fr.modulus :=
    lt_of_le_of_lt hp (by decide : FIELD_ELEMENTS_PER_EXT_BLOB < Fr.modulus)
  have hshifts_le : (polynomialCoeff.size + n - 1) / n - 1 ≤ N :=
    shifts_le_cells_per_ext_blob hp
  have hq_sz : (toeplitzQuotient polynomialCoeff n c).size = polynomialCoeff.size - n :=
    size_toeplitzQuotient polynomialCoeff n c
  have hex_sz : (setup.g1Monomial.extract 0 (toeplitzQuotient polynomialCoeff n c).size).size =
      (toeplitzQuotient polynomialCoeff n c).size := by
    rw [Array.size_extract, hq_sz, Nat.min_eq_left hsetup_sz, Nat.sub_zero]
  -- Witness `vanishing` and `quotient` from the algebraic characterizations proved above.
  refine ⟨binomialVanishing n c, toeplitzQuotient polynomialCoeff n c,
    vanishingPolynomialcoeff_cosetForCell hcoset,
    dividePolynomialcoeff_binomialVanishing hn_pos hf_mod c,
    g1LincombPoints_eq_msm hex_sz,
    getElem!_cellsOfExtendedEvaluations_extendedEvaluations hp hcoset, ?_⟩
  -- Unpack the spawned tasks inside `fk20CellsAndProofs`.
  let shifts := (polynomialCoeff.size + n - 1) / n - 1
  let hs := (Array.range shifts).map fun e =>
    Bls.G1.msm (setup.g1Monomial.extract 0 (polynomialCoeff.size - n * (e + 1)))
      (polynomialCoeff.extract (n * (e + 1)) polynomialCoeff.size)
  let padded := hs ++ Array.replicate (N - hs.size) Bls.G1.zero
  have htasks_eq :
      (((Array.range shifts).map fun e => Task.spawn fun _ =>
        Bls.G1.msm (setup.g1Monomial.extract 0 (polynomialCoeff.size - n * (e + 1)))
          (polynomialCoeff.extract (n * (e + 1)) polynomialCoeff.size)).map Task.get) = hs := by
    rw [Array.map_map]
    rfl
  have hproofs_eq :
      (fk20CellsAndProofs setup polynomialCoeff).2 =
        (bitReversalPermutation (fftG1 padded (computeRootsOfUnity N))).map Bls.G1.compress := by
    dsimp only [fk20CellsAndProofs]
    change (bitReversalPermutation (fftG1 _ (computeRootsOfUnity N))).map Bls.G1.compress = _
    rw [htasks_eq]
  -- Relate `c` to `omega^r`.
  have hr_lt : r < N := reverseBits_lt_two_pow cellIndex 7
  have hc_eq_ωr : c = ω ^ r := by
    have hc_root := cosetShift_pow_cell cellIndex hci
    rw [show c = _ from hc_root,
      getElem!_pos (computeRootsOfUnity N) r (by rw [size_computeRootsOfUnity]; exact hr_lt),
      getElem_computeRootsOfUnity]
  -- Apply `sum_padded_msm_eq_msm_toeplitz`.
  obtain ⟨hpad_valid, hpad_tor, hv_msm_q, hsum_eq⟩ :=
    sum_padded_msm_eq_msm_toeplitz (pts := setup.g1Monomial) (f := polynomialCoeff)
      (n := n) (N := N) hshifts_le hsetup_sz hsetup_valid hsetup_tor c
  have hpad_sz : padded.size = 2 ^ 7 := by
    have hhs_sz : hs.size = shifts := by simp [hs]
    have hN2 : N = 2 ^ 7 := rfl
    rw [Array.size_append, hhs_sz, Array.size_replicate, ← hN2]
    omega
  have hroots_sz : (computeRootsOfUnity N).size = 2 ^ 7 := by
    rw [size_computeRootsOfUnity]; rfl
  have hω_prim : IsPrimitiveRoot ω (2 ^ 7) :=
    isPrimitiveRoot_domainRoot (Nat.dvd_of_mod_eq_zero (by decide) : 2 ^ 7 ∣ BLS_MODULUS - 1)
  have hroots_elem : ∀ i < 2 ^ 7, (computeRootsOfUnity N)[i]! = ω ^ i := by
    intro i hi
    rw [getElem!_pos (computeRootsOfUnity N) i (hroots_sz ▸ hi), getElem_computeRootsOfUnity]
  have hr_lt7 : r < 2 ^ 7 := hr_lt
  -- Validity and `toPoint` of `(fftG1 padded (computeRootsOfUnity N))[r]!`.
  have hv_fft : G1.Valid (fftG1 padded (computeRootsOfUnity N))[r]! :=
    valid_getElem!_fftG1 padded (computeRootsOfUnity N) hpad_sz hpad_valid r hr_lt7
  have hpt_fft : G1.toPoint (fftG1 padded (computeRootsOfUnity N))[r]! =
      G1.toPoint (Bls.G1.msm (setup.g1Monomial.extract 0 (polynomialCoeff.size - n))
        (toeplitzQuotient polynomialCoeff n c)) := by
    rw [toPoint_getElem!_fftG1 hω_prim padded (computeRootsOfUnity N)
      hpad_sz hroots_sz hroots_elem hpad_valid hpad_tor r hr_lt7]
    have hpow_rw :
        (∑ i ∈ Finset.range (2 ^ 7), (ω ^ (i * r)).val • G1.toPoint padded[i]!) =
          ∑ i ∈ Finset.range N, (c ^ i).val • G1.toPoint padded[i]! := by
      change (∑ i ∈ Finset.range N, (ω ^ (i * r)).val • G1.toPoint padded[i]!) = _
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.mul_comm i r, fr_pow_mul, ← hc_eq_ωr]
    exact hpow_rw.trans hsum_eq
  -- Index into `(bitReversalPermutation (fftG1 ...)).map Bls.G1.compress`.
  set fftOut := fftG1 padded (computeRootsOfUnity N)
  have hfft_sz : fftOut.size = N := by
    rw [size_fftG1, hpad_sz]; rfl
  have hbrp_sz : (bitReversalPermutation fftOut).size = N := by
    rw [size_bitReversalPermutation, hfft_sz]
  have hci_brp : cellIndex < (bitReversalPermutation fftOut).size := hbrp_sz.symm ▸ hci
  have hci_fft : cellIndex < fftOut.size := hfft_sz.symm ▸ hci
  have hget_proof :
      (fk20CellsAndProofs setup polynomialCoeff).2[cellIndex]! =
        Bls.G1.compress fftOut[r]! := by
    rw [hproofs_eq,
      getElem!_pos _ cellIndex (by rw [Array.size_map]; exact hci_brp),
      Array.getElem_map,
      ← getElem!_pos (bitReversalPermutation fftOut) cellIndex hci_brp,
      getElem!_bitReversalPermutation fftOut cellIndex hci_fft,
      hfft_sz]
  rw [hget_proof, hq_sz]
  exact compress_eq_of_toPoint_eq hv_fft hv_msm_q hpt_fft

/-- Specialization of `fk20CellsAndProofs_eq_perCellSpec` to decoded blobs.

When `blobToPolynomial blob = .ok poly`, `polynomialEvalToCoeff poly` has `4096` coefficients.

Every cell and proof returned by `computeCellsAndKzgProofs` then matches the Fulu per-cell specification.
-/
theorem computeCellsAndKzgProofs_blob_spec
    {setup : TrustedSetup} {blob : Blob} {poly : Polynomial}
    {cellIndex : CellIndex} {coset : Coset}
    (hblob : blobToPolynomial blob = .ok poly)
    (hsetup_sz : FIELD_ELEMENTS_PER_BLOB - FIELD_ELEMENTS_PER_CELL ≤ setup.g1Monomial.size)
    (hsetup_valid : ∀ t < FIELD_ELEMENTS_PER_BLOB - FIELD_ELEMENTS_PER_CELL,
      G1.Valid setup.g1Monomial[t]!)
    (hsetup_tor : ∀ t < FIELD_ELEMENTS_PER_BLOB - FIELD_ELEMENTS_PER_CELL,
      Fr.modulus • G1.toPoint setup.g1Monomial[t]! = 0)
    (hcoset : cosetForCell cellIndex = .ok coset) :
    let polynomialCoeff := polynomialEvalToCoeff poly
    ∃ vanishing quotient,
      vanishingPolynomialcoeff coset = .ok vanishing ∧
      dividePolynomialcoeff polynomialCoeff vanishing = .ok quotient ∧
      g1LincombPoints (setup.g1Monomial.extract 0 quotient.size) quotient =
        pure (Bls.G1.msm (setup.g1Monomial.extract 0 quotient.size) quotient) ∧
      (fk20CellsAndProofs setup polynomialCoeff).1[cellIndex]! =
        cosetEvalsToCell (coset.map (evaluatePolynomialcoeff polynomialCoeff)) ∧
      (fk20CellsAndProofs setup polynomialCoeff).2[cellIndex]! =
        Bls.G1.compress (Bls.G1.msm (setup.g1Monomial.extract 0 quotient.size) quotient) := by
  intro polynomialCoeff
  have hp_sz : polynomialCoeff.size = FIELD_ELEMENTS_PER_BLOB := by
    rw [size_polynomialEvalToCoeff, size_blobToPolynomial blob poly hblob]
  exact fk20CellsAndProofs_eq_perCellSpec
    (hp_sz ▸ (by decide : FIELD_ELEMENTS_PER_BLOB ≤ FIELD_ELEMENTS_PER_EXT_BLOB))
    (hp_sz.symm ▸ hsetup_sz)
    (hp_sz.symm ▸ hsetup_valid)
    (hp_sz.symm ▸ hsetup_tor)
    hcoset

/-! ## End-to-end cell and proof recovery -/

private theorem list_mapM_ok_mem_and_len {cs : List Cell} {es : List CosetEvals}
    (h : cs.mapM cellToCosetEvals = .ok es) :
    es.length = cs.length ∧ ∀ c ∈ cs, ∃ y, cellToCosetEvals c = .ok y := by
  induction cs generalizing es with
  | nil =>
    have hnil : ([] : List Cell).mapM cellToCosetEvals = .ok [] := rfl
    rw [hnil] at h
    injection h with h'
    subst h'
    exact ⟨rfl, fun _ hc => nomatch hc⟩
  | cons hd tl ih =>
    rw [List.mapM_cons] at h
    cases hhd : cellToCosetEvals hd with
    | error e =>
      rw [hhd] at h
      cases h
    | ok y =>
      rw [hhd] at h
      cases htl : tl.mapM cellToCosetEvals with
      | error e =>
        rw [htl] at h
        cases h
      | ok ys =>
        rw [htl] at h
        injection h with h'
        subst h'
        obtain ⟨hlen_tl, hmem_tl⟩ := ih htl
        refine ⟨by simp [hlen_tl], fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc_tl
        · exact ⟨y, hhd⟩
        · exact hmem_tl c hc_tl

private theorem mapM_lift_cellToCosetEvals {cells : Array Cell} {cosetsEvals : Array CosetEvals}
    (hdec : cells.mapM cellToCosetEvals = .ok cosetsEvals) :
    (cells.mapM fun c => (cellToCosetEvals c : KzgM CosetEvals)) = pure cosetsEvals := by
  rw [Array.mapM_eq_mapM_toList] at hdec
  obtain ⟨es, hes, rfl⟩ : ∃ es, cells.toList.mapM cellToCosetEvals = .ok es ∧ es.toArray = cosetsEvals := by
    cases hm : cells.toList.mapM cellToCosetEvals with
    | error e =>
      rw [hm] at hdec
      cases hdec
    | ok es =>
      rw [hm] at hdec
      exact ⟨es, rfl, Except.ok.inj hdec⟩
  unfold Array.mapM
  suffices ∀ (i : Nat) (acc : Array CosetEvals) (rem : List Cell) (out : List CosetEvals),
      cells.toList.drop i = rem →
      rem.mapM cellToCosetEvals = .ok out →
      Array.mapM.map (fun c => (cellToCosetEvals c : KzgM CosetEvals)) cells i acc =
        pure (acc ++ out.toArray) by
    simpa using this 0 (Array.emptyWithCapacity cells.size) cells.toList es (by simp) hes
  intro i acc rem
  induction rem generalizing i acc with
  | nil =>
    intro out hdrop hrem
    have hnil : ([] : List Cell).mapM cellToCosetEvals = .ok [] := rfl
    rw [hnil] at hrem
    injection hrem with h'
    subst h'
    have hge : ¬ i < cells.size := by
      intro hlt
      have hlen := congrArg List.length hdrop
      simp [Array.length_toList] at hlen
      omega
    rw [Array.mapM.map.eq_1, dite_eq_right hge]
    simp
  | cons hd tl ih =>
    intro out hdrop hrem
    have hlt : i < cells.size := by
      by_contra hge
      have hlen := congrArg List.length hdrop
      simp [Array.length_toList] at hlen
      omega
    have hhd_eq : cells[i] = hd := by
      have hget : (cells.toList.drop i)[0]? = (hd :: tl)[0]? := congrArg (·[0]?) hdrop
      rw [List.getElem?_drop, Nat.add_zero, Array.getElem?_toList,
        Array.getElem?_eq_getElem hlt] at hget
      exact Option.some.inj hget
    have hdrop_next : cells.toList.drop (i + 1) = tl := by
      rw [← List.drop_drop, hdrop]
      rfl
    rw [List.mapM_cons] at hrem
    cases hhd : cellToCosetEvals hd with
    | error e =>
      rw [hhd] at hrem
      cases hrem
    | ok y =>
      rw [hhd] at hrem
      cases htl : tl.mapM cellToCosetEvals with
      | error e =>
        rw [htl] at hrem
        cases hrem
      | ok ys =>
        rw [htl] at hrem
        injection hrem with h'
        subst h'
        rw [Array.mapM.map.eq_1, dite_eq_left hlt, hhd_eq]
        have hstep : (cellToCosetEvals hd : KzgM CosetEvals) = ExceptT.mk (pure (.ok y)) := by
          rw [hhd]
          rfl
        rw [hstep, bind_mk_ok]
        change Array.mapM.map (fun c => (cellToCosetEvals c : KzgM CosetEvals)) cells (i + 1)
          (acc.push y) = pure (acc ++ (y :: ys).toArray)
        rw [ih (i + 1) (acc.push y) ys hdrop_next htl]
        congr 1
        apply Array.ext'
        simp [Array.toList_append]

private theorem nodup_of_ascending {xs : Array Nat}
    (hasc : (Array.range (xs.size - 1)).any (fun i => xs[i + 1]! ≤ xs[i]!) = false) :
    xs.toList.Nodup := by
  have hstep : ∀ i, i + 1 < xs.size → xs[i]! < xs[i + 1]! := by
    intro i hi
    by_contra hge
    have hle : xs[i + 1]! ≤ xs[i]! := Nat.le_of_not_lt hge
    have hany : (Array.range (xs.size - 1)).any (fun k => xs[k + 1]! ≤ xs[k]!) = true := by
      rw [Array.any_eq_true]
      refine ⟨i, by simp; omega, ?_⟩
      rw [Array.getElem_range]
      exact decide_eq_true hle
    rw [hasc] at hany
    cases hany
  -- Strict monotonicity across adjacent indices implies `xs[i]! < xs[j]!` for `i < j < xs.size`.
  have hlt_all : ∀ i j, i < j → j < xs.size → xs[i]! < xs[j]! := by
    intro i j hij hj
    obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - (i + 1), by omega⟩
    induction d with
    | zero =>
      exact hstep i hj
    | succ d ih =>
      have hprev := ih (by omega) (by omega)
      have hnext := hstep (i + 1 + d) (by omega)
      have hidx : i + 1 + (d + 1) = i + 1 + d + 1 := by omega
      rw [hidx]
      exact Nat.lt_trans hprev hnext
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj heq
  have hj_sz : j < xs.size := by simpa [Array.length_toList] using hj
  have hi_sz : i < xs.size := Nat.lt_trans hij hj_sz
  have hi : i < xs.toList.length := Nat.lt_trans hij hj
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.some.injEq] at heq
  have heq_bang : xs[i]! = xs[j]! := by
    rw [getElem!_pos xs i hi_sz, getElem!_pos xs j hj_sz]
    simpa using heq
  exact Nat.ne_of_lt (hlt_all i j hij hj_sz) heq_bang

/-- On valid samples of a blob polynomial `p`, `recoverCellsAndKzgProofs` runs `fk20CellsAndProofs setup p`. -/
theorem recoverCellsAndKzgProofs_ok_eq_bind
    {p : PolynomialCoeff} {cellIndices : Array CellIndex}
    {cells : Array Cell} {cosetsEvals : Array CosetEvals}
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hlen : cells.size = cellIndices.size)
    (hmin : CELLS_PER_EXT_BLOB / 2 ≤ cellIndices.size)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hasc : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = false)
    (hdec : cells.mapM cellToCosetEvals = .ok cosetsEvals)
    (hmatch : RecoverySamplesMatch p cellIndices cosetsEvals) :
    recoverCellsAndKzgProofs cellIndices cells =
      (do
        let setup ← TrustedSetup.get!
        return fk20CellsAndProofs setup p) := by
  have hnd : cellIndices.toList.Nodup := nodup_of_ascending hasc
  have hbound_mem : ∀ ci ∈ cellIndices.toList, ci < CELLS_PER_EXT_BLOB := by
    intro ci hci
    by_contra hge
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hci
    have hany : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true := by
      rw [Array.any_eq_true]
      exact ⟨idx, by simpa using hidx, decide_eq_true (Nat.le_of_not_lt hge)⟩
    rw [hbound] at hany
    cases hany
  have hmax : cellIndices.size ≤ CELLS_PER_EXT_BLOB := by
    have hsum := recoveryMissing_size_add_size cellIndices hnd hbound_mem
    omega
  have hlist_ok : ∃ es, cells.toList.mapM cellToCosetEvals = .ok es ∧ es.toArray = cosetsEvals := by
    have hdec' := hdec
    rw [Array.mapM_eq_mapM_toList] at hdec'
    cases hm : cells.toList.mapM cellToCosetEvals with
    | error e => rw [hm] at hdec'; cases hdec'
    | ok es => rw [hm] at hdec'; exact ⟨es, rfl, Except.ok.inj hdec'⟩
  obtain ⟨es, hes, hes_arr⟩ := hlist_ok
  obtain ⟨hlen_es, hmem_es⟩ := list_mapM_ok_mem_and_len hes
  have hfind : cells.find? (fun c => c.size != BYTES_PER_CELL) = none := by
    rw [Array.find?_eq_none]
    intro c hc
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hc
    obtain ⟨y, hy⟩ := hmem_es cells[k] (Array.getElem_mem_toList hk)
    by_contra hbad
    have hne : cells[k].size ≠ BYTES_PER_CELL := by simpa using hbad
    rw [cellToCosetEvals, ite_eq_left hne] at hy
    cases hy
  have hcosets_len : cosetsEvals.size = cellIndices.size := by
    rw [← hes_arr, List.size_toArray, hlen_es, Array.length_toList, hlen]
  have hrec : recoverPolynomialcoeff cellIndices cosetsEvals = .ok p :=
    recoverPolynomialcoeff_correct_of_valid_indices hp hcosets_len hnd hbound_mem hmin hmatch
  unfold recoverCellsAndKzgProofs
  rw [ite_eq_right (not_not.mpr hlen),
    ite_eq_right (Nat.not_lt.mpr hmin),
    ite_eq_right (Nat.not_lt.mpr hmax),
    ite_eq_right (by simp [hbound]),
    ite_eq_right (by simpa [Array.size_range] using hasc)]
  simp only [hfind, mapM_lift_cellToCosetEvals hdec, pure_bind]
  change (ExceptT.mk (pure (recoverPolynomialcoeff cellIndices cosetsEvals)) >>=
    computeCellsAndKzgProofsPolynomialcoeff) = _
  rw [hrec, bind_mk_ok]
  rfl

/-- End-to-end recovery specification for `recoverCellsAndKzgProofs`.

With at least 64 strictly ascending valid cells of `p`, it reconstructs all 128 cells and proofs of `p`.

Each recovered cell and proof satisfies the Fulu per-cell quotient commitment specification.
-/
theorem recoverCellsAndKzgProofs_spec
    {setup : TrustedSetup} {p : PolynomialCoeff}
    {cellIndices : Array CellIndex} {cells : Array Cell} {cosetsEvals : Array CosetEvals}
    {cellIndex : CellIndex} {coset : Coset}
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hlen : cells.size = cellIndices.size)
    (hmin : CELLS_PER_EXT_BLOB / 2 ≤ cellIndices.size)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hasc : (Array.range (cellIndices.size - 1)).any
      (fun i => cellIndices[i + 1]! ≤ cellIndices[i]!) = false)
    (hdec : cells.mapM cellToCosetEvals = .ok cosetsEvals)
    (hmatch : RecoverySamplesMatch p cellIndices cosetsEvals)
    (hsetup_sz : FIELD_ELEMENTS_PER_BLOB - FIELD_ELEMENTS_PER_CELL ≤ setup.g1Monomial.size)
    (hsetup_valid : ∀ t < FIELD_ELEMENTS_PER_BLOB - FIELD_ELEMENTS_PER_CELL,
      G1.Valid setup.g1Monomial[t]!)
    (hsetup_tor : ∀ t < FIELD_ELEMENTS_PER_BLOB - FIELD_ELEMENTS_PER_CELL,
      Fr.modulus • G1.toPoint setup.g1Monomial[t]! = 0)
    (hcoset : cosetForCell cellIndex = .ok coset) :
    recoverCellsAndKzgProofs cellIndices cells =
      (do
        let setup ← TrustedSetup.get!
        return fk20CellsAndProofs setup p) ∧
    ∃ vanishing quotient,
      vanishingPolynomialcoeff coset = .ok vanishing ∧
      dividePolynomialcoeff p vanishing = .ok quotient ∧
      g1LincombPoints (setup.g1Monomial.extract 0 quotient.size) quotient =
        pure (Bls.G1.msm (setup.g1Monomial.extract 0 quotient.size) quotient) ∧
      (fk20CellsAndProofs setup p).1[cellIndex]! =
        cosetEvalsToCell (coset.map (evaluatePolynomialcoeff p)) ∧
      (fk20CellsAndProofs setup p).2[cellIndex]! =
        Bls.G1.compress (Bls.G1.msm (setup.g1Monomial.extract 0 quotient.size) quotient) :=
  ⟨recoverCellsAndKzgProofs_ok_eq_bind hp hlen hmin hbound hasc hdec hmatch,
   fk20CellsAndProofs_eq_perCellSpec
     (hp ▸ (by decide : FIELD_ELEMENTS_PER_BLOB ≤ FIELD_ELEMENTS_PER_EXT_BLOB))
     (hp.symm ▸ hsetup_sz)
     (hp.symm ▸ hsetup_valid)
     (hp.symm ▸ hsetup_tor)
     hcoset⟩

end EthLib.Cryptography.Kzg
