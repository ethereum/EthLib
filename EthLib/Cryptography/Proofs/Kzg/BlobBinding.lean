module

public import EthLib.Cryptography.Proofs.Kzg.Verify

/-!
# Proofs: an accepted blob opening binds its blob, or names a root

Let the check of a blob opening accept on a well-formed setup.

Let its commitment and proof represent `f(τ)` and `g(τ)`, for `f` and `g` of degree below 4096.

Let `p` be the interpolant of the blob's decoded values, and `z` the evaluation challenge.

Then one of three cases holds, and the cases can overlap:

- `f = p`;
- or `f ≠ p`, `f - p` has degree below 4096, and `z` is a root of `f - p`;
- or `h = f - p(z) - g (X - z)` is nonzero of degree at most 4096, and `τ` is a root of `h`.

The cases carry meaning only when an algebraic adversary outputs `f` and `g` without `τ`.

For other choices, such as constants, the third case only restates the check.

No theorem here bounds the cost of finding such polynomials when `τ` is secret.

The algebraic group model is that of Fuchsbauer, Kiltz and Loss, CRYPTO 2018:

<https://eprint.iacr.org/2017/620>

The scheme is PolyCommit_DL, §3.2 of Kate, Zaverucha and Goldberg, ASIACRYPT 2010:

<https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-- The error polynomial of an opening: `f - y - g (X - z)`.

The commitment reads as `f` at the secret, and the proof reads as `g`.

In a blob opening, `y` is the blob's interpolant at the evaluation challenge. -/
noncomputable def blobOpeningError {F : Type*} [Field F] (f g : F[X]) (y z : F) : F[X] :=
  f - Polynomial.C y - g * (X - Polynomial.C z)

-- The polynomial lemmas below are stated over any field, not over `Fr` itself.
--
-- On `Fr`, the ring instance and the scoped field instance give two semirings.
--
-- Matching the two on the interpolant during kernel replay would unfold the 4096-point sum.

/-- At `z`, the error polynomial takes the value `f(z) - y`. -/
theorem eval_blobOpeningError {F : Type*} [Field F] (f g : F[X]) (y z : F) :
    (blobOpeningError f g y z).eval z = f.eval z - y := by
  simp [blobOpeningError]

/-- At `τ`, the error polynomial takes the value `f(τ) - y - g(τ) (τ - z)`. -/
theorem eval_blobOpeningError_at {F : Type*} [Field F] (f g : F[X]) (y z τ : F) :
    (blobOpeningError f g y z).eval τ = f.eval τ - y - g.eval τ * (τ - z) := by
  simp [blobOpeningError]

/-- When `f(τ) - p(z) = g(τ) (τ - z)`, either `f = p`, or `z` is a root of `f - p`.

Otherwise `τ` is a root of the nonzero error polynomial. -/
theorem opening_eq_or_root {F : Type*} [Field F] {f g p : F[X]} {z τ : F}
    (hid : f.eval τ - p.eval z = g.eval τ * (τ - z)) :
    f = p ∨ f ≠ p ∧ (f - p).eval z = 0 ∨
      blobOpeningError f g (p.eval z) z ≠ 0 ∧
        (blobOpeningError f g (p.eval z) z).eval τ = 0 := by
  have htau : (blobOpeningError f g (p.eval z) z).eval τ = 0 := by
    rw [eval_blobOpeningError_at, sub_eq_zero]
    exact hid
  rcases eq_or_ne (blobOpeningError f g (p.eval z) z) 0 with h0 | hne
  · have hz : f.eval z = p.eval z := by
      have hzero := congrArg (eval z) h0
      rw [eval_blobOpeningError, eval_zero] at hzero
      exact sub_eq_zero.mp hzero
    rcases eq_or_ne f p with hfp | hfne
    · exact Or.inl hfp
    · exact Or.inr (Or.inl ⟨hfne, by rw [eval_sub, sub_eq_zero]; exact hz⟩)
  · exact Or.inr (Or.inr ⟨hne, htau⟩)

/-- For `f` and `g` of degree below `n`, the error polynomial has degree at most `n`. -/
theorem natDegree_blobOpeningError_le {F : Type*} [Field F] {f g : F[X]} {n : Nat}
    (hf : f.natDegree < n) (hg : g.natDegree < n) (y z : F) :
    (blobOpeningError f g y z).natDegree ≤ n := by
  rw [blobOpeningError]
  refine le_trans (natDegree_sub_le (f - Polynomial.C y) (g * (X - Polynomial.C z))) ?_
  refine max_le ?_ ?_
  · exact le_trans (natDegree_sub_le f (Polynomial.C y))
      (max_le (Nat.le_of_lt hf) (by rw [natDegree_C]; exact Nat.zero_le n))
  · refine le_trans (natDegree_mul_le (p := g) (q := X - Polynomial.C z)) ?_
    refine Nat.le_trans (Nat.add_le_add_left (natDegree_sub_le X (Polynomial.C z)) _) ?_
    have hxz : max (X : F[X]).natDegree (Polynomial.C z).natDegree ≤ 1 :=
      max_le natDegree_X_le (by rw [natDegree_C]; decide)
    exact le_trans (Nat.add_le_add_left hxz _) (Nat.succ_le_of_lt hg)

/-- **An accepted blob opening binds its blob, or names a root.**

Assume a well-formed setup of the secret `τ`.

Let the blob decode, and let the commitment and the proof pass validation.

Let those points represent `f(τ)` and `g(τ)`, for two polynomials `f` and `g` of degree below 4096.

Let the check accept, and let `p` be the interpolant of the blob's decoded values.

Let `z` be the evaluation challenge of the blob and the commitment.

Then one of three cases holds, with `h = f - p(z) - g (X - z)`:

- `f = p`;
- or `f ≠ p`, `f - p` has degree below 4096, and `z` is a root of `f - p`;
- or `h` is nonzero of degree at most 4096, and `τ` is a root of `h`.

This theorem gives no bound on the cost of finding such polynomials when `τ` is secret. -/
theorem verifyBlobKzgProof_binding {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {blob : Blob} {commitment proof : Bytes48} {poly : Polynomial}
    {C P : G1} {f g : Fr[X]} (hblob : blobToPolynomial blob = .ok poly)
    (hC : validateKzgG1Point commitment = .ok C) (hf : G1.Represents C (f.eval τ))
    (hP : validateKzgG1Point proof = .ok P) (hg : G1.Represents P (g.eval τ))
    (hfdeg : f.natDegree < FIELD_ELEMENTS_PER_BLOB) (hgdeg : g.natDegree < FIELD_ELEMENTS_PER_BLOB)
    (h : verifyBlobKzgProof s blob commitment proof = .ok true) :
    f = interpolant poly ∨
      f ≠ interpolant poly ∧ (f - interpolant poly).natDegree < FIELD_ELEMENTS_PER_BLOB ∧
        (f - interpolant poly).eval (computeChallenge blob commitment) = 0 ∨
      blobOpeningError f g ((interpolant poly).eval (computeChallenge blob commitment))
          (computeChallenge blob commitment) ≠ 0 ∧
        (blobOpeningError f g ((interpolant poly).eval (computeChallenge blob commitment))
          (computeChallenge blob commitment)).natDegree ≤ FIELD_ELEMENTS_PER_BLOB ∧
        (blobOpeningError f g ((interpolant poly).eval (computeChallenge blob commitment))
          (computeChallenge blob commitment)).eval τ = 0 := by
  have hsubdeg (a b : Fr[X]) (ha : a.natDegree < FIELD_ELEMENTS_PER_BLOB)
      (hb : b.natDegree < FIELD_ELEMENTS_PER_BLOB) :
      (a - b).natDegree < FIELD_ELEMENTS_PER_BLOB :=
    lt_of_le_of_lt (natDegree_sub_le a b) (max_lt ha hb)
  obtain ⟨poly', C', P', hblob', hC', hP', hv⟩ := verifyBlobKzgProof_eq_ok_true h
  cases hblob.symm.trans hblob'
  cases hC.symm.trans hC'
  cases hP.symm.trans hP'
  rcases opening_eq_or_root ((verifyKzgProofImpl_iff hs hf hg
      (computeChallenge blob commitment)
      ((interpolant poly).eval (computeChallenge blob commitment))).mp hv)
    with hfp | ⟨hne, hroot⟩ | ⟨hne, hroot⟩
  · exact Or.inl hfp
  · exact Or.inr (Or.inl ⟨hne, hsubdeg f (interpolant poly) hfdeg (natDegree_interpolant_lt poly),
      hroot⟩)
  · exact Or.inr (Or.inr ⟨hne, natDegree_blobOpeningError_le hfdeg hgdeg _ _, hroot⟩)

end EthLib.Cryptography.Kzg
