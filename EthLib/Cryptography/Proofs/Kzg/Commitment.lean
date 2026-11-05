module

public import EthLib.Cryptography.Proofs.Kzg.Evaluation
public import EthLib.Cryptography.Proofs.Kzg.Core
public import EthLib.Cryptography.Proofs.Kzg.TrustedSetup
public import EthLib.Cryptography.Proofs.Bls.Represents

/-!
# Proofs: a commitment is the blob's polynomial at the setup secret

A setup of the secret `τ` holds `[τ^i]_1`, `[τ^i]_2` and `[L_i(τ)]_1`, with `L_i` a Lagrange basis.

A blob's commitment sums its values times the Lagrange points, which gives `[p(τ)]_1`.

The scheme is PolyCommit_DL, §3.2 of Kate, Zaverucha and Goldberg, ASIACRYPT 2010:

<https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-- The setup of the secret `τ`.

The monomial points represent the powers of `τ`, in `G1` and in `G2`.

Lagrange point `i` represents basis polynomial `i` of the blob domain, at `τ`.

The domain is the 4096-th roots of unity in bit-reversed order.

The decoder bit-reverses the Lagrange points, so point `i` belongs to domain point `i`. -/
structure TrustedSetup.WellFormed (s : TrustedSetup) (τ : Fr) : Prop where
  /-- Lagrange point `i` represents `[L_i(τ)]_1`. -/
  lagrange_g1 : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB,
    G1.Represents s.g1LagrangeBrp[i] ((Lagrange.basis Finset.univ evalDomain i).eval τ)
  /-- Monomial point `i` of `G1` represents `[τ^i]_1`. -/
  monomial_g1 : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Represents s.g1Monomial[i] (τ ^ i.val)
  /-- Monomial point `i` of `G2` represents `[τ^i]_2`. -/
  monomial_g2 : ∀ i : Fin KZG_SETUP_G2_LENGTH, G2.Represents s.g2Monomial[i] (τ ^ i.val)

/-- A well-formed setup is valid: every point is on its curve. -/
theorem TrustedSetup.WellFormed.valid {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ) :
    s.Valid :=
  ⟨fun i => (hs.lagrange_g1 i).1, fun i => (hs.monomial_g1 i).1, fun i => (hs.monomial_g2 i).1⟩

/-- In a well-formed setup, `r` times each monomial point of `G1` is zero. -/
theorem TrustedSetup.WellFormed.torsion {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {t : Nat} (ht : t < FIELD_ELEMENTS_PER_BLOB) :
    Fr.modulus • G1.toPoint s.g1Monomial.toArray[t]! = 0 := by
  rw [getElem!_pos s.g1Monomial.toArray t (by simpa using ht)]
  have h := (hs.monomial_g1 ⟨t, ht⟩).2
  simp only [Fin.getElem_fin] at h
  simp only [Vector.getElem_toArray]
  rw [h, G1.toPoint_mul_generator, G1.ofFr, ← mul_nsmul', mul_nsmul, G1.modulus_smul_generator,
    nsmul_zero]

/-- The polynomial of degree below 4096 that takes the given values on the blob domain. -/
noncomputable def interpolant (poly : Polynomial) : _root_.Polynomial Fr :=
  Lagrange.interpolate Finset.univ evalDomain fun i => poly[i.val]!

/-- The value of the interpolant at `τ` is the sum of the values times the basis at `τ`. -/
theorem eval_interpolant (poly : Polynomial) (τ : Fr) :
    (interpolant poly).eval τ =
      ∑ i : Fin FIELD_ELEMENTS_PER_BLOB,
        poly[i.val]! * (Lagrange.basis Finset.univ evalDomain i).eval τ := by
  rw [interpolant, Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C]

/-- On a decoded blob, the commitment compresses the sum of the values times the points. -/
theorem blobToKzgCommitment_eq_ok (s : TrustedSetup) {blob : Blob} {poly : Polynomial}
    (hblob : blobToPolynomial blob = .ok poly) :
    blobToKzgCommitment s blob = .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) := by
  have hsize : s.g1LagrangeBrp.toArray.size = poly.size := by
    rw [Vector.size_toArray, size_blobToPolynomial blob poly hblob]
  unfold blobToKzgCommitment
  rw [hblob]
  change (g1LincombPoints s.g1LagrangeBrp.toArray poly >>= fun c => pure (compressG1 c)) = _
  rw [g1LincombPoints_eq_msm hsize]
  rfl

/-- The sum of 4096 values times the Lagrange points represents the interpolant at `τ`. -/
theorem represents_lagrange_msm {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {poly : Polynomial} (hsize : poly.size = FIELD_ELEMENTS_PER_BLOB) :
    G1.Represents (G1.msm s.g1LagrangeBrp.toArray poly) ((interpolant poly).eval τ) := by
  let a : Nat → Fr := fun j =>
    if h : j < FIELD_ELEMENTS_PER_BLOB then (Lagrange.basis Finset.univ evalDomain ⟨j, h⟩).eval τ
    else 0
  have hpts : ∀ j < s.g1LagrangeBrp.toArray.size,
      G1.Represents s.g1LagrangeBrp.toArray[j]! (a j) := by
    intro j hj
    rw [Vector.size_toArray] at hj
    rw [getElem!_pos s.g1LagrangeBrp.toArray j (by simpa using hj)]
    simpa [a, hj] using hs.lagrange_g1 ⟨j, hj⟩
  have h := G1.represents_msm (by rw [Vector.size_toArray, hsize]) hpts
  rw [Vector.size_toArray] at h
  convert h using 1
  rw [eval_interpolant, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [a]

/-- On a decoded blob of a well-formed setup, the commitment holds `[p(τ)]_1`.

Here `p` is the polynomial of degree below 4096 that takes the blob's values on the domain. -/
theorem blobToKzgCommitment_represents {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {blob : Blob} {poly : Polynomial} (hblob : blobToPolynomial blob = .ok poly) :
    blobToKzgCommitment s blob = .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) ∧
      G1.Represents (G1.msm s.g1LagrangeBrp.toArray poly) ((interpolant poly).eval τ) :=
  ⟨blobToKzgCommitment_eq_ok s hblob,
    represents_lagrange_msm hs (size_blobToPolynomial blob poly hblob)⟩

end EthLib.Cryptography.Kzg
