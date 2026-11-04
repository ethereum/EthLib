module

public import EthLib.Cryptography.Proofs.Kzg.Quotient
public import EthLib.Cryptography.Proofs.Kzg.ValidateG1

/-!
# Proofs: honest KZG proofs verify

The check of an opening of `c` at `z` to `y`, with proof `w`, holds when `c - y = w (τ - z)`.

This needs the pairing law, as a hypothesis, and the secret `τ` of a well-formed setup.

An honest proof commits to the quotient `q = (p - p(z)) / (X - z)`, so the identity holds.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (Bytes32)
open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

-- Core's power instance on `Fin` hides Mathlib's power on `Fr`, as in `Proofs.Bls.FrZMod`.
attribute [-instance] Fin.instNatPow

/-- The scalar identity of the opening check. -/
private theorem opening_iff (c y w t z : ZMod Fr.modulus) :
    (c + -y) * -1 + w * (t + -z) = 0 ↔ c - y = w * (t - z) := by
  constructor <;> intro h <;> linear_combination -h

/-- Under the pairing law, the check with `[τ]_2` accepts exactly when `c - y = w (τ - z)`.

Here the commitment represents `c • g1` and the proof `w • g1`. -/
theorem verifyKzgProofWith_iff (laws : Bls.PairingLaws) {s2 : G2} {τ : Fr}
    (hs2 : G2.Represents s2 τ) {C P : G1} {c w : Fr}
    (hC : G1.Represents C c) (hP : G1.Represents P w) (z y : Fr) :
    verifyKzgProofWith s2 C z y P = true ↔ c - y = w * (τ - z) := by
  have hCy := hC.add (G1.represents_mul_generator (-y))
  have hX := hs2.add (G2.represents_mul_generator (-z))
  have h := laws.two_pairs hCy G2.represents_generator.neg hP hX
  exact h.trans (opening_iff c y w τ z)

/-- Under the pairing law and a well-formed setup, the check accepts iff `c - y = w (τ - z)`. -/
theorem verifyKzgProofImpl_iff (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {C P : G1} {c w : Fr}
    (hC : G1.Represents C c) (hP : G1.Represents P w) (z y : Fr) :
    verifyKzgProofImpl s C z y P = true ↔ c - y = w * (τ - z) := by
  have hs2 : G2.Represents (s.g2Monomial[1]'(by decide)) τ := by
    have h := hs.monomial_g2 ⟨1, by decide⟩
    simp only [Fin.getElem_fin, pow_one] at h
    exact h
  exact verifyKzgProofWith_iff laws hs2 hC hP z y

/-- The compressed encoding of a representative passes KZG validation.

The decoded point represents the same scalar. -/
theorem validateKzgG1Point_compressG1 {P : G1} {a : Fr} (h : G1.Represents P a) :
    ∃ Q, validateKzgG1Point (compressG1 P) = .ok Q ∧ G1.Represents Q a := by
  obtain ⟨Q, hu, hpt⟩ := G1.uncompress_compress h.1
  refine ⟨Q, validateKzgG1Point_eq_ok_iff.mpr ⟨hu, ?_⟩, G1.uncompress_valid hu, hpt.trans h.2⟩
  rw [hpt, h.2, G1.toPoint_mul_generator, G1.ofFr, ← mul_nsmul', mul_nsmul,
    G1.modulus_smul_generator, nsmul_zero]

/-- An opening whose scalars satisfy `c - y = w (τ - z)` verifies, from its bytes. -/
theorem verifyKzgProof_of_represents (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {C P : G1} {c w z y : Fr} {zBytes : Bytes32}
    (hC : G1.Represents C c) (hP : G1.Represents P w) (hz : bytesToBlsField zBytes = .ok z)
    (hid : c - y = w * (τ - z)) :
    verifyKzgProof s (compressG1 C) zBytes (blsFieldToBytes y) (compressG1 P) = .ok true := by
  obtain ⟨C', hC', hrC⟩ := validateKzgG1Point_compressG1 hC
  obtain ⟨P', hP', hrP⟩ := validateKzgG1Point_compressG1 hP
  unfold verifyKzgProof
  rw [hC', hP', hz, bytesToBlsField_blsFieldToBytes]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [(verifyKzgProofImpl_iff laws hs hrC hrP z y).mpr hid]

/-- The proof that the computation returns represents the quotient at `τ`. -/
theorem represents_quotient {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {poly Q : Polynomial} {z : Fr} (hQs : Q.size = FIELD_ELEMENTS_PER_BLOB)
    (hQv : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB,
      Q[i.val]! = (quotientPoly poly z).eval (evalDomain i)) :
    G1.Represents (G1.msm s.g1LagrangeBrp.toArray Q) ((quotientPoly poly z).eval τ) := by
  have hq : interpolant Q = quotientPoly poly z :=
    interpolant_eq_of_eval (by
      have h := natDegree_quotientPoly_le poly z
      have h4 : FIELD_ELEMENTS_PER_BLOB = 4096 := rfl
      rw [h4] at h ⊢
      omega) hQv
  have h := represents_lagrange_msm hs hQs
  rw [hq] at h
  exact h

/-- The identity `p(τ) - p(z) = q(τ) (τ - z)`, from the exact division. -/
theorem eval_interpolant_sub (poly : Polynomial) (z τ : Fr) :
    (interpolant poly).eval τ - (interpolant poly).eval z =
      (quotientPoly poly z).eval τ * (τ - z) := by
  have h := congrArg (eval τ) (interpolant_sub_eq_mul poly z)
  simp only [eval_sub, eval_C, eval_mul, eval_X] at h
  exact h.trans (mul_comm _ _)

/-- **Honest proofs verify.**

Under the pairing law and a well-formed setup, a proof that the computation returns verifies.

It holds for every point `z`, inside or outside the domain. -/
theorem verifyKzgProof_computeKzgProof (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {blob : Blob} {C P : KZGCommitment} {zBytes yBytes : Bytes32}
    (hC : blobToKzgCommitment s blob = .ok C)
    (hP : computeKzgProof s blob zBytes = .ok (P, yBytes)) :
    verifyKzgProof s C zBytes yBytes P = .ok true := by
  cases hblob : blobToPolynomial blob with
  | error e =>
    have herr : blobToKzgCommitment s blob = .error e := by
      unfold blobToKzgCommitment
      rw [hblob]
      rfl
    rw [herr] at hC
    exact absurd hC (fun h => nomatch h)
  | ok poly =>
    have hsize := size_blobToPolynomial blob poly hblob
    rw [blobToKzgCommitment_eq_ok s hblob] at hC
    obtain rfl := Except.ok.inj hC
    cases hz : bytesToBlsField zBytes with
    | error e =>
      have herr : computeKzgProof s blob zBytes = .error e := by
        unfold computeKzgProof
        rw [hblob, hz]
        rfl
      rw [herr] at hP
      exact absurd hP (fun h => nomatch h)
    | ok z =>
      obtain ⟨Q, hQs, hQv, hImpl⟩ := computeKzgProofImpl_eq s hsize z
      have hcomp : computeKzgProof s blob zBytes =
          .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray Q),
            blsFieldToBytes ((interpolant poly).eval z)) := by
        unfold computeKzgProof
        rw [hblob, hz]
        simp only [bind, Except.bind]
        rw [hImpl]
        rfl
      rw [hcomp] at hP
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hP)
      exact verifyKzgProof_of_represents laws hs (represents_lagrange_msm hs hsize)
        (represents_quotient hs hQs hQv) hz (eval_interpolant_sub poly z τ)

/-- **Honest blob proofs verify.**

Under the pairing law and a well-formed setup, a blob's proof verifies against its commitment. -/
theorem verifyBlobKzgProof_computeBlobKzgProof (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {blob : Blob} {C P : KZGCommitment}
    (hC : blobToKzgCommitment s blob = .ok C)
    (hP : computeBlobKzgProof s blob C = .ok P) :
    verifyBlobKzgProof s blob C P = .ok true := by
  cases hblob : blobToPolynomial blob with
  | error e =>
    have herr : blobToKzgCommitment s blob = .error e := by
      unfold blobToKzgCommitment
      rw [hblob]
      rfl
    rw [herr] at hC
    exact absurd hC (fun h => nomatch h)
  | ok poly =>
    have hsize := size_blobToPolynomial blob poly hblob
    rw [blobToKzgCommitment_eq_ok s hblob] at hC
    obtain rfl := Except.ok.inj hC
    have hrC := represents_lagrange_msm hs (τ := τ) hsize
    obtain ⟨C', hC', hrC'⟩ := validateKzgG1Point_compressG1 hrC
    -- The commitment passes validation, so the proof computation keeps it.
    have hbytes : bytesToKzgCommitment (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) =
        .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) := by
      refine bytesToKzgCommitment_ok_iff.mpr ⟨?_, rfl⟩
      rw [validateKzgG1_eq_validateKzgG1Point, hC']
      rfl
    let z := computeChallenge blob (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly))
    obtain ⟨Q, hQs, hQv, hImpl⟩ := computeKzgProofImpl_eq s hsize z
    have hcomp : computeBlobKzgProof s blob (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) =
        .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray Q)) := by
      unfold computeBlobKzgProof
      rw [hbytes, hblob]
      simp only [bind, Except.bind]
      rw [hImpl]
      rfl
    rw [hcomp] at hP
    obtain rfl := Except.ok.inj hP
    obtain ⟨P', hP', hrP'⟩ := validateKzgG1Point_compressG1 (represents_quotient hs hQs hQv)
    unfold verifyBlobKzgProof
    rw [hC', hblob, hP']
    simp only [bind, Except.bind, pure, Except.pure]
    rw [evaluatePolynomialInEvaluationForm_eq_interpolate poly _ hsize]
    exact congrArg Except.ok
      ((verifyKzgProofImpl_iff laws hs hrC' hrP' _ _).mpr (eval_interpolant_sub poly z τ))

end EthLib.Cryptography.Kzg
