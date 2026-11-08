module

public import EthLib.Cryptography.Proofs.Kzg.Quotient
public import EthLib.Cryptography.Proofs.Kzg.ValidateG1

/-!
# Proofs: honest KZG proofs verify, and accepted blob openings

The check of an opening of `c` at `z` to `y`, with proof `w`, holds when `c - y = w (τ - z)`.

This needs the pairing law, as a hypothesis, and the secret `τ` of a well-formed setup.

An honest proof commits to the quotient `q = (p - p(z)) / (X - z)`, so the identity holds.

For a blob opening whose commitment and proof read as `f(τ)` and `g(τ)` of degree below 4096:

- `f = p`, where `p` is the interpolant of the blob's decoded values;
- or `f ≠ p`, `f - p` has degree below 4096, and the challenge `z` is a root of `f - p`;
- or `h = f - p(z) - g (X - z)` is nonzero of degree at most 4096, and `τ` is a root of `h`.

This theorem gives no bound on the cost of finding such polynomials when `τ` is secret.

The reading of points as polynomials is the algebraic group model of Fuchsbauer, Kiltz and Loss:

<https://eprint.iacr.org/2017/620>

The scheme is PolyCommit_DL, §3.2 of Kate, Zaverucha and Goldberg, ASIACRYPT 2010:

<https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (Bytes32)
open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-- The scalar identity of the opening check. -/
private theorem opening_iff (c y w t z : Fr) :
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

/-- For a blob that decodes, the proof computation accepts the commitment of the blob.

It returns the compressed commitment to the quotient at the challenge of the blob. -/
theorem computeBlobKzgProof_eq {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ) {blob : Blob}
    {poly : Polynomial} (hblob : blobToPolynomial blob = .ok poly) :
    ∃ Q : Polynomial, Q.size = FIELD_ELEMENTS_PER_BLOB ∧
      (∀ i : Fin FIELD_ELEMENTS_PER_BLOB, Q[i.val]! =
        (quotientPoly poly (computeChallenge blob
          (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)))).eval (evalDomain i)) ∧
      computeBlobKzgProof s blob (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) =
        .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray Q)) := by
  have hsize := size_blobToPolynomial blob poly hblob
  obtain ⟨C', hC', -⟩ := validateKzgG1Point_compressG1 (represents_lagrange_msm hs (τ := τ) hsize)
  have hbytes : bytesToKzgCommitment (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) =
      .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)) := by
    refine bytesToKzgCommitment_ok_iff.mpr ⟨?_, rfl⟩
    rw [validateKzgG1_eq_validateKzgG1Point, hC']
    rfl
  obtain ⟨Q, hQs, hQv, hImpl⟩ := computeKzgProofImpl_eq s hsize
    (computeChallenge blob (compressG1 (G1.msm s.g1LagrangeBrp.toArray poly)))
  refine ⟨Q, hQs, hQv, ?_⟩
  unfold computeBlobKzgProof
  rw [hbytes, hblob]
  change (computeKzgProofImpl s poly _ >>= fun v => pure v.1) = _
  rw [hImpl]
  rfl

/-- For a blob that decodes, the commitment and the proof computations return no error. -/
theorem exists_blobToKzgCommitment_computeBlobKzgProof {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {blob : Blob} {poly : Polynomial}
    (hblob : blobToPolynomial blob = .ok poly) :
    ∃ C P, blobToKzgCommitment s blob = .ok C ∧ computeBlobKzgProof s blob C = .ok P := by
  obtain ⟨Q, -, -, hcomp⟩ := computeBlobKzgProof_eq hs hblob
  exact ⟨_, _, blobToKzgCommitment_eq_ok s hblob, hcomp⟩

/-- **A valid opening of a blob at its Fiat-Shamir challenge, for the secret `τ`.**

The blob decodes to values `poly`.

The commitment and the proof pass KZG validation, as points that represent `c` and `w`.

Let `z` be the evaluation challenge of the blob and the commitment.

Then `c - p(z) = w (τ - z)` for the interpolant `p` of `poly`. -/
def BlobOpeningValid (τ : Fr) (blob : Blob) (commitment proof : Bytes48) : Prop :=
  ∃ poly C c P w, blobToPolynomial blob = .ok poly ∧
    validateKzgG1Point commitment = .ok C ∧ G1.Represents C c ∧
    validateKzgG1Point proof = .ok P ∧ G1.Represents P w ∧
    c - (interpolant poly).eval (computeChallenge blob commitment) =
      w * (τ - computeChallenge blob commitment)

/-- **An honestly computed blob commitment and proof form a valid opening.**

Let the setup be well-formed for the secret `τ`.

Let `blobToKzgCommitment` return `C`, and let `computeBlobKzgProof` return `P`.

Then `(blob, C, P)` is a valid blob opening at `τ`. -/
theorem blobOpeningValid_computeBlobKzgProof {s : TrustedSetup} {τ : Fr} (hs : s.WellFormed τ)
    {blob : Blob} {C P : Bytes48} (hC : blobToKzgCommitment s blob = .ok C)
    (hP : computeBlobKzgProof s blob C = .ok P) :
    BlobOpeningValid τ blob C P := by
  cases hblob : blobToPolynomial blob with
  | error e =>
    unfold blobToKzgCommitment at hC
    rw [hblob] at hC
    cases hC
  | ok poly =>
    rw [blobToKzgCommitment_eq_ok s hblob] at hC
    obtain rfl := Except.ok.inj hC
    obtain ⟨Q, hQs, hQv, hcomp⟩ := computeBlobKzgProof_eq hs hblob
    rw [hcomp] at hP
    obtain rfl := Except.ok.inj hP
    obtain ⟨C', hC', hrC'⟩ := validateKzgG1Point_compressG1
      (represents_lagrange_msm hs (τ := τ) (size_blobToPolynomial blob poly hblob))
    obtain ⟨P', hP', hrP'⟩ := validateKzgG1Point_compressG1 (represents_quotient hs hQs hQv)
    exact ⟨poly, C', _, P', _, hblob, hC', hrC', hP', hrP', eval_interpolant_sub poly _ τ⟩

/-- Under the pairing law and a well-formed setup, a valid blob opening verifies. -/
theorem verifyBlobKzgProof_of_blobOpeningValid (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {blob : Blob} {commitment proof : Bytes48}
    (h : BlobOpeningValid τ blob commitment proof) :
    verifyBlobKzgProof s blob commitment proof = .ok true := by
  obtain ⟨poly, C, c, P, w, hblob, hC, hrC, hP, hrP, hid⟩ := h
  unfold verifyBlobKzgProof
  rw [hC, hblob, hP]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [evaluatePolynomialInEvaluationForm_eq_interpolate poly _
    (size_blobToPolynomial blob poly hblob)]
  exact congrArg Except.ok ((verifyKzgProofImpl_iff laws hs hrC hrP _ _).mpr hid)

/-- An accepted check of a blob decodes the blob, the commitment and the proof.

The check of the decoded points then accepts at the challenge and the interpolant. -/
theorem verifyBlobKzgProof_eq_ok_true {s : TrustedSetup} {blob : Blob}
    {commitment proof : Bytes48}
    (h : verifyBlobKzgProof s blob commitment proof = .ok true) :
    ∃ poly C P, blobToPolynomial blob = .ok poly ∧
      validateKzgG1Point commitment = .ok C ∧ validateKzgG1Point proof = .ok P ∧
      verifyKzgProofImpl s C (computeChallenge blob commitment)
        ((interpolant poly).eval (computeChallenge blob commitment)) P = true := by
  unfold verifyBlobKzgProof at h
  cases hC : validateKzgG1Point commitment with
  | error e =>
    rw [hC] at h
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | ok C =>
    cases hblob : blobToPolynomial blob with
    | error e =>
      rw [hC, hblob] at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      exact nomatch h
    | ok poly =>
      cases hP : validateKzgG1Point proof with
      | error e =>
        rw [hC, hblob, hP] at h
        simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw] at h
        rw [evaluatePolynomialInEvaluationForm_eq_interpolate poly _
          (size_blobToPolynomial blob poly hblob)] at h
        exact nomatch h
      | ok P =>
        rw [hC, hblob, hP] at h
        simp only [bind, Except.bind, pure, Except.pure] at h
        rw [evaluatePolynomialInEvaluationForm_eq_interpolate poly _
          (size_blobToPolynomial blob poly hblob)] at h
        exact ⟨poly, C, P, rfl, rfl, rfl, Except.ok.inj h⟩

/-! ## An accepted opening binds the blob, or names a root -/

/-- The polynomial of an opening that passes: `f - y - g (X - z)`.

The commitment reads as `f` at the secret, and the proof reads as `g`.

In a blob opening, `y` is the blob's interpolant at the evaluation challenge. -/
noncomputable def blobOpeningError {F : Type*} [Field F] (f g : F[X]) (y z : F) : F[X] :=
  f - Polynomial.C y - g * (X - Polynomial.C z)

-- The polynomial lemmas below are stated over a field, as in `FrBatchInverse`.
--
-- On `Fr` itself, the ring instance and the scoped field instance give two semirings.
--
-- Matching the two on the interpolant during kernel replay would unfold the 4096-point sum.

/-- At `z`, the opening polynomial takes the value `f(z) - y`. -/
theorem eval_blobOpeningError {F : Type*} [Field F] (f g : F[X]) (y z : F) :
    (blobOpeningError f g y z).eval z = f.eval z - y := by
  simp [blobOpeningError]

/-- At `τ`, the opening polynomial takes the value `f(τ) - y - g(τ) (τ - z)`. -/
theorem eval_blobOpeningError_at {F : Type*} [Field F] (f g : F[X]) (y z τ : F) :
    (blobOpeningError f g y z).eval τ = f.eval τ - y - g.eval τ * (τ - z) := by
  simp [blobOpeningError]

/-- When `f(τ) - p(z) = g(τ) (τ - z)`, either `f = p` or `z` or `τ` is a root. -/
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

/-- For `f` and `g` of degree below `n`, the opening polynomial has degree at most `n`. -/
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

/-- **An accepted blob opening commits to its blob, or names a root.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Let the blob decode, and let the commitment and the proof pass validation.

Let those points represent `f(τ)` and `g(τ)`, for two polynomials `f` and `g` of degree below 4096.

Let the check accept, and let `p` be the interpolant of the blob's decoded values.

Let `z` be the evaluation challenge of the blob and the commitment.

Then one of three cases holds, with `h = f - p(z) - g (X - z)`:

- `f = p`;
- or `f ≠ p`, `f - p` has degree below 4096, and `z` is a root of `f - p`;
- or `h` is nonzero of degree at most 4096, and `τ` is a root of `h`.

This theorem gives no bound on the cost of finding such polynomials when `τ` is secret. -/
theorem verifyBlobKzgProof_binding (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {blob : Blob} {commitment proof : Bytes48} {poly : Polynomial}
    {C P : G1} {f g : Fr[X]} (hblob : blobToPolynomial blob = .ok poly)
    (hC : validateKzgG1Point commitment = .ok C) (hf : G1.Represents C (f.eval τ))
    (hP : validateKzgG1Point proof = .ok P) (hg : G1.Represents P (g.eval τ))
    (hfdeg : f.natDegree < FIELD_ELEMENTS_PER_BLOB) (hgdeg : g.natDegree < FIELD_ELEMENTS_PER_BLOB)
    (h : verifyBlobKzgProof s blob commitment proof = .ok true) :
    let p := interpolant poly
    let z := computeChallenge blob commitment
    let hpoly := blobOpeningError f g (p.eval z) z
    f = p ∨
      f ≠ p ∧ (f - p).natDegree < FIELD_ELEMENTS_PER_BLOB ∧ (f - p).eval z = 0 ∨
      hpoly ≠ 0 ∧ hpoly.natDegree ≤ FIELD_ELEMENTS_PER_BLOB ∧ hpoly.eval τ = 0 := by
  have hsubdeg (a b : Fr[X]) (ha : a.natDegree < FIELD_ELEMENTS_PER_BLOB)
      (hb : b.natDegree < FIELD_ELEMENTS_PER_BLOB) :
      (a - b).natDegree < FIELD_ELEMENTS_PER_BLOB :=
    lt_of_le_of_lt (natDegree_sub_le a b) (max_lt ha hb)
  have herrdeg (a b : Fr[X]) (ha : a.natDegree < FIELD_ELEMENTS_PER_BLOB)
      (hb : b.natDegree < FIELD_ELEMENTS_PER_BLOB) (y z : Fr) :
      (blobOpeningError a b y z).natDegree ≤ FIELD_ELEMENTS_PER_BLOB :=
    natDegree_blobOpeningError_le ha hb y z
  obtain ⟨poly', C', P', hblob', hC', hP', hv⟩ := verifyBlobKzgProof_eq_ok_true h
  cases hblob.symm.trans hblob'
  cases hC.symm.trans hC'
  cases hP.symm.trans hP'
  rcases opening_eq_or_root ((verifyKzgProofImpl_iff laws hs hf hg
      (computeChallenge blob commitment)
      ((interpolant poly).eval (computeChallenge blob commitment))).mp hv)
    with hfp | ⟨hne, hroot⟩ | ⟨hne, hroot⟩
  · exact Or.inl hfp
  · exact Or.inr (Or.inl ⟨hne, hsubdeg f (interpolant poly) hfdeg (natDegree_interpolant_lt poly),
      hroot⟩)
  · exact Or.inr (Or.inr ⟨hne, herrdeg f g hfdeg hgdeg
      ((interpolant poly).eval (computeChallenge blob commitment))
      (computeChallenge blob commitment), hroot⟩)

/-- **Honest blob proofs verify.**

Under the pairing law and a well-formed setup, a blob's proof verifies against its commitment. -/
theorem verifyBlobKzgProof_computeBlobKzgProof (laws : Bls.PairingLaws) {s : TrustedSetup}
    {τ : Fr} (hs : s.WellFormed τ) {blob : Blob} {C P : KZGCommitment}
    (hC : blobToKzgCommitment s blob = .ok C)
    (hP : computeBlobKzgProof s blob C = .ok P) :
    verifyBlobKzgProof s blob C P = .ok true := by
  exact verifyBlobKzgProof_of_blobOpeningValid laws hs
    (blobOpeningValid_computeBlobKzgProof hs hC hP)

end EthLib.Cryptography.Kzg
