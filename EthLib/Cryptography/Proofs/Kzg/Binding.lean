module

public import EthLib.Cryptography.Proofs.Kzg.Verify
public import EthLib.Cryptography.Proofs.Bls.KeyValidate

/-!
# Proofs: two openings to different values give a strong Diffie–Hellman solution

Let two proofs open one commitment at `z` to values `y ≠ y'`, and let both checks pass.

Then `(π - π') / (y' - y)` represents `1 / (τ - z)`.

So `(-z, (π - π') / (y' - y))` solves the strong Diffie–Hellman problem for the secret `τ`.

The setup also holds `[τ]_2`, so the instance is the asymmetric variant of the problem.

The scalar of 48 bytes is the scalar that their point represents, if there is one.

The search reads only the two openings, as in Appendix C.1 of the paper below.

It is the extended version of Kate, Zaverucha and Goldberg, CACR 2010-10:

<https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Base (Bytes32)
open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr

/-- A solution `(c, P)` of the strong Diffie–Hellman problem for the secret `τ`.

The point `P` represents `1 / (τ + c)` times the generator, and `τ + c ≠ 0`.

The problem is Definition 2.3 of the extended KZG paper. -/
def IsSdhSolution (τ : Fr) (sol : Fr × G1) : Prop :=
  τ + sol.1 ≠ 0 ∧ G1.Represents sol.2 (τ + sol.1)⁻¹

/-- The search of a solution in two openings at `z`, to `y` with proof `π` and to `y'` with `π'`.

Equal values give nothing.

Otherwise it returns `(-z, (π - π') / (y' - y))`. -/
def findSdh (z y y' : Fr) (π π' : G1) : Option (Fr × G1) :=
  if y = y' then none else some (-z, G1.mul (G1.add π (G1.neg π')) (y' - y).inverse)

/-- The search finds nothing in two openings to one value. -/
theorem findSdh_self (z y : Fr) (π π' : G1) : findSdh z y y π π' = none := by
  simp [findSdh]

/-- The scalar step: two accepting openings to different values give `1 / (τ - z)`. -/
private theorem sdh_scalar (c y y' w w' t z : Fr) (hne : y ≠ y')
    (h : c - y = w * (t - z)) (h' : c - y' = w' * (t - z)) :
    t + -z ≠ 0 ∧ (y' - y)⁻¹ * (w + -w') = (t + -z)⁻¹ := by
  have htz : t + -z ≠ 0 := by
    intro h0
    have : t - z = 0 := by rw [sub_eq_add_neg]; exact h0
    rw [this, mul_zero, sub_eq_zero] at h h'
    exact hne (h.symm.trans h')
  have hyy : y' - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  refine ⟨htz, ?_⟩
  field_simp
  linear_combination h' - h

/-- Two openings of one commitment at `z` whose scalars satisfy the opening identity.

Let the proofs represent `w` and `w'`, and let the values `y` and `y'` differ.

Then the search returns a strong Diffie–Hellman solution for `τ`. -/
theorem findSdh_valid_of_identity {τ c w w' z y y' : Fr} {P P' : G1}
    (hP : G1.Represents P w) (hP' : G1.Represents P' w') (hne : y ≠ y')
    (hid : c - y = w * (τ - z)) (hid' : c - y' = w' * (τ - z)) :
    ∃ sol, findSdh z y y' P P' = some sol ∧ IsSdhSolution τ sol := by
  obtain ⟨htz, hinv⟩ := sdh_scalar c y y' w w' τ z hne hid hid'
  refine ⟨(-z, G1.mul (G1.add P (G1.neg P')) (y' - y).inverse), by simp [findSdh, hne], htz, ?_⟩
  have hscalar : (y' - y).inverse * (w + -w') = (τ + -z)⁻¹ := by
    rw [Bls.Fr.inverse_eq_inv]
    exact hinv
  show G1.Represents (G1.mul (G1.add P (G1.neg P')) (y' - y).inverse) (τ + -z)⁻¹
  rw [← hscalar]
  exact (hP.add hP'.neg).mul (y' - y).inverse

/-- **Evaluation binding, with a named solution.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Let a commitment and two proofs represent `c`, `w` and `w'`.

Let the check accept the first proof for the value `y`, and the second for `y'`.

Then `y = y'`, or the search returns a strong Diffie–Hellman solution for `τ`. -/
theorem findSdh_valid (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {C P P' : G1} {c w w' z y y' : Fr}
    (hC : G1.Represents C c) (hP : G1.Represents P w) (hP' : G1.Represents P' w')
    (h : verifyKzgProofImpl s C z y P = true) (h' : verifyKzgProofImpl s C z y' P' = true) :
    y = y' ∨ ∃ sol, findSdh z y y' P P' = some sol ∧ IsSdhSolution τ sol := by
  by_cases hne : y = y'
  · exact Or.inl hne
  · exact Or.inr (findSdh_valid_of_identity hP hP' hne
      ((verifyKzgProofImpl_iff laws hs hC hP z y).mp h)
      ((verifyKzgProofImpl_iff laws hs hC hP' z y').mp h'))

/-- A point that passes KZG validation represents some scalar. -/
theorem represents_of_validateKzgG1Point {b : Bytes48} {P : G1}
    (h : validateKzgG1Point b = .ok P) : ∃ a, G1.Represents P a := by
  obtain ⟨hu, hr⟩ := validateKzgG1Point_eq_ok_iff.mp h
  have hv := G1.uncompress_valid hu
  exact (G1.inSubgroup_iff_exists_represents hv).mp
    ((G1.inSubgroup_iff_modulus_smul_eq_zero hv).mpr hr)

/-- Bytes that pass KZG validation decode to a point that represents some scalar. -/
theorem represents_of_validateKzgG1 {b : Bytes48} (h : validateKzgG1 b = true) {P : G1}
    (hP : uncompressG1 b = .ok P) : ∃ a, G1.Represents P a := by
  obtain ⟨Q, hQ⟩ := exists_validateKzgG1Point_of_validateKzgG1 h
  rw [uncompressG1_of_validateKzgG1Point hQ] at hP
  cases hP
  exact represents_of_validateKzgG1Point hQ

/-- The scalar of 48 bytes: the scalar that their point represents, if there is one. -/
noncomputable def scalarOf (b : Bytes48) : Fr :=
  Classical.epsilon fun a => ∀ P, uncompressG1 b = .ok P → G1.Represents P a

/-- Bytes that pass KZG validation decode to a point that represents their scalar. -/
theorem represents_scalarOf {b : Bytes48} (h : validateKzgG1 b = true) {P : G1}
    (hP : uncompressG1 b = .ok P) : G1.Represents P (scalarOf b) := by
  obtain ⟨a, ha⟩ := represents_of_validateKzgG1 h hP
  refine Classical.epsilon_spec (p := fun a => ∀ P, uncompressG1 b = .ok P → G1.Represents P a)
    ⟨a, fun P' hP' => ?_⟩ P hP
  rw [hP] at hP'
  cases hP'
  exact ha

/-- Bytes that decode to a point of the subgroup have the scalar of that point. -/
theorem scalarOf_eq {b : Bytes48} {P : G1} {a : Fr} (hb : validateKzgG1Point b = .ok P)
    (ha : G1.Represents P a) : scalarOf b = a :=
  (represents_scalarOf (validateKzgG1_of_validateKzgG1Point hb)
    (uncompressG1_of_validateKzgG1Point hb)).unique ha

/-- An accepted check from bytes decodes all four inputs, and the check of the points accepts. -/
theorem verifyKzgProof_eq_ok_true {s : TrustedSetup} {commitmentBytes proofBytes : Bytes48}
    {zBytes yBytes : Bytes32}
    (h : verifyKzgProof s commitmentBytes zBytes yBytes proofBytes = .ok true) :
    ∃ C P z y, validateKzgG1Point commitmentBytes = .ok C ∧
      validateKzgG1Point proofBytes = .ok P ∧ bytesToBlsField zBytes = .ok z ∧
      bytesToBlsField yBytes = .ok y ∧ verifyKzgProofImpl s C z y P = true := by
  unfold verifyKzgProof at h
  cases hC : validateKzgG1Point commitmentBytes with
  | error e =>
    rw [hC] at h
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | ok C =>
    cases hP : validateKzgG1Point proofBytes with
    | error e =>
      rw [hC, hP] at h
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      exact nomatch h
    | ok P =>
      cases hz : bytesToBlsField zBytes with
      | error e =>
        rw [hC, hP, hz] at h
        simp only [bind, Except.bind, pure, Except.pure] at h
        exact nomatch h
      | ok z =>
        cases hy : bytesToBlsField yBytes with
        | error e =>
          rw [hC, hP, hz, hy] at h
          simp only [bind, Except.bind, pure, Except.pure] at h
          exact nomatch h
        | ok y =>
          rw [hC, hP, hz, hy] at h
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          exact ⟨C, P, z, y, rfl, rfl, rfl, rfl, h⟩

/-- **Evaluation binding from bytes.**

Assume the pairing law and a well-formed setup of the secret `τ`.

Let the check accept one commitment at one point `z` with two values and two proofs.

Then the values agree, or the search on the decoded openings returns a solution for `τ`. -/
theorem findSdh_valid_bytes (laws : Bls.PairingLaws) {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitmentBytes proofBytes proofBytes' : Bytes48}
    {zBytes yBytes yBytes' : Bytes32}
    (h : verifyKzgProof s commitmentBytes zBytes yBytes proofBytes = .ok true)
    (h' : verifyKzgProof s commitmentBytes zBytes yBytes' proofBytes' = .ok true) :
    ∃ z y y' P P', bytesToBlsField zBytes = .ok z ∧ bytesToBlsField yBytes = .ok y ∧
      bytesToBlsField yBytes' = .ok y' ∧ validateKzgG1Point proofBytes = .ok P ∧
      validateKzgG1Point proofBytes' = .ok P' ∧
      (y = y' ∨ ∃ sol, findSdh z y y' P P' = some sol ∧ IsSdhSolution τ sol) := by
  obtain ⟨C, P, z, y, hC, hP, hz, hy, hv⟩ := verifyKzgProof_eq_ok_true h
  obtain ⟨C', P', z', y', hC', hP', hz', hy', hv'⟩ := verifyKzgProof_eq_ok_true h'
  obtain rfl : C = C' := Except.ok.inj (hC.symm.trans hC')
  obtain rfl : z = z' := Except.ok.inj (hz.symm.trans hz')
  obtain ⟨c, hrC⟩ := represents_of_validateKzgG1Point hC
  obtain ⟨w, hrP⟩ := represents_of_validateKzgG1Point hP
  obtain ⟨w', hrP'⟩ := represents_of_validateKzgG1Point hP'
  exact ⟨z, y, y', P, P', hz, hy, hy', hP, hP', findSdh_valid laws hs hrC hrP hrP' hv hv'⟩

end EthLib.Cryptography.Kzg
