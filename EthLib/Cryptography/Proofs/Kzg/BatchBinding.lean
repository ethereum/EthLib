module

public import EthLib.Cryptography.Proofs.Kzg.Binding
import EthLib.Cryptography.Proofs.Bls.PairingAte

/-!
# Proofs: binding of the batch check of KZG openings

The batch check combines `n` openings with the powers of a challenge `r`.

Opening `i` claims `p_i(z_i) = y_i`, with commitment `c_i` and proof `w_i`.

Its error is `c_i - y_i - w_i (τ - z_i)`, which is zero exactly when the single check accepts it.

For a well-formed setup, the batch check accepts exactly when `r` is a root of the error polynomial.

That polynomial is `P(X) = sum_i e_i X^i`, with `e_i` the error of opening `i`.

So an accepted batch has every opening valid, or `r` is a root of a nonzero `P`.

Take two valid openings of one commitment at one point, to two values.

The search of the single check then returns a strong Diffie–Hellman solution.

The challenge is a hash of the openings, so `P` is fixed before `r` is drawn.

A nonzero `P` has at most `n - 1` roots.

Let the hash be a random oracle, which the adversary queries `q` times.

It finds a root with probability at most `(q + 1) (n - 1) / |Fr|`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-- The polynomial `sum_{i < n} e_i X^i` of the errors `e_i` of `n` checks. -/
noncomputable def errorPoly (e : Nat → Fr) (n : Nat) : Fr[X] :=
  ∑ i ∈ Finset.range n, C (e i) * X ^ i

/-- Coefficient `i` of the error polynomial is the error of check `i`, below `n`. -/
theorem coeff_errorPoly (e : Nat → Fr) (n i : Nat) :
    (errorPoly e n).coeff i = if i < n then e i else 0 := by
  simp only [errorPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range n) i]
  simp only [Finset.mem_range]

/-- The error polynomial is zero exactly when every error is zero. -/
theorem errorPoly_eq_zero_iff (e : Nat → Fr) (n : Nat) :
    errorPoly e n = 0 ↔ ∀ i < n, e i = 0 := by
  constructor
  · intro h i hi
    have := coeff_errorPoly e n i
    rw [h, coeff_zero, ite_eq_left hi] at this
    exact this.symm
  · intro h
    ext i
    rw [coeff_errorPoly, coeff_zero]
    split
    · rename_i hi
      rw [h i hi]
    · rfl

/-- The error polynomial has degree at most `n - 1`. -/
theorem natDegree_errorPoly_le (e : Nat → Fr) (n : Nat) : (errorPoly e n).natDegree ≤ n - 1 := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [coeff_errorPoly, ite_eq_right (by omega)]

/-- The value of the error polynomial at `r`, as a sum. -/
theorem eval_errorPoly (e : Nat → Fr) (n : Nat) (r : Fr) :
    (errorPoly e n).eval r = ∑ i ∈ Finset.range n, e i * r ^ i := by
  simp [errorPoly, eval_finsetSum]

/-- The error of an opening: zero exactly when `c - y = w (τ - z)`. -/
def openingError (τ c y w z : Fr) : Fr := c - y - w * (τ - z)

/-- The error polynomial of a batch: `P(X) = sum_{i < n} X^i (c_i - y_i - w_i (τ - z_i))`. -/
noncomputable def batchErrorPoly (τ : Fr) (c y w z : Nat → Fr) (n : Nat) : Fr[X] :=
  errorPoly (fun i => openingError τ (c i) (y i) (w i) (z i)) n

/-- Coefficient `i` of the error polynomial is the error of opening `i`, below `n`. -/
theorem coeff_batchErrorPoly (τ : Fr) (c y w z : Nat → Fr) (n i : Nat) :
    (batchErrorPoly τ c y w z n).coeff i =
      if i < n then openingError τ (c i) (y i) (w i) (z i) else 0 :=
  coeff_errorPoly _ n i

/-- The error polynomial is zero exactly when every opening is valid. -/
theorem batchErrorPoly_eq_zero_iff (τ : Fr) (c y w z : Nat → Fr) (n : Nat) :
    batchErrorPoly τ c y w z n = 0 ↔ ∀ i < n, c i - y i = w i * (τ - z i) := by
  rw [batchErrorPoly, errorPoly_eq_zero_iff]
  exact forall₂_congr fun i _ => sub_eq_zero

/-- The error polynomial has degree at most `n - 1`. -/
theorem natDegree_batchErrorPoly_le (τ : Fr) (c y w z : Nat → Fr) (n : Nat) :
    (batchErrorPoly τ c y w z n).natDegree ≤ n - 1 :=
  natDegree_errorPoly_le _ n

/-- The value of the error polynomial at `r`, as a sum. -/
theorem eval_batchErrorPoly (τ : Fr) (c y w z : Nat → Fr) (n : Nat) (r : Fr) :
    (batchErrorPoly τ c y w z n).eval r =
      ∑ i ∈ Finset.range n, openingError τ (c i) (y i) (w i) (z i) * r ^ i :=
  eval_errorPoly _ n r

/-! ## The batch check -/

/-- One term of the identity of the check. -/
private theorem term_identity (c y w z t x : Fr) :
    (c - y - w * (t - z)) * x = x * w * -t + (x * (c + -y) + z * x * w) := by
  ring

/-- The factor `1` of the generator of `G2` drops out of the identity of the check. -/
private theorem add_mul_one_iff_zero {a b : Fr} : a + b * 1 = 0 ↔ a + b = 0 := by
  rw [mul_one]

/-- **The batch check returns a verdict on inputs of one size.**

Take commitments, their points, points `z`, values `y`, proofs and their points of one size.

Then the batch check returns a verdict, with no error. -/
theorem verifyKzgProofBatch_exists_ok (s : TrustedSetup)
    {commitments : Array KZGCommitment} {commitmentsG1 : Array G1}
    {zs ys : Array Fr} {proofs : Array KZGProof} {proofsG1 : Array G1}
    (h₁ : zs.size = commitments.size) (h₂ : ys.size = commitments.size)
    (h₃ : proofs.size = commitments.size) (h₄ : commitmentsG1.size = commitments.size)
    (h₅ : proofsG1.size = commitments.size) :
    ∃ b, verifyKzgProofBatch s commitments commitmentsG1 zs ys proofs proofsG1 = .ok b := by
  unfold verifyKzgProofBatch
  simp only [h₁, h₂, h₃, h₄, h₅, ne_eq, not_true_eq_false, ↓reduceIte]
  have hrp := size_computePowers (computeVerifyKzgProofBatchChallenge commitments zs ys proofs)
    commitments.size
  rw [g1LincombPoints_eq_msm (by rw [hrp, h₅]), g1LincombPoints_eq_msm (by simp [h₁, h₅]),
    g1LincombPoints_eq_msm (by simp [h₂, h₄])]
  exact ⟨_, rfl⟩

/-- **The batch check as a scalar identity.**

Assume a well-formed setup of the secret `τ`.

Let commitment `i` represent `c i` and proof `i` represent `w i`.

Let the batch check return the verdict `b`.

Then `b` is true exactly when the challenge is a root of the error polynomial. -/
theorem verifyKzgProofBatch_ok_iff_root {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitments : Array KZGCommitment} {commitmentsG1 : Array G1}
    {zs ys : Array Fr} {proofs : Array KZGProof} {proofsG1 : Array G1} {c w : Nat → Fr} {b : Bool}
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ i < proofsG1.size, G1.Represents proofsG1[i]! (w i))
    (h : verifyKzgProofBatch s commitments commitmentsG1 zs ys proofs proofsG1 = .ok b) :
    b = true ↔ (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size).eval
      (computeVerifyKzgProofBatchChallenge commitments zs ys proofs) = 0 := by
  unfold verifyKzgProofBatch at h
  by_cases h₁ : zs.size ≠ commitments.size
  · simp [h₁, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₂ : ys.size ≠ commitments.size
  · simp [h₁, h₂, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₃ : proofs.size ≠ commitments.size
  · simp [h₁, h₂, h₃, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₄ : commitmentsG1.size ≠ commitments.size
  · simp [h₁, h₂, h₃, h₄, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₅ : proofsG1.size ≠ commitments.size
  · simp [h₁, h₂, h₃, h₄, h₅, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  simp only [ne_eq, Decidable.not_not] at h₁ h₂ h₃ h₄ h₅
  simp only [h₁, h₂, h₃, h₄, h₅, ne_eq, not_true_eq_false, ↓reduceIte] at h
  have hrp := size_computePowers (computeVerifyKzgProofBatchChallenge commitments zs ys proofs)
    commitments.size
  rw [g1LincombPoints_eq_msm (by rw [hrp, h₅]), g1LincombPoints_eq_msm (by simp [h₁, h₅]),
    g1LincombPoints_eq_msm (by simp [h₂, h₄])] at h
  simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
  set r := computeVerifyKzgProofBatchChallenge commitments zs ys proofs
  set n := commitments.size
  set rp := computePowers r n
  set cm := Array.zipWith (fun commitmentG1 y => commitmentG1.add (G1.generator.mul (-y)))
    commitmentsG1 ys
  set zrp := Array.zipWith (fun x1 x2 => x1 * x2) zs rp
  have hpow : ∀ j < n, rp[j]! = r ^ j := fun j hj => by
    rw [getElem!_pos rp j (by rw [hrp]; exact hj), getElem_computePowers, Bls.Fr.powNat_eq_pow]
  have hcm : cm.size = n := by simp [cm, h₂, h₄]
  have hzrp : zrp.size = n := by simp [zrp, rp, h₁]
  -- The four points of the check, as combinations of the scalars.
  have hA := G1.represents_msm (scalars := rp) (by rw [hrp, h₅]) hP
  have hB := G1.represents_msm (scalars := rp) (a := fun j => c j + -ys[j]!) (by rw [hrp, hcm])
    fun j hj => by
      have hc := hC j (by omega)
      rw [getElem!_pos commitmentsG1 j (by omega)] at hc
      rw [getElem!_pos cm j hj, Array.getElem_zipWith, getElem!_pos ys j (by omega)]
      exact hc.add (G1.represents_mul_generator _)
  have hD := G1.represents_msm (scalars := zrp) (by rw [hzrp, h₅]) hP
  have hs2 : G2.Represents (s.g2Monomial[1]'(by decide)) τ := by
    have h := hs.monomial_g2 ⟨1, by decide⟩
    simp only [Fin.getElem_fin, pow_one] at h
    exact h
  have hid := Bls.pairingLaws.two_pairs hA hs2.neg (hB.add hD) G2.represents_generator
  rw [hcm, h₅] at hid
  subst h
  -- The value of the error polynomial at `r` is the left side of the identity of the check.
  have key : ∑ i ∈ Finset.range n, openingError τ (c i) ys[i]! (w i) zs[i]! * r ^ i =
      ∑ i ∈ Finset.range n, (rp[i]! * w i * -τ + (rp[i]! * (c i + -ys[i]!) + zrp[i]! * w i)) :=
    Finset.sum_congr rfl fun j hj => by
      have hj := Finset.mem_range.mp hj
      have hz : zrp[j]! = zs[j]! * r ^ j := by
        rw [getElem!_pos zrp j (by omega), Array.getElem_zipWith, getElem!_pos zs j (by omega),
          ← hpow j hj, getElem!_pos rp j (by omega)]
      rw [hpow j hj, hz, openingError]
      exact term_identity _ _ _ _ _ _
  refine hid.trans (add_mul_one_iff_zero.trans ?_)
  rw [eval_batchErrorPoly, key, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]

/-- **An accepted batch check has its challenge as a root.**

Under the hypotheses of the scalar identity, let the batch check accept.

Then its challenge is a root of the error polynomial. -/
theorem verifyKzgProofBatch_root {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitments : Array KZGCommitment} {commitmentsG1 : Array G1}
    {zs ys : Array Fr} {proofs : Array KZGProof} {proofsG1 : Array G1} {c w : Nat → Fr}
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ i < proofsG1.size, G1.Represents proofsG1[i]! (w i))
    (h : verifyKzgProofBatch s commitments commitmentsG1 zs ys proofs proofsG1 = .ok true) :
    (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size).eval
      (computeVerifyKzgProofBatchChallenge commitments zs ys proofs) = 0 :=
  (verifyKzgProofBatch_ok_iff_root hs hC hP h).mp rfl

/-- A batch that the check accepts has as many proofs as commitments. -/
theorem proofsG1_size_of_ok {s : TrustedSetup} {commitments : Array KZGCommitment}
    {commitmentsG1 : Array G1} {zs ys : Array Fr} {proofs : Array KZGProof} {proofsG1 : Array G1}
    {b : Bool} (h : verifyKzgProofBatch s commitments commitmentsG1 zs ys proofs proofsG1 = .ok b) :
    proofsG1.size = commitments.size := by
  unfold verifyKzgProofBatch at h
  by_cases h₁ : zs.size ≠ commitments.size
  · simp [h₁, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₂ : ys.size ≠ commitments.size
  · simp [h₁, h₂, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₃ : proofs.size ≠ commitments.size
  · simp [h₁, h₂, h₃, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₄ : commitmentsG1.size ≠ commitments.size
  · simp [h₁, h₂, h₃, h₄, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_contra h₅
  simp [h₁, h₂, h₃, h₄, h₅, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- **An accepted batch is valid, or its challenge is a root.**

Take the hypotheses of the scalar identity.

Then every opening of an accepted batch satisfies `c_i - y_i = w_i (τ - z_i)`.

Otherwise the error polynomial is not zero, and the challenge is one of its roots. -/
theorem verifyKzgProofBatch_valid_or_root {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitments : Array KZGCommitment} {commitmentsG1 : Array G1}
    {zs ys : Array Fr} {proofs : Array KZGProof} {proofsG1 : Array G1} {c w : Nat → Fr}
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ i < proofsG1.size, G1.Represents proofsG1[i]! (w i))
    (h : verifyKzgProofBatch s commitments commitmentsG1 zs ys proofs proofsG1 = .ok true) :
    (∀ i < commitments.size, c i - ys[i]! = w i * (τ - zs[i]!)) ∨
      (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size ≠ 0 ∧
        (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size).eval
          (computeVerifyKzgProofBatchChallenge commitments zs ys proofs) = 0) := by
  by_cases hzero : batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size = 0
  · exact Or.inl ((batchErrorPoly_eq_zero_iff τ c _ w _ _).mp hzero)
  · exact Or.inr ⟨hzero, verifyKzgProofBatch_root hs hC hP h⟩

/-! ## Binding -/

/-- **Binding inside one batch.**

Let an accepted batch open two commitments that represent one scalar, at one point.

Then one of three cases holds.

- The two values agree.
- The search on the two openings returns a strong Diffie–Hellman solution for `τ`.
- The challenge is a root of the error polynomial, which is not zero. -/
theorem verifyKzgProofBatch_binding {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitments : Array KZGCommitment} {commitmentsG1 : Array G1}
    {zs ys : Array Fr} {proofs : Array KZGProof} {proofsG1 : Array G1} {c w : Nat → Fr}
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ i < proofsG1.size, G1.Represents proofsG1[i]! (w i))
    (h : verifyKzgProofBatch s commitments commitmentsG1 zs ys proofs proofsG1 = .ok true)
    {i j : Nat} (hi : i < commitments.size) (hj : j < commitments.size)
    (hc : c i = c j) (hz : zs[i]! = zs[j]!) :
    ys[i]! = ys[j]! ∨
      (∃ sol, findSdh zs[i]! ys[i]! ys[j]! proofsG1[i]! proofsG1[j]! = some sol ∧
        IsSdhSolution τ sol) ∨
      (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size ≠ 0 ∧
        (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size).eval
          (computeVerifyKzgProofBatchChallenge commitments zs ys proofs) = 0) := by
  by_cases hne : ys[i]! = ys[j]!
  · exact Or.inl hne
  rcases verifyKzgProofBatch_valid_or_root hs hC hP h with hall | hroot
  · -- The batch has as many proofs as commitments, or it would not be accepted.
    have hsize : proofsG1.size = commitments.size := proofsG1_size_of_ok h
    have hid := hall i hi
    have hid' := hall j hj
    rw [← hc, ← hz] at hid'
    exact Or.inr (Or.inl (findSdh_valid_of_identity (hP i (by omega)) (hP j (by omega)) hne
      hid hid'))
  · exact Or.inr (Or.inr hroot)

/-- **Binding between a batch and a single check.**

Let an accepted batch open commitment `i` at `z`.

Let the single check accept a commitment that represents the same scalar, at `z`.

Then one of three cases holds.

- The two values agree.
- The search on the two openings returns a strong Diffie–Hellman solution for `τ`.
- The challenge of the batch is a root of its error polynomial, which is not zero. -/
theorem verifyKzgProofBatch_binding_single {s : TrustedSetup} {τ : Fr}
    (hs : s.WellFormed τ) {commitments : Array KZGCommitment} {commitmentsG1 : Array G1}
    {zs ys : Array Fr} {proofs : Array KZGProof} {proofsG1 : Array G1} {c w : Nat → Fr}
    (hC : ∀ i < commitmentsG1.size, G1.Represents commitmentsG1[i]! (c i))
    (hP : ∀ i < proofsG1.size, G1.Represents proofsG1[i]! (w i))
    (h : verifyKzgProofBatch s commitments commitmentsG1 zs ys proofs proofsG1 = .ok true)
    {i : Nat} (hi : i < commitments.size) {C P : G1} {w' y : Fr}
    (hC' : G1.Represents C (c i)) (hP' : G1.Represents P w')
    (h' : verifyKzgProofImpl s C zs[i]! y P = true) :
    ys[i]! = y ∨
      (∃ sol, findSdh zs[i]! ys[i]! y proofsG1[i]! P = some sol ∧ IsSdhSolution τ sol) ∨
      (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size ≠ 0 ∧
        (batchErrorPoly τ c (ys[·]!) w (zs[·]!) commitments.size).eval
          (computeVerifyKzgProofBatchChallenge commitments zs ys proofs) = 0) := by
  by_cases hne : ys[i]! = y
  · exact Or.inl hne
  rcases verifyKzgProofBatch_valid_or_root hs hC hP h with hall | hroot
  · have hsize : proofsG1.size = commitments.size := proofsG1_size_of_ok h
    exact Or.inr (Or.inl (findSdh_valid_of_identity (hP i (by omega)) hP' hne (hall i hi)
      ((verifyKzgProofImpl_iff hs hC' hP' zs[i]! y).mp h')))
  · exact Or.inr (Or.inr hroot)

end EthLib.Cryptography.Kzg
