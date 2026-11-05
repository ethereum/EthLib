module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Code
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Counter
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Uniform

/-!
# What one encoding trial rejects

One trial of the counter search keeps the low 128 bits of a uniform answer.

Those bits are a uniform digest, so a trial accepts exactly when a uniform digest decodes.

At least `2^114` of the `2^128` digests decode.

So a trial rejects at most `1 - 2^-14` of the answers.
-/

@[expose] public section

open Finset ENNReal OracleComp OracleSpec

namespace SphincsSecurity.Completeness

variable [Params]

open TargetSum

omit [Params] in
/-- A trial accepts with probability the share of digests that decode. -/
theorem probEvent_accept :
    Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[(decodeDigest (truncateHash u)).isSome]
      = ((univ.filter fun d : Digest => (decodeDigest d).isSome).card : ℝ≥0∞)
          / (Fintype.card Digest : ℝ≥0∞) := by
  rw [← SphincsSecurity.probEvent_uniform_truncateHash_mem
    (univ.filter fun d : Digest => (decodeDigest d).isSome)]
  exact prEvent_congr _ _ _ fun u => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [Params] in
/-- One trial rejects at most `1 - 2^-14` of the answers. -/
theorem failMass_encoding_add_le :
    failMass (fun out => decodeDigest (truncateHash out)) + ((2 : ℝ≥0∞) ^ 14)⁻¹ ≤ 1 := by
  obtain ⟨accepted, haccepted⟩ :
      ∃ n, (univ.filter fun d : Digest => (decodeDigest d).isSome).card = n := ⟨_, rfl⟩
  have hnat : (2 : Nat) ^ 114 ≤ accepted := haccepted ▸ two_pow_le_card_accepting
  have hcard : (Fintype.card Digest : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
    rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hreject : Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[¬ (decodeDigest
        (truncateHash u)).isSome = true]
      = failMass (fun out => decodeDigest (truncateHash out)) := by
    rw [failMass_eq_probEvent]
    exact prEvent_congr _ _ _ fun u => by cases decodeDigest (truncateHash u) <;> simp
  have hmass : failMass (fun out => decodeDigest (truncateHash out))
      = 1 - (accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
    rw [← hreject, prEvent_not_eq_one_sub, probEvent_accept, hcard, haccepted]
  have hle : (accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 ≤ 1 := by
    rw [← haccepted, ← hcard, ← probEvent_accept]
    exact prEvent_le_one _
  have hshare : ((2 : ℝ≥0∞) ^ 14)⁻¹ ≤ (accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)),
      show (2 : ℝ≥0∞) ^ 128 = 2 ^ 14 * 2 ^ 114 by rw [← pow_add],
      ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    exact_mod_cast hnat
  rw [hmass]
  exact (add_le_add le_rfl hshare).trans_eq (tsub_add_cancel_of_le hle)

end SphincsSecurity.Completeness
