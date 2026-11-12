module

public import EthLib.Execution.Evm.Precompiles.PointEvaluation
import EthLib.Cryptography.Proofs.Kzg.TrustedSetup

/-!
# Proofs: `Evm.Precompiles.PointEvaluation`

- A call succeeds exactly when the call data has 192 bytes, the gas covers 50000, the versioned hash names the commitment and the proof verifies.
- Every successful call returns the same 64 bytes: 4096, then the BLS12-381 group order.
- When the embedded setup decodes, the setup point `[tau]_2` of the call is its `G2` point 1.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.PointEvaluation

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg (kzgCommitmentToVersionedHash)

/-- Call data of any other length than 192 bytes fails before the gas is charged. -/
theorem pointEvaluation_invalidInputLength {data : ByteArray} (hsize : data.size ≠ INPUT_BYTES) (gas : Nat) :
    pointEvaluation data gas = .error (.invalidInputLength data.size) := by
  simp [pointEvaluation, hsize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- 192 bytes with less than 50000 gas run out of gas. -/
theorem pointEvaluation_outOfGas {data : ByteArray} (hsize : data.size = INPUT_BYTES) {gas : Nat}
    (hgas : gas < GAS_POINT_EVALUATION) :
    pointEvaluation data gas = .error (.outOfGas GAS_POINT_EVALUATION gas) := by
  simp [pointEvaluation, hsize, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A call succeeds exactly when every check passes, and then returns `output`. -/
theorem pointEvaluation_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    pointEvaluation data gas = .ok out ↔
      data.size = INPUT_BYTES ∧ GAS_POINT_EVALUATION ≤ gas ∧
      (kzgCommitmentToVersionedHash (data.extract 96 144)).toArray = (data.extract 0 32).data ∧
      verifyKzgProof (data.extract 96 144) (data.extract 32 64) (data.extract 64 96) (data.extract 144 192)
        = .ok true ∧
      out = output := by
  simp only [pointEvaluation, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  -- Each check, in order: it either fails the call or lets it go on.
  split
  · rename_i hsize
    simp only [reduceCtorEq, false_iff, not_and]
    intro h
    exact absurd h hsize
  split
  · rename_i hsize hgas
    simp only [reduceCtorEq, false_iff, not_and]
    intro _ h
    omega
  split
  · rename_i hsize hgas hhash
    simp only [reduceCtorEq, false_iff, not_and]
    intro _ _ h
    exact absurd h hhash
  rename_i hsize hgas hhash
  cases hverify : verifyKzgProof (data.extract 96 144) (data.extract 32 64) (data.extract 64 96) (data.extract 144 192) with
  | error e => simp
  | ok verified =>
    cases verified
    · simp
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, true_and]
      constructor
      · intro h
        exact ⟨Decidable.not_not.mp hsize, by omega, Decidable.not_not.mp hhash, h.symm⟩
      · intro h
        exact h.2.2.2.symm

/-- The order of the BLS12-381 groups, the value of `BLS_MODULUS` in EIP-4844. -/
theorem Fr_modulus : Fr.modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513 :=
  rfl

/-- The output, byte for byte: `4096` as a 32-byte word, then `BLS_MODULUS` as a 32-byte word. -/
theorem output_eq :
    output.data.toList =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10, 0x00,
       0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05,
       0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01] := by
  decide +kernel

/-- Two errors with one code come from one constructor. -/
theorem PointEvaluationError.code_injective (e₁ e₂ : PointEvaluationError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PointEvaluationError.code] at h; exact absurd h (by decide))

open EthLib.Cryptography.Kzg in
/-- The 96 bytes of the precompile's `[tau]_2` are entry 1 of `g2_monomial` in the embedded setup.

The definition of `[tau]_2` says that it is this entry, and this fact checks that claim.

It decodes one hex string of 192 characters. -/
private theorem hexToBytes_g2MonomialHex_one :
    (TrustedSetup.hexToBytes? (TrustedSetupData.g2MonomialHex[1]'(by decide))).map ByteArray.data =
      some KZG_SETUP_G2_MONOMIAL_1.data := by
  decide +kernel

open EthLib.Cryptography.Kzg in
/-- The setup point of the call decompresses to entry 1 of the `G2` points of the embedded setup.

It assumes that the embedded setup decodes, as the other theorems about that setup do.

So the `[tau]_2` of the precompile is the one that the KZG theorems about a decoded setup use. -/
theorem uncompress_KZG_SETUP_G2_MONOMIAL_1 {s : TrustedSetup} (h : TrustedSetup.ofHex = .ok s) :
    Cryptography.Bls.G2.uncompress KZG_SETUP_G2_MONOMIAL_1 = .ok (s.g2Monomial[1]'(by decide)) := by
  unfold TrustedSetup.ofHex at h
  -- The three lists stay abstract, so no step evaluates the decoding of the 8257 hex strings.
  generalize TrustedSetup.hexListToBytes TrustedSetupData.g1LagrangeHex = a at h
  generalize TrustedSetup.hexListToBytes TrustedSetupData.g1MonomialHex = b at h
  generalize hc : TrustedSetup.hexListToBytes TrustedSetupData.g2MonomialHex = c at h
  cases a with
  | error => cases h
  | ok a =>
  cases b with
  | error => cases h
  | ok b =>
  cases c with
  | error => cases h
  | ok c =>
  simp only [bind, Except.bind] at h
  obtain ⟨hc1, hu⟩ := TrustedSetup.ofBytes_g2Monomial h 1 (by decide)
  -- Entry 1 of the decoded list is the decoding of hex string 1, which is the constant.
  obtain ⟨-, hget⟩ := TrustedSetup.hexListToBytes_getElem hc
  have hg := hexToBytes_g2MonomialHex_one
  rw [hget 1 (by decide), Option.map_some, Option.some.injEq] at hg
  have hd : c[1]! = KZG_SETUP_G2_MONOMIAL_1 := ByteArray.ext hg
  rw [← hd, getElem!_pos c 1 hc1]
  exact hu

end EthLib.Execution.Evm.Precompiles.PointEvaluation
