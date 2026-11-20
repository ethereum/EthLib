module

public import EthLib.Execution.Evm.Precompiles.PointEvaluation
import EthLib.Base.Proofs.Bytes

/-!
# Proofs: `Evm.Precompiles.PointEvaluation`

- A call succeeds exactly when the call data has 192 bytes, the gas covers 50000, the versioned hash names the commitment and the proof verifies.
- Every successful call returns the same 64 bytes: 4096, then the BLS12-381 group order.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.PointEvaluation

open EthLib.Cryptography.Bls (Fr)
open EthLib.Base (readBytes)
open EthLib.Cryptography.Kzg (kzgCommitmentToVersionedHash)

/-- Call data of any other length than 192 bytes fails before the gas is charged. -/
theorem pointEvaluation_invalidInputLength {data : ByteArray} (hsize : data.size ≠ INPUT_BYTES) (gas : Nat) :
    pointEvaluation data gas = .error (.invalidInputLength data.size) := by
  simp [pointEvaluation, hsize]

/-- 192 bytes with less than 50000 gas run out of gas. -/
theorem pointEvaluation_outOfGas {data : ByteArray} (hsize : data.size = INPUT_BYTES) {gas : Nat}
    (hgas : gas < GAS_POINT_EVALUATION) :
    pointEvaluation data gas = .error (.outOfGas GAS_POINT_EVALUATION gas) := by
  simp [pointEvaluation, hsize, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A call succeeds exactly when every check passes, and then returns `output`.

The fields start at bytes 0, 32, 64, 96 and 144, as in "Point evaluation precompile" of EIP-4844. -/
theorem pointEvaluation_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    pointEvaluation data gas = .ok out ↔
      ∃ fits : data.size = INPUT_BYTES, GAS_POINT_EVALUATION ≤ gas ∧
        kzgCommitmentToVersionedHash (readBytes data 96 48 (by simp [fits, INPUT_BYTES]))
          = readBytes data 0 32 (by simp [fits, INPUT_BYTES]) ∧
        verifyKzgProof (readBytes data 96 48 (by simp [fits, INPUT_BYTES]))
          (readBytes data 32 32 (by simp [fits, INPUT_BYTES]))
          (readBytes data 64 32 (by simp [fits, INPUT_BYTES]))
          (readBytes data 144 48 (by simp [fits, INPUT_BYTES])) = .ok true ∧
        out = output := by
  unfold pointEvaluation
  by_cases fits : data.size = INPUT_BYTES
  · rw [dite_eq_left fits]
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
    -- Each check, in order: it either fails the call or lets it go on.
    split
    · rename_i hgas
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro _ h
      omega
    split
    · rename_i hgas hhash
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro _ _ h
      exact absurd h hhash
    rename_i hgas hhash
    split
    · rename_i e _
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro _ _ _ h
      simp_all
    · rename_i verified hverify
      cases verified
      · simp only [Bool.not_false, ↓reduceIte, reduceCtorEq, false_iff, not_exists, not_and]
        intro _ _ _ h
        simp_all
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq]
        constructor
        · intro h
          exact ⟨fits, by omega, Decidable.not_not.mp hhash, hverify, h.symm⟩
        · intro ⟨_, _, _, _, h⟩
          exact h.symm
  · rw [dite_eq_right fits]
    simp only [reduceCtorEq, false_iff, not_exists]
    intro h
    exact absurd h fits

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

end EthLib.Execution.Evm.Precompiles.PointEvaluation
