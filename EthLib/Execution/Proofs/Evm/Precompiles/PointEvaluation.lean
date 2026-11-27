module

public import EthLib.Execution.Evm.Precompiles.PointEvaluation
public import EthLib.Cryptography.Proofs.Kzg.Binding
public import EthLib.Cryptography.Proofs.Kzg.TrustedSetup
import EthLib.Base.Proofs.Bytes
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: `Evm.Precompiles.PointEvaluation`

- A call succeeds exactly when four checks pass:
  - The call data has 192 bytes.
  - The gas covers 50000.
  - The versioned hash names the commitment.
  - The proof verifies.
- Every successful call returns the same 64 bytes: 4096, then the BLS12-381 group order.
- On the embedded setup, the check of the call is the KZG check of the cryptography layer.
- An accepted proof satisfies the opening equation `c - y = w (τ - z)` of a well-formed setup.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.PointEvaluation

open EthLib.Cryptography.Bls (Fr G1)
open EthLib.Base (Bytes32 readBytes)
open EthLib.Cryptography.Kzg (VersionedHash kzgCommitmentToVersionedHash TrustedSetup Bytes48
  validateKzgG1Point bytesToBlsField)

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
        (kzgCommitmentToVersionedHash ⟨readBytes data 96 48 (by simp [fits, INPUT_BYTES])⟩).bytes
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
      exact absurd (congrArg VersionedHash.mk h) hhash
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
          -- Equal versioned hashes have equal bytes.
          exact ⟨fits, by omega, congrArg (·.bytes) (Decidable.not_not.mp hhash), hverify, h.symm⟩
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
  code_injective PointEvaluationError.code

/-! ## The KZG check of the cryptography layer -/

/-- On the embedded setup, the check of the call agrees with the KZG check of the crypto layer.

The check of the call decodes `[tau]_2` alone.

The other one reads it from the decoded setup.

It assumes that the embedded setup decodes, as the other theorems about that setup do. -/
theorem verifyKzgProof_eq_ok_iff {s : TrustedSetup} (hs : TrustedSetup.ofHex = .ok s)
    (commitment : Bytes48) (z y : Bytes32) (proof : Bytes48) (b : Bool) :
    verifyKzgProof commitment z y proof = .ok b ↔
      Cryptography.Kzg.verifyKzgProof s commitment z y proof = .ok b := by
  unfold verifyKzgProof Cryptography.Kzg.verifyKzgProof
  -- `[tau]_2` decoded alone is point 1 of the decoded setup.
  rw [TrustedSetup.g2MonomialOfHex_eq hs 1 (by decide)]
  -- Both checks decode the commitment, `z`, `y`, then the proof, and fail on the same input.
  cases hC : validateKzgG1Point commitment with
  | error e =>
    rw [Cryptography.Kzg.bytesToKzgCommitment_of_validateKzgG1Point_error hC]
    simp [Except.mapError, bind, Except.bind]
  | ok C =>
    rw [Cryptography.Kzg.bytesToKzgCommitment_of_validateKzgG1Point hC]
    simp only [Except.mapError, bind, Except.bind, bytesToBlsField]
    cases hz : Fr.fromBytesBE z with
    | error e => simp
    | ok zF =>
      cases hy : Fr.fromBytesBE y with
      | error e => simp
      | ok yF =>
        cases hP : validateKzgG1Point proof with
        | error e =>
          rw [Cryptography.Kzg.bytesToKzgProof_of_validateKzgG1Point_error hP]
          simp
        | ok P =>
          -- Valid bytes decode to the points that validation returned.
          rw [Cryptography.Kzg.bytesToKzgProof_of_validateKzgG1Point hP]
          simp only
          rw [Cryptography.Kzg.uncompressG1_of_validateKzgG1Point hC,
            Cryptography.Kzg.uncompressG1_of_validateKzgG1Point hP]
          -- Both run the pairing check with point 1 of the `G2` setup as `[tau]_2`.
          simp only [pure, Except.pure, Cryptography.Kzg.verifyKzgProofImpl, Except.ok.injEq]

/-- On the embedded setup, a call succeeds exactly when the cryptography layer's KZG check accepts.

The other checks are the length of 192 bytes, the gas of 50000 and the versioned hash.

It assumes that the embedded setup decodes. -/
theorem pointEvaluation_eq_ok_iff_kzg {s : TrustedSetup} (hs : TrustedSetup.ofHex = .ok s)
    (data : ByteArray) (gas : Nat) (out : ByteArray) :
    pointEvaluation data gas = .ok out ↔
      ∃ fits : data.size = INPUT_BYTES, GAS_POINT_EVALUATION ≤ gas ∧
        (kzgCommitmentToVersionedHash ⟨readBytes data 96 48 (by simp [fits, INPUT_BYTES])⟩).bytes
          = readBytes data 0 32 (by simp [fits, INPUT_BYTES]) ∧
        Cryptography.Kzg.verifyKzgProof s (readBytes data 96 48 (by simp [fits, INPUT_BYTES]))
          (readBytes data 32 32 (by simp [fits, INPUT_BYTES]))
          (readBytes data 64 32 (by simp [fits, INPUT_BYTES]))
          (readBytes data 144 48 (by simp [fits, INPUT_BYTES])) = .ok true ∧
        out = output := by
  rw [pointEvaluation_eq_ok_iff]
  simp only [verifyKzgProof_eq_ok_iff hs]

/-- On the embedded setup, well formed for the secret `τ`, a successful call opens the commitment.

The commitment and the proof decode to points that represent `c` and `w`.

The fields `z` and `y` decode to elements of the scalar field.

Then `c - y = w (τ - z)`, the equation of a KZG opening of `c` at `z` to `y`.

It assumes that the embedded setup decodes, and that it is well formed for `τ` (assumption D3). -/
theorem pointEvaluation_opening {s : TrustedSetup} {τ : Fr} (hs : TrustedSetup.ofHex = .ok s)
    (hw : s.WellFormed τ) {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : pointEvaluation data gas = .ok out) :
    ∃ fits : data.size = INPUT_BYTES, ∃ C P c w z y,
      validateKzgG1Point (readBytes data 96 48 (by simp [fits, INPUT_BYTES])) = .ok C ∧
      G1.Represents C c ∧
      validateKzgG1Point (readBytes data 144 48 (by simp [fits, INPUT_BYTES])) = .ok P ∧
      G1.Represents P w ∧
      bytesToBlsField (readBytes data 32 32 (by simp [fits, INPUT_BYTES])) = .ok z ∧
      bytesToBlsField (readBytes data 64 32 (by simp [fits, INPUT_BYTES])) = .ok y ∧
      c - y = w * (τ - z) := by
  obtain ⟨fits, -, -, hv, -⟩ := (pointEvaluation_eq_ok_iff_kzg hs data gas out).mp h
  obtain ⟨C, P, z, y, hC, hP, hz, hy, hacc⟩ := Cryptography.Kzg.verifyKzgProof_eq_ok_true hv
  -- Points that pass KZG validation lie in the subgroup, so each represents a scalar.
  obtain ⟨c, hrC⟩ := Cryptography.Kzg.represents_of_validateKzgG1Point hC
  obtain ⟨w, hrP⟩ := Cryptography.Kzg.represents_of_validateKzgG1Point hP
  exact ⟨fits, C, P, c, w, z, y, hC, hrC, hP, hrP, hz, hy,
    (Cryptography.Kzg.verifyKzgProofImpl_iff hw hrC hrP z y).mp hacc⟩

end EthLib.Execution.Evm.Precompiles.PointEvaluation
