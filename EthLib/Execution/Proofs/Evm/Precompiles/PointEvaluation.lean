module

public import EthLib.Execution.Evm.Precompiles.PointEvaluation
public import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: `Evm.Precompiles.PointEvaluation`

- A call succeeds exactly when the call data has 192 bytes, the gas covers 50000, the versioned hash names the commitment and the proof verifies.
- Every successful call returns the same 64 bytes: 4096, then the BLS12-381 group order.
- The versioned hash has 32 bytes, and starts with the version `0x01`.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.PointEvaluation

open EthLib.Cryptography.Bls (Fr)

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
      (kzgCommitmentToVersionedHash (data.extract 96 144)).data.toList = (data.extract 0 32).data.toList ∧
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

/-- The versioned hash of every commitment has 32 bytes and starts with `0x01`. -/
theorem kzgCommitmentToVersionedHash_shape (commitment : ByteArray) :
    (kzgCommitmentToVersionedHash commitment).size = 32 ∧
      (kzgCommitmentToVersionedHash commitment).data.toList.head? = some VERSIONED_HASH_VERSION_KZG := by
  have hsize := Cryptography.Hash.Sha256.hash_size commitment
  constructor
  · simp [kzgCommitmentToVersionedHash, Cryptography.Hash.sha256, ByteArray.size_append, ByteArray.size_extract,
      hsize]
    rfl
  · simp [kzgCommitmentToVersionedHash]

/-! ## Known answers

Each length and price is worked out by hand. -/

/-- 191 bytes are one short: the call fails before the gas is charged. -/
theorem pointEvaluation_191 : pointEvaluation ⟨.replicate 191 0⟩ 50000 = .error (.invalidInputLength 191) :=
  pointEvaluation_invalidInputLength (by simp [ByteArray.size, INPUT_BYTES]) 50000

/-- 192 bytes with 49999 gas run out of gas. -/
theorem pointEvaluation_49999 :
    pointEvaluation ⟨.replicate 192 0⟩ 49999 = .error (.outOfGas 50000 49999) :=
  pointEvaluation_outOfGas (by simp [ByteArray.size, INPUT_BYTES]) (by decide)

end EthLib.Execution.Evm.Precompiles.PointEvaluation
