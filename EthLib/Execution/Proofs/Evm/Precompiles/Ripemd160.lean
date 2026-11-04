module

public import EthLib.Execution.Evm.Precompiles.Ripemd160
public import EthLib.Cryptography.Proofs.Hash.Ripemd160
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Ripemd160`

- The output of the precompile at address `0x03` is 32 bytes: twelve zero bytes, then the RIPEMD-160 digest.
- A call succeeds exactly when the gas covers `600 + 120 * ceil(len / 32)`, and then returns that output.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ripemd160

open EthLib.Cryptography.Hash

/-- The padding is twelve bytes. -/
private theorem padding_size :
    (ByteArray.mk (Array.replicate (OUTPUT_BYTES - DIGEST_BYTES) 0)).size = 12 := by
  simp [ByteArray.size, OUTPUT_BYTES, DIGEST_BYTES]

/-- The digest is 20 bytes. -/
private theorem digest_size (data : ByteArray) : (Cryptography.Hash.ripemd160 data).size = 20 :=
  Ripemd160.hash_size data

/-- The output is 32 bytes, whatever the call data. -/
@[simp] theorem ripemd160_size (data : ByteArray) : (ripemd160 data).size = OUTPUT_BYTES := by
  unfold ripemd160
  rw [ByteArray.size_append, padding_size, digest_size]
  rfl

/-- The first twelve bytes are zero. -/
theorem ripemd160_leading_zeros (data : ByteArray) (i : Nat) (within : i < 12) :
    (ripemd160 data)[i]'(by rw [ripemd160_size]; simp [OUTPUT_BYTES]; omega) = 0 := by
  -- Name the bound, so it unfolds together with the output.
  have bound : i < (ripemd160 data).size := by rw [ripemd160_size]; simp [OUTPUT_BYTES]; omega
  change (ripemd160 data)[i]'bound = 0
  unfold EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 at bound ⊢
  -- The zeros are the left part of the concatenation.
  rw [ByteArray.getElem_append_left (by rw [padding_size]; exact within)]
  simp [ByteArray.getElem_eq_getElem_data]

/-- The last twenty bytes are the RIPEMD-160 digest. -/
theorem ripemd160_digest (data : ByteArray) (i : Nat) (within : i < 20) :
    (ripemd160 data)[12 + i]'(by rw [ripemd160_size]; simp [OUTPUT_BYTES]; omega) =
      (Cryptography.Hash.ripemd160 data)[i]'(by rw [digest_size]; omega) := by
  -- Unfold the output with simp, which carries the index bound along.
  simp only [EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160]
  -- The digest is the right part of the concatenation, after the twelve zeros.
  rw [ByteArray.getElem_append_right (by rw [padding_size]; omega)]
  simp [padding_size]

/-! ## The price -/

/-- The price in closed form, `600 + 120 * ceil(size / 32)`. -/
theorem gasCost_eq (size : Nat) : gasCost size = 600 + 120 * ((size + 31) / 32) := by
  rw [gasCost, EthLib.Execution.Evm.wordCount_eq]
  rfl

/-- A call succeeds exactly when the gas covers the price, and then returns the output. -/
theorem call_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    call data gas = .ok out ↔ gasCost data.size ≤ gas ∧ out = ripemd160 data := by
  unfold call
  by_cases short : gas < gasCost data.size
  · simp only [short, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    omega
  · simp only [short, ↓reduceIte, Except.ok.injEq]
    exact ⟨fun h => ⟨by omega, h.symm⟩, fun h => h.2.symm⟩

/-- A call fails exactly when the gas is below the price, and the error carries both. -/
theorem call_eq_error_iff (data : ByteArray) (gas : Nat) (e : Ripemd160Error) :
    call data gas = .error e ↔ gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas := by
  unfold call
  by_cases short : gas < gasCost data.size
  · simp only [short, ↓reduceIte, Except.error.injEq, true_and]
    exact eq_comm
  · simp [short]

/-- Two errors with one code come from one constructor. -/
theorem Ripemd160Error.code_injective (e₁ e₂ : Ripemd160Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Ripemd160Error.code] at h; exact absurd h (by decide))

end EthLib.Execution.Evm.Precompiles.Ripemd160
