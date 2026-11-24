module

public import EthLib.Execution.Evm.Precompiles.Ripemd160
public import EthLib.Cryptography.Proofs.Hash.Ripemd160
public import EthLib.Base.Proofs.Except
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Ripemd160`

- The output of the precompile at address `0x03` is 32 bytes: twelve zero bytes, then the RIPEMD-160 digest.
- A call succeeds exactly when the gas covers `600 + 120 * ceil(len / 32)`, and then returns that output.
- The price grows with the size, and fits in 64 bits below 2^62 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ripemd160

open EthLib.Cryptography.Hash
open EthLib.Execution.Evm (wordPrice_eq wordPrice_mono wordPrice_le)

/-- The padding is twelve bytes. -/
private theorem padding_size :
    (ByteArray.mk (Array.replicate (OUTPUT_BYTES - DIGEST_BYTES) 0)).size = 12 := by
  simp [ByteArray.size, OUTPUT_BYTES, DIGEST_BYTES]

/-- The digest is 20 bytes. -/
private theorem digest_size (data : ByteArray) :
    (Base.packBytes (Cryptography.Hash.ripemd160 data)).size = 20 := by
  simp [Base.packBytes, ByteArray.size]

/-- The output is 32 bytes, whatever the call data. -/
@[simp] theorem output_size (data : ByteArray) : (output data).size = OUTPUT_BYTES := by
  unfold output
  rw [ByteArray.size_append, padding_size, digest_size]
  rfl

/-- The first twelve bytes are zero. -/
theorem output_leading_zeros (data : ByteArray) (i : Nat) (within : i < 12) :
    (output data)[i]'(by rw [output_size]; simp [OUTPUT_BYTES]; omega) = 0 := by
  -- Name the bound, so it unfolds together with the output.
  have bound : i < (output data).size := by rw [output_size]; simp [OUTPUT_BYTES]; omega
  change (output data)[i]'bound = 0
  unfold EthLib.Execution.Evm.Precompiles.Ripemd160.output at bound ⊢
  -- The zeros are the left part of the concatenation.
  rw [ByteArray.getElem_append_left (by rw [padding_size]; exact within)]
  simp [ByteArray.getElem_eq_getElem_data]

/-- The last twenty bytes are the RIPEMD-160 digest. -/
theorem output_digest (data : ByteArray) (i : Nat) (within : i < 20) :
    (output data)[12 + i]'(by rw [output_size]; simp [OUTPUT_BYTES]; omega) =
      (Cryptography.Hash.ripemd160 data)[i]'within := by
  -- Unfold the output with simp, which carries the index bound along.
  simp only [EthLib.Execution.Evm.Precompiles.Ripemd160.output]
  -- The digest is the right part of the concatenation, after the twelve zeros.
  rw [ByteArray.getElem_append_right (by rw [padding_size]; omega)]
  simp [padding_size, Base.packBytes, ByteArray.getElem_eq_getElem_data]

/-! ## The price -/

/-- The price in closed form, `600 + 120 * ceil(size / 32)`. -/
theorem gasCost_eq (size : Nat) : gasCost size = 600 + 120 * ((size + 31) / 32) :=
  wordPrice_eq _ _ size

/-- Longer call data never costs less. -/
theorem gasCost_mono {short long : Nat} (le : short ≤ long) : gasCost short ≤ gasCost long :=
  wordPrice_mono _ _ le

/-- Below 2^62 bytes of call data, the price fits in 64 bits.

So a call with a 64-bit gas amount can pay it.

Some call data shorter than 2^63 bytes costs at least 2^64, so the bound is 2^62. -/
theorem gasCost_lt_two_pow_64 {size : Nat} (bounded : size < 2 ^ 62) : gasCost size < 2 ^ 64 := by
  -- Such call data fits in 2^57 words.
  have covers : size ≤ 32 * 2 ^ 57 := by
    have : (2 : Nat) ^ 62 = 32 * 2 ^ 57 := by decide
    omega
  exact Nat.lt_of_le_of_lt (wordPrice_le _ _ covers) (by decide)

/-- A call succeeds exactly when the gas covers the price, and then returns the output. -/
theorem ripemd160_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    ripemd160 data gas = .ok out ↔ gasCost data.size ≤ gas ∧ out = output data := by
  unfold ripemd160
  exact Base.ite_lt_eq_ok_iff

/-- A call fails exactly when the gas is below the price, and the error carries both. -/
theorem ripemd160_eq_error_iff (data : ByteArray) (gas : Nat) (e : Ripemd160Error) :
    ripemd160 data gas = .error e ↔
      gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas := by
  unfold ripemd160
  exact Base.ite_lt_eq_error_iff

/-- Two errors with one code come from one constructor. -/
theorem Ripemd160Error.code_injective (e₁ e₂ : Ripemd160Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- The error type has one constructor, so both errors have its index.
  cases e₁
  cases e₂
  rfl

end EthLib.Execution.Evm.Precompiles.Ripemd160
