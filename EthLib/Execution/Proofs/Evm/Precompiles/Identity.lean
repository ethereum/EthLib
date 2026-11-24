module

public import EthLib.Execution.Evm.Precompiles.Identity
public import EthLib.Base.Proofs.Except
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Evm.Precompiles.Identity`

- A call succeeds exactly when the gas covers `15 + 3 * ceil(len / 32)`, and then returns its call data.
- A call fails exactly when the gas is below that price.
- The price grows with the size, and fits in 64 bits below 2^63 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Identity

open EthLib.Execution.Evm (wordPrice_eq wordPrice_mono wordPrice_le)

/-- The price in closed form, `15 + 3 * ceil(size / 32)`. -/
theorem gasCost_eq (size : Nat) : gasCost size = 15 + 3 * ((size + 31) / 32) :=
  wordPrice_eq _ _ size

/-- Longer call data never costs less. -/
theorem gasCost_mono {short long : Nat} (le : short ≤ long) : gasCost short ≤ gasCost long :=
  wordPrice_mono _ _ le

/-- Below 2^63 bytes of call data, the price fits in 64 bits.

So a call with a 64-bit gas amount can pay it. -/
theorem gasCost_lt_two_pow_64 {size : Nat} (bounded : size < 2 ^ 63) : gasCost size < 2 ^ 64 := by
  -- Such call data fits in 2^58 words.
  have covers : size ≤ 32 * 2 ^ 58 := by
    have : (2 : Nat) ^ 63 = 32 * 2 ^ 58 := by decide
    omega
  exact Nat.lt_of_le_of_lt (wordPrice_le _ _ covers) (by decide)

/-- A call succeeds exactly when the gas covers the price, and then returns its call data. -/
theorem identity_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    identity data gas = .ok out ↔ gasCost data.size ≤ gas ∧ out = data := by
  unfold identity
  exact Base.ite_lt_eq_ok_iff

/-- A call fails exactly when the gas is below the price, and the error carries both. -/
theorem identity_eq_error_iff (data : ByteArray) (gas : Nat) (e : IdentityError) :
    identity data gas = .error e ↔ gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas := by
  unfold identity
  exact Base.ite_lt_eq_error_iff

/-- Two errors with one code come from one constructor. -/
theorem IdentityError.code_injective (e₁ e₂ : IdentityError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [IdentityError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Evm.Precompiles.Identity
