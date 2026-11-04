module

public import EthLib.Execution.Evm.Precompiles.Identity
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Evm.Precompiles.Identity`

- A call succeeds exactly when the gas covers `15 + 3 * ceil(len / 32)`, and then returns its call data.
- A call fails exactly when the gas is below that price.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Identity

open EthLib.Execution.Evm (wordCount_eq)

/-- The price in closed form, `15 + 3 * ceil(size / 32)`. -/
theorem gasCost_eq (size : Nat) : gasCost size = 15 + 3 * ((size + 31) / 32) := by
  rw [gasCost, wordCount_eq]
  rfl

/-- A call succeeds exactly when the gas covers the price, and then returns its call data. -/
theorem identity_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    identity data gas = .ok out ↔ gasCost data.size ≤ gas ∧ out = data := by
  unfold identity
  by_cases short : gas < gasCost data.size
  · simp only [short, ↓reduceIte, reduceCtorEq, false_iff, not_and]
    omega
  · simp only [short, ↓reduceIte, Except.ok.injEq]
    constructor
    · intro h
      exact ⟨by omega, h.symm⟩
    · intro h
      exact h.2.symm

/-- A call fails exactly when the gas is below the price, and the error carries both. -/
theorem identity_eq_error_iff (data : ByteArray) (gas : Nat) (e : IdentityError) :
    identity data gas = .error e ↔ gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas := by
  unfold identity
  by_cases short : gas < gasCost data.size
  · simp only [short, ↓reduceIte, Except.error.injEq, true_and]
    exact eq_comm
  · simp [short]

end EthLib.Execution.Evm.Precompiles.Identity
