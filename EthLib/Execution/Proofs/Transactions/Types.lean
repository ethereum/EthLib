module

public import EthLib.Execution.Transactions.Types

/-!
# Proofs: the codes of the transaction errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

/-- Two errors with one code come from one constructor. -/
theorem TransactionError.code_injective (e₁ e₂ : TransactionError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [TransactionError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Transactions
