module

public import EthLib.Execution.Transactions.Types
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the codes of the transaction errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

/-- Two errors with one code come from one constructor. -/
theorem TransactionError.code_injective (e₁ e₂ : TransactionError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective TransactionError.code

end EthLib.Execution.Transactions
