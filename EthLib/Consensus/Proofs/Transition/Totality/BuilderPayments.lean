module

public import EthLib.Consensus.Proofs.Transition.Totality.Bound
public import EthLib.Consensus.Transition.BuilderPayments

import EthLib.Consensus.Proofs.Builders
import EthLib.Consensus.Proofs.Transition.BuilderPayments

/-!
# Proofs: the epoch step of builder payments succeeds

The settlement of [EIP-7732] can fail when it computes the payment quorum.

The quorum reads the total active balance, which needs the registry within its limit.

The sum of effective balances must also be below `2^64`.

At least six slots per epoch then make the quorum multiplication fit in 64 bits.

The step changes only the pending builder payments and withdrawals.

The bounds on the amounts that a run of slots needs read neither field, so the step keeps them.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- From Gloas, the epoch settlement of builder payments succeeds.

The registry must be within its limit, and the sum of effective balances below `2^64`.

An epoch must have at least six slots. -/
theorem processBuilderPendingPayments_total (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (within : state.RegistryWithinLimit)
    (summed : effectiveBalanceSum state < 2 ^ 64) (slots : 6 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    ∃ after, processBuilderPendingPayments state gloas = .ok after := by
  obtain ⟨total, totalOk, -, -⟩ := getTotalActiveBalance_exists_ok within summed
  have quorum := getBuilderPaymentQuorumThreshold_of_total totalOk slots
  simp only [processBuilderPendingPayments, quorum, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

/-- The epoch settlement of builder payments keeps the bounds on the amounts of a run of slots. -/
theorem WithinBudget.processBuilderPendingPayments {budget scoreBound : Nat}
    {state after : BeaconState preset fork} (holds : WithinBudget budget scoreBound state)
    {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) :
    WithinBudget budget scoreBound after := by
  rw [processBuilderPendingPayments_eq computed]
  exact ⟨holds.within, holds.matched, holds.capped, holds.funded, holds.slashed, holds.scored,
    holds.carried⟩

end EthLib.Consensus
