module

public import EthLib.Base.Except
public import EthLib.Consensus.Transition.BuilderPayments
public import EthLib.Serialization.Proofs.Ssz.Typed.Rooted

/-!
# Proofs: the epoch step of the builder payments

After the step, the first half of the payments is the old second half.

The second half then holds the payment of no bid.

The withdrawals queue gains the withdrawals of the old first half that reach the quorum, in order.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- A position of the first epoch takes the payment one epoch later. -/
theorem getElem_shiftPayments_early (payments : BuilderPendingPayments preset) {position : Nat}
    (early : position < preset.SLOTS_PER_EPOCH.toNat) :
    (shiftPayments payments)[position]'(by omega) =
      payments[position + preset.SLOTS_PER_EPOCH.toNat]'(by omega) := by
  change (shiftPayments payments).elements[position] = _
  simp [shiftPayments, early]

/-- A position of the second epoch holds the payment of no bid. -/
theorem getElem_shiftPayments_late (payments : BuilderPendingPayments preset) {position : Nat}
    (late : preset.SLOTS_PER_EPOCH.toNat ≤ position)
    (inside : position < 2 * preset.SLOTS_PER_EPOCH.toNat) :
    (shiftPayments payments)[position] = BuilderPendingPayment.empty := by
  change (shiftPayments payments).elements[position] = _
  simp [shiftPayments, Nat.not_lt.mpr late]

/-- The step appends the released withdrawals to the queue and moves the payments by one epoch.

The released withdrawals are those of the payments of the first epoch that reach the quorum. -/
theorem processBuilderPendingPayments_spec {state after : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) :
    ∃ quorum, getBuilderPaymentQuorumThreshold state = .ok quorum ∧
      (after.builderPendingWithdrawals gloas).data.toList =
        (state.builderPendingWithdrawals gloas).data.toList ++
          releasedPayments (state.builderPendingPayments gloas).elements.toList
            preset.SLOTS_PER_EPOCH.toNat quorum ∧
      after.builderPendingPayments gloas = shiftPayments (state.builderPendingPayments gloas) := by
  unfold processBuilderPendingPayments at computed
  obtain ⟨quorum, found, rest⟩ := bind_ok_iff.mp computed
  cases rest
  exact ⟨quorum, found, by simp, rfl⟩

end EthLib.Consensus
