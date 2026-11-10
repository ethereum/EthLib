module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtSlots
public import EthLib.Consensus.Proofs.Transition.PaymentRelease

/-!
# Proofs: the slots that pay the bid of a block

From Gloas the builder of a block pays its proposer through a pending payment.

The step lemmas of the payments give the shape of each step that may pay a bid.

Here the steps of a slot are put together.

A slot inside an epoch pays no bid.

The last slot of an epoch runs the epoch step of the payments, between steps that keep them.

So it pays each payment of the previous epoch that reaches the quorum of that step.

Each payment it pays is closed after the slot.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- With a positive quorum, one slot queues the withdrawals of open payments, each closed after it.

The positive quorum is an assumption on the preset, which both presets meet.

A slot inside an epoch releases no payment.

At the last slot of an epoch, the epoch transition runs, and its step of the payments reads a state.

That state is the one the epoch transition reaches before that step, after the slot is cached.

The slot then pays each payment of the previous epoch whose weight is at least the quorum there.

The hypothesis on the parent payment is part of the builder debt invariant.

The hypotheses on the weights and the genesis epoch are assumptions, which no lemma proves yet.
-/
theorem advanceSlot_release (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} (fresh : ParentPaymentFresh state gloas)
    (paid : WeightedPaymentsFunded state gloas) (genesis : GenesisFirstHalfEmpty state gloas)
    (computed : advanceSlot config checks state = .ok after) :
    ∃ released : List Slot, PaymentRelease state after gloas released ∧
      (∀ slot ∈ released, ¬ PaymentOpen after gloas slot) ∧
      (after.slot % preset.SLOTS_PER_EPOCH ≠ 0 → released = []) ∧
      (after.slot % preset.SLOTS_PER_EPOCH = 0 → ∃ cached pending quorum,
        processSlot state = .ok cached ∧ epochBeforePayments config checks cached = .ok pending ∧
        getBuilderPaymentQuorumThreshold pending = .ok quorum ∧
        ∀ slot position, slotPaymentPosition state slot = some position →
          position.toNat < preset.SLOTS_PER_EPOCH.toNat →
          quorum ≤ (paymentAt state gloas position.toNat).weight → slot ∈ released) := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := builderFrame_processSlot cachedOk
  have forward : state.slot ≤ next := UInt64.le_iff_toNat_le.mpr (by omega)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨pending, settled, pendingOk, before, settledOk, tail⟩ :=
      processEpoch_builderSplit (gloas := gloas) epochedOk
    have pendingFrame := cachedFrame.trans before
    obtain ⟨quorum, released, quorumOk, release, closes, reaches⟩ :=
      processBuilderPendingPayments_release positive (fresh.of_frame pendingFrame)
        (paid.of_frame pendingFrame) (genesis.of_frame pendingFrame)
        settledOk (by rw [pendingFrame.slot]; exact sum) boundary
    have frame := tail.withSlot next
    refine ⟨released, release.of_frames pendingFrame frame, ?_,
      fun outside => absurd boundary outside,
      fun _ => ⟨cached, pending, quorum, cachedOk, pendingOk, quorumOk, ?_⟩⟩
    · intro slot member opened
      exact closes slot member ((paymentOpen_congr (slotPaymentPosition_congr frame.slot)
        frame.headerSlot (congrFun frame.bid gloas)
        (fun position => congrArg _ (frame.paymentAt gloas position)) slot).mp opened)
    · intro slot position located below reached
      rw [← slotPaymentPosition_congr pendingFrame.slot] at located
      rw [← pendingFrame.paymentAt gloas] at reached
      exact reaches slot position located below reached
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have sameEpoch : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat :=
      nextSlot_epoch_of_inside sum inside
    refine ⟨[], PaymentRelease.of_fields forward (slotPaymentPosition_congr_epoch sameEpoch)
      cachedFrame.headerSlot (congrFun cachedFrame.bid gloas)
      (fun position => congrArg _ (cachedFrame.paymentAt gloas position))
      (congrFun cachedFrame.withdrawals gloas), nofun, fun _ => rfl,
      fun boundary => absurd boundary inside⟩

end EthLib.Consensus
