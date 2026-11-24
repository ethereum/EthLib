module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtSlots
public import EthLib.Consensus.Proofs.Transition.PaymentRelease

/-!
# Proofs: the slots that pay the bid of a block

From Gloas the builder of a block pays its proposer through a pending payment.

The step lemmas of the payments give the shape of each step that may pay a bid.

Here the steps of a slot are put together.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The payment of the bid at a slot reaches the quorum that the epoch transition computes.

That transition runs after one slot, and only a slot that ends an epoch runs it.

The quorum is read on the state that the epoch transition reaches before its payments step.

The payment must be one of the previous epoch, in the first half of the window. -/
def ReachesQuorum (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (slot : Slot) : Prop :=
  ∃ cached pending quorum position, processSlot state = .ok cached ∧
    epochBeforePayments config checks cached = .ok pending ∧
    getBuilderPaymentQuorumThreshold pending = .ok quorum ∧
    slotPaymentPosition state slot = some position ∧
    position.toNat < preset.SLOTS_PER_EPOCH.toNat ∧
    quorum ≤ (paymentAt state gloas position.toNat).weight

/-- With a positive quorum, one slot queues the withdrawals of open payments, each closed after it.

The positive quorum is an assumption on the preset, which both presets meet. -/
theorem advanceSlot_release (positive : preset.PaymentQuorumPositive)
    -- The hypothesis on the parent payment is part of the builder debt invariant.
    {gloas : .glamsterdam ≤ fork} (fresh : ParentPaymentFresh state gloas)
    -- The weight and genesis epoch hypotheses hold along a chain from the upgrade to Gloas.
    (paid : WeightedPaymentsFunded state gloas) (genesis : GenesisFirstHalfEmpty state gloas)
    (computed : advanceSlot config checks state = .ok after) :
    ∃ released : List Slot, PaymentRelease state after gloas released ∧
      -- Each payment it pays is closed after the slot.
      (∀ slot ∈ released, ¬ PaymentOpen after gloas slot) ∧
      -- A slot inside an epoch releases no payment.
      (after.slot % preset.SLOTS_PER_EPOCH ≠ 0 → released = []) ∧
      -- At the last slot of an epoch, the epoch transition runs.
      --
      -- Its step of the payments reads the state that it reaches before that step.
      --
      -- That state comes after the slot is cached.
      --
      -- The slot pays each payment of the previous epoch whose weight is at least the quorum there.
      --
      -- It pays no other payment.
      (after.slot % preset.SLOTS_PER_EPOCH = 0 →
        ∀ slot, slot ∈ released ↔ ReachesQuorum config checks state gloas slot) := by
  obtain ⟨next, cached, sum, cachedOk, cachedFrame, ⟨inside, rfl⟩ |
    ⟨boundary, pending, settled, pendingOk, before, settledOk, frame⟩⟩ :=
    advanceSlot_builderSplit (gloas := gloas) computed
  · have sameEpoch : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat :=
      nextSlot_epoch_of_inside sum inside
    have forward : state.slot ≤ next := UInt64.le_iff_toNat_le.mpr (by omega)
    refine ⟨[], PaymentRelease.of_fields forward (slotPaymentPosition_congr_epoch sameEpoch)
      cachedFrame.headerSlot (congrFun cachedFrame.bid gloas)
      (fun position => congrArg _ (cachedFrame.paymentAt gloas position))
      (congrFun cachedFrame.withdrawals gloas), nofun, fun _ => rfl,
      fun boundary => absurd boundary inside⟩
  -- The last slot of an epoch runs the epoch step of the payments, between steps that keep them.
  · have pendingFrame := cachedFrame.trans before
    obtain ⟨quorum, released, quorumOk, release, closes, reaches, reached⟩ :=
      processBuilderPendingPayments_release positive (fresh.of_frame pendingFrame)
        (paid.of_frame pendingFrame) (genesis.of_frame pendingFrame)
        settledOk (by rw [pendingFrame.slot]; exact sum) boundary
    refine ⟨released, release.of_frames pendingFrame frame, ?_,
      fun outside => absurd (frame.slot ▸ boundary) outside, fun _ slot => ⟨?_, ?_⟩⟩
    · intro slot member opened
      exact closes slot member ((paymentOpen_congr (slotPaymentPosition_congr frame.slot)
        frame.headerSlot (congrFun frame.bid gloas)
        (fun position => congrArg _ (frame.paymentAt gloas position)) slot).mp opened)
    · intro member
      obtain ⟨position, located, below, enough⟩ := reached slot member
      rw [slotPaymentPosition_congr pendingFrame.slot] at located
      rw [pendingFrame.paymentAt gloas] at enough
      exact ⟨cached, pending, quorum, position, cachedOk, pendingOk, quorumOk, located, below,
        enough⟩
    · rintro ⟨cached', pending', quorum', position, cachedOk', pendingOk', quorumOk', located,
        below, enough⟩
      cases cachedOk'.symm.trans cachedOk
      cases pendingOk'.symm.trans pendingOk
      cases quorumOk'.symm.trans quorumOk
      rw [← slotPaymentPosition_congr pendingFrame.slot] at located
      rw [← pendingFrame.paymentAt gloas] at enough
      exact reaches slot position located below enough

end EthLib.Consensus
