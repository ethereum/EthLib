module

public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.MixesKept
public import EthLib.Consensus.Proofs.Transition.Totality.Justification
public import EthLib.Consensus.Proofs.Transition.Totality.RewardsBeforeAltair
public import EthLib.Consensus.Proofs.Transition.Totality.UpgradeNext

/-!
# Proofs: slots keep the pending attestations resolved and well formed

Before Altair, the totality of the epoch transition assumes two facts on the pending attestations.

The committee and the signers of each one succeed.

Each one is as inclusion in a block stored it, in the epoch of its list.

One slot keeps both facts, and so does a run of slots.

At the end of an epoch the current list becomes the previous one, and its committees stay.

They stay since the epoch step keeps the active validators and the mix that the seed reads.

From Altair both facts hold, since there are no pending attestations.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- One slot keeps each recent pending attestation as inclusion in a block stored it. -/
theorem PendingWellFormed.of_advanceSlot (wellFormed : PendingWellFormed state)
    (computed : advanceSlot config checks state = .ok after) : PendingWellFormed after := by
  intro before
  obtain ⟨previous, current⟩ := wellFormed before
  have grows := advanceSlot_registryGrows computed
  have afterPrevious := getPreviousEpoch_toNat after
  have statePrevious := getPreviousEpoch_toNat state
  rcases advanceSlot_pending before computed with ⟨same, keptPrevious, keptCurrent⟩ |
    ⟨step, moved, emptied⟩
  · have currentEq : getCurrentEpoch after = getCurrentEpoch state := UInt64.toNat_inj.mp same
    have previousEq : getPreviousEpoch after = getPreviousEpoch state :=
      UInt64.toNat_inj.mp (by omega)
    refine ⟨fun attestation member => ?_, fun attestation member => ?_⟩
    · rw [keptPrevious] at member
      obtain ⟨epoch, delay, proposer⟩ := previous attestation member
      exact ⟨previousEq ▸ epoch, delay, by omega⟩
    · rw [keptCurrent] at member
      obtain ⟨epoch, delay, proposer⟩ := current attestation member
      exact ⟨currentEq ▸ epoch, delay, by omega⟩
  · have previousEq : getPreviousEpoch after = getCurrentEpoch state :=
      UInt64.toNat_inj.mp (by omega)
    refine ⟨fun attestation member => ?_, fun attestation member => ?_⟩
    · rw [moved] at member
      obtain ⟨epoch, delay, proposer⟩ := current attestation member
      exact ⟨previousEq ▸ epoch, delay, by omega⟩
    · rw [emptied] at member
      simp at member

/-- One slot keeps the committee and the signers of each recent pending attestation succeeding.

Each recent pending attestation must be as inclusion in a block stored it.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem PendingResolved.of_advanceSlot
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (wellFormed : PendingWellFormed state) (resolved : PendingResolved state)
    (computed : advanceSlot config checks state = .ok after) : PendingResolved after := by
  intro before attestation member
  obtain ⟨previous, current⟩ := wellFormed before
  have afterPrevious := getPreviousEpoch_toNat after
  have statePrevious := getPreviousEpoch_toNat state
  -- The signers read only the committee, which the slot keeps for a recent epoch of both states.
  have signers : ∀ epoch, computeEpochAtSlot preset attestation.data.slot = epoch →
      getPreviousEpoch after ≤ epoch → epoch ≤ getCurrentEpoch state →
      getPendingAttestingIndices after attestation =
        getPendingAttestingIndices state attestation := by
    intro epoch atSlot low high
    unfold getPendingAttestingIndices
    rw [committeesKept_advanceSlot apart computed low high _ _ atSlot]
  rcases advanceSlot_pending before computed with ⟨same, keptPrevious, keptCurrent⟩ |
    ⟨step, moved, emptied⟩
  · rw [keptPrevious, keptCurrent] at member
    have previousEq : getPreviousEpoch after = getPreviousEpoch state :=
      UInt64.toNat_inj.mp (by omega)
    rcases member with inPrevious | inCurrent
    · rw [signers _ (previous attestation inPrevious).1 (by rw [previousEq]; exact UInt64.le_refl _)
        (getPreviousEpoch_le state)]
      exact resolved before attestation (.inl inPrevious)
    · rw [signers _ (current attestation inCurrent).1
        (by rw [previousEq]; exact getPreviousEpoch_le state) (UInt64.le_refl _)]
      exact resolved before attestation (.inr inCurrent)
  · rw [moved, emptied] at member
    have previousEq : getPreviousEpoch after = getCurrentEpoch state :=
      UInt64.toNat_inj.mp (by omega)
    rcases member with inMoved | inEmptied
    · rw [signers _ (current attestation inMoved).1 (by rw [previousEq]; exact UInt64.le_refl _)
        (UInt64.le_refl _)]
      exact resolved before attestation (.inr inMoved)
    · simp at inEmptied

/-- A run of slots keeps each recent pending attestation as inclusion in a block stored it. -/
theorem PendingWellFormed.of_advanceSlots :
    ∀ {count : Nat} {state after : BeaconState preset fork}, PendingWellFormed state →
      advanceSlots config checks count state = .ok after → PendingWellFormed after
  | 0, state, after, wellFormed, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ wellFormed
  | count + 1, state, after, wellFormed, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact PendingWellFormed.of_advanceSlots (wellFormed.of_advanceSlot nextOk) rest

/-- A run of slots keeps the signers of each recent pending attestation succeeding.

Each recent pending attestation must be as inclusion in a block stored it.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem PendingResolved.of_advanceSlots
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    ∀ {count : Nat} {state after : BeaconState preset fork},
      PendingWellFormed state → PendingResolved state →
      advanceSlots config checks count state = .ok after → PendingResolved after
  | 0, state, after, _, resolved, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ resolved
  | count + 1, state, after, wellFormed, resolved, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact PendingResolved.of_advanceSlots apart (wellFormed.of_advanceSlot nextOk)
      (resolved.of_advanceSlot apart wellFormed nextOk) rest

/-- From Altair, every state has its recent pending attestations well formed.

No fork from Altair on has pending attestations. -/
theorem PendingWellFormed.of_altair (altair : .altair ≤ fork) (state : BeaconState preset fork) :
    PendingWellFormed state :=
  fun before => absurd before (Nat.not_lt_of_le altair)

/-- From Altair, every state has its recent pending attestations resolved.

No fork from Altair on has pending attestations. -/
theorem PendingResolved.of_altair (altair : .altair ≤ fork) (state : BeaconState preset fork) :
    PendingResolved state :=
  fun before => absurd before (Nat.not_lt_of_le altair)

end EthLib.Consensus
