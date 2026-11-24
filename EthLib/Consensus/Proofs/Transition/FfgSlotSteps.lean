module

public import EthLib.Consensus.Proofs.Transition.FfgTwoEpochs
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Invariants
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Proofs: the slot steps of a run that end two epochs of honest target votes finalize the first

Two slot steps that each end an epoch finalize.

In each of those epochs, honest validators hold two thirds of the stake.

They finalize the checkpoint of the first epoch, as two epoch steps do.

This holds from Altair, where the target votes are flags, also when a fork starts in between.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- From Altair, the slot step of the last slot of an epoch runs justification inside it.

Justification runs on the state with the roots of the slot cached.

That state has the epoch, the stake and the target votes of the state before the step.

It also has its current justified checkpoint and its bits of justification.

The state after the step keeps the checkpoints and the bits that justification left. -/
private theorem advanceSlotAcross_justification {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (advanced : advanceSlotAcross config checks forked = .ok after)
    -- A run of the chain ends an epoch with the slot step of its last slot.
    (lastSlot : (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0) :
    ∃ cached justified : BeaconState preset forked.fork,
      processJustificationAndFinalization cached = .ok justified ∧
      getCurrentEpoch cached = getCurrentEpoch forked.state ∧
      getActiveValidatorIndices cached = getActiveValidatorIndices forked.state ∧
      balanceAt cached = balanceAt forked.state ∧
      targetIndices cached = targetIndices forked.state ∧
      -- It also has its current justified checkpoint and its bits of justification.
      cached.currentJustifiedCheckpoint = forked.state.currentJustifiedCheckpoint ∧
      cached.justificationBits = forked.state.justificationBits ∧
      -- The state after the step keeps the checkpoints and the bits that justification left.
      after.state.currentJustifiedCheckpoint = justified.currentJustifiedCheckpoint ∧
      after.state.justificationBits = justified.justificationBits ∧
      after.state.finalizedCheckpoint = justified.finalizedCheckpoint := by
  obtain ⟨fork, state⟩ := forked
  -- That step caches the roots of the slot, runs the epoch transition, then the upgrades now due.
  obtain ⟨advancedState, advancedOk, upgraded⟩ := bind_ok_iff.mp advanced
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advancedOk
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
  -- The rest of the epoch transition and the upgrades keep the checkpoints and the bits.
  have current := (processUpgrades_justified upgraded).2
  have bits := processUpgrades_justificationBits upgraded
  have finalized := processUpgrades_finalized upgraded
  -- From Altair the target votes are flags, which caching the roots keeps.
  have targets : targetIndices cached = targetIndices state := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    funext epoch
    unfold targetIndices
    simp only [altair, ↓reduceDIte]
    rfl
  -- Caching the roots changes neither the registry, nor the flags, nor the slot.
  --
  -- So the stake and the target votes that justification reads are those of the state of the run.
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  exact ⟨_, justified, justifiedOk, rfl, rfl, rfl, targets, rfl, rfl,
    current.trans frame.currentJustified, bits.trans frame.justificationBits,
    finalized.trans frame.finalized⟩

/-- From Altair, the slot step of a run at the last slot of an epoch justifies it, by honest votes.

Honest validators with two thirds of the active stake must count for the target.

The newest bit of justification is then set, after the upgrades now due.

The active stake is that of the current epoch, with effective balances, before the step.

The epoch must be past the first two, so that justification runs. -/
theorem advanceSlotAcross_justifiesCurrent {forked after : ForkedBeaconState preset}
    (altair : .altair ≤ forked.fork) (advanced : advanceSlotAcross config checks forked = .ok after)
    (lastSlot : (forked.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (late : GENESIS_EPOCH + 1 < getCurrentEpoch forked.state)
    {honest : Finset ValidatorIndex}
    -- Every target index that justification counts for the epoch must include the honest set.
    (counted : ∀ indices,
      targetIndices forked.state (getCurrentEpoch forked.state) = .ok indices →
        honest ⊆ indices.toFinset)
    -- The active stake is that of the current epoch, with effective balances, before the step.
    (quorum : 2 * stake (fun index => balanceAt forked.state index.toNat)
        (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset ≤
      3 * stake (fun index => balanceAt forked.state index.toNat) honest) :
    after.state.justificationBits.bits[0] = true ∧
      after.state.currentJustifiedCheckpoint.epoch = getCurrentEpoch forked.state := by
  obtain ⟨cached, justified, justifiedOk, epoch, active, balances, targets, -, -, current, bits,
    -⟩ := advanceSlotAcross_justification altair advanced lastSlot
  -- Justification reads the epoch, the stake and the votes of the state before the step.
  have passed := processJustificationAndFinalization_justifiesCurrent justifiedOk
    (by rw [epoch]; exact late) (by rw [epoch, targets]; exact counted)
    (by rw [epoch, active, balances]; exact quorum)
  rw [current, bits, ← epoch]
  exact passed

/-- From Altair, the slot steps of a run that end two epochs of honest votes finalize the first.

The first step is at the last slot of an epoch, and the second at the last slot of the next one.

A fork may start between them, so the two states before the steps may be at different forks.

Between the two steps the current justified checkpoint and the bits of justification stay.

At each step, honest validators with two thirds of the active stake count for the target.

The first epoch must be past the first two, so that justification runs.

The finalized checkpoint after the second step is the justified checkpoint of the first epoch.

The current justified checkpoint after the second step is that of the second epoch. -/
theorem advanceSlotAcross_finalizesTwoEpochs
    {first firstAfter second secondAfter : ForkedBeaconState preset}
    {firstHonest secondHonest : Finset ValidatorIndex}
    -- A fork may start between them, so the two states before the steps may be at different forks.
    (firstAltair : .altair ≤ first.fork) (secondAltair : .altair ≤ second.fork)
    (firstAdvanced : advanceSlotAcross config checks first = .ok firstAfter)
    (firstLast : (first.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    -- The first epoch must be past the first two, so that justification runs.
    (late : GENESIS_EPOCH + 1 < getCurrentEpoch first.state)
    (firstCounted : ∀ indices,
      targetIndices first.state (getCurrentEpoch first.state) = .ok indices →
        firstHonest ⊆ indices.toFinset)
    (firstQuorum : 2 * stake (fun index => balanceAt first.state index.toNat)
        (getActiveValidatorIndices first.state (getCurrentEpoch first.state)).toFinset ≤
      3 * stake (fun index => balanceAt first.state index.toNat) firstHonest)
    -- Between the two steps the current justified checkpoint and the bits of justification stay.
    (justifiedKept :
      second.state.currentJustifiedCheckpoint = firstAfter.state.currentJustifiedCheckpoint)
    (bitsKept : second.state.justificationBits = firstAfter.state.justificationBits)
    (next : (getCurrentEpoch second.state).toNat = (getCurrentEpoch first.state).toNat + 1)
    (secondAdvanced : advanceSlotAcross config checks second = .ok secondAfter)
    (secondLast : (second.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (secondCounted : ∀ indices,
      targetIndices second.state (getCurrentEpoch second.state) = .ok indices →
        secondHonest ⊆ indices.toFinset)
    (secondQuorum : 2 * stake (fun index => balanceAt second.state index.toNat)
        (getActiveValidatorIndices second.state (getCurrentEpoch second.state)).toFinset ≤
      3 * stake (fun index => balanceAt second.state index.toNat) secondHonest) :
    secondAfter.state.finalizedCheckpoint = firstAfter.state.currentJustifiedCheckpoint ∧
      secondAfter.state.finalizedCheckpoint.epoch = getCurrentEpoch first.state ∧
      -- The current justified checkpoint after the second step is that of the second epoch.
      secondAfter.state.currentJustifiedCheckpoint.epoch = getCurrentEpoch second.state := by
  obtain ⟨firstCached, firstJustified, firstOk, firstEpoch, firstActive, firstBalances,
    firstTargets, -, -, firstCurrent, firstBits, -⟩ :=
    advanceSlotAcross_justification firstAltair firstAdvanced firstLast
  obtain ⟨secondCached, secondJustified, secondOk, secondEpoch, secondActive, secondBalances,
    secondTargets, secondKeptCurrent, secondKeptBits, secondCurrent, -, secondFinalized⟩ :=
    advanceSlotAcross_justification secondAltair secondAdvanced secondLast
  -- The state inside the second step keeps the checkpoint and the bits that the first step left.
  have finalized := processJustificationAndFinalization_finalizesTwoEpochs firstOk
    (by rw [firstEpoch]; exact late) (by rw [firstEpoch, firstTargets]; exact firstCounted)
    (by rw [firstEpoch, firstActive, firstBalances]; exact firstQuorum)
    (by rw [secondKeptCurrent, justifiedKept, firstCurrent])
    (by rw [secondKeptBits, bitsKept, firstBits]) (by rw [firstEpoch, secondEpoch]; exact next)
    secondOk (by rw [secondEpoch, secondTargets]; exact secondCounted)
    (by rw [secondEpoch, secondActive, secondBalances]; exact secondQuorum)
  rw [secondFinalized, secondCurrent, firstCurrent, ← firstEpoch, ← secondEpoch]
  exact finalized

end EthLib.Consensus
