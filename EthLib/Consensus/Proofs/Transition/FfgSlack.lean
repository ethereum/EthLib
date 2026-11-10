module

public import EthLib.Consensus.Proofs.Transition.FfgJustification

/-!
# Proofs: justification keeps the justified checkpoints slack-justified in Casper FFG

The bound that the epoch step gives for a link, up to churn, is a slack link of the model.

So the step keeps the two justified checkpoints of a state slack-justified in the model.

This is the step of an induction over the epochs of a chain, from the genesis checkpoint.

Each checkpoint of the model has its own set of weights.

Here they hold the effective balances of each state whose step justifies it.

A target is read at the step of its epoch and again at the next step, with new balances between.

So the sets and weights of a checkpoint need to match only the step that first justifies it.

Along one chain that step is unique.

Two branches can justify one checkpoint from two different states.

The set of weights of that checkpoint then holds the balances of both states.

Its validator set must still be one set in both states, which no theorem shows yet.

Justification runs in the epoch step, at the state after the caching of the last slot of an epoch.

The caching writes the root of that slot only.

So the roots of the recent epochs stay when the buffer of roots covers two epochs.

So one slot keeps the two checkpoints slack-justified, under hypotheses on the state before it.

The link of the previous epoch needs its source below its target.

So the previous justified epoch must be below the previous epoch once justification runs.

One slot keeps that, given the two invariants on the justified checkpoints.

The blocks and the upgrades keep it too.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The slack is the stake of the set `E(V t, U t)` of Gasper §8.6, Definition 8.1.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {β : Type*} [Preorder β]
  {attested : Set (ValidatorIndex × AttestationData)}
  {V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex}
  {W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)} {genesis : β}
  {votes : Set (Vote ValidatorIndex β)}

/-- The two justified checkpoints of the state are slack-justified in the model.

Each root maps to a block of the model. -/
def SlackJustifiedCheckpoints (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)) (genesis : β)
    (votes : Set (Vote ValidatorIndex β)) (block : Root → β)
    (state : BeaconState preset fork) : Prop :=
  SlackJustified V U W genesis votes (state.previousJustifiedCheckpoint.toFfg block) ∧
    SlackJustified V U W genesis votes (state.currentJustifiedCheckpoint.toFfg block)

/-- The sets of the model match the state for the checkpoint of an epoch.

That checkpoint has the block of the root that the state records for the start of the epoch.

Its validator set is the active set of the epoch.

Its set of weights holds the effective balances of the state.

Each of its validators in its second set is active in the current epoch.

For the current epoch that always holds.

As the second set, the active set of the next epoch meets it for both recent epochs. -/
def TargetSetsMatch (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)) (block : Root → β)
    (state : BeaconState preset fork) (epoch : Epoch) : Prop :=
  ∀ root, getBlockRoot state epoch = .ok root →
    V ⟨block root, epoch.toNat⟩ = (getActiveValidatorIndices state epoch).toFinset ∧
      (fun index => balanceAt state index.toNat) ∈ W ⟨block root, epoch.toNat⟩ ∧
      V ⟨block root, epoch.toNat⟩ ∩ U ⟨block root, epoch.toNat⟩ ⊆
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset

/-- The bound of a link up to churn gives a slack link of the model.

The sets of the model must match the state for the checkpoint of the epoch.

The source must come before the target, in epoch and in the chain of the target. -/
theorem LinkWithChurn.slackLink {block : Root → β} {epoch : Epoch} {root : Root}
    {s : Models.Ffg.Checkpoint β}
    (link : LinkWithChurn state votes epoch s ⟨block root, epoch.toNat⟩)
    (sets : TargetSetsMatch V U W block state epoch) (rootOk : getBlockRoot state epoch = .ok root)
    (epochs : s.epoch < epoch.toNat) (chain : s.block ≤ block root) :
    SlackLink V U W votes s ⟨block root, epoch.toNat⟩ := by
  classical
  obtain ⟨set, weights, later⟩ := sets root rootOk
  set t : Models.Ffg.Checkpoint β := ⟨block root, epoch.toNat⟩
  refine ⟨epochs, chain, _, weights, ?_⟩
  -- The validators that left the active set lie outside the second set.
  have exited : V t \ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ⊆
      V t \ U t := by
    intro index member
    simp only [Finset.mem_sdiff] at member ⊢
    exact ⟨member.1, fun inU => member.2 (later (Finset.mem_inter.mpr ⟨member.1, inU⟩))⟩
  have slack := stake_mono (w := fun index => balanceAt state index.toNat) exited
  unfold LinkWithChurn at link
  rw [← set] at link
  convert link.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 slack) _)

/-- Justification keeps the two justified checkpoints slack-justified in the model.

The hypotheses on the votes and the stake are those of the bound of a link up to churn.

The current justified epoch must be at most the previous epoch.

Once justification runs, the previous justified epoch must be below the previous epoch.

The step may make the checkpoint of the previous or the current epoch the current justified one.

If that changes the current justified checkpoint, the sets and weights of the model must match.

They must match the state for the epoch of the new checkpoint.

Otherwise they need not match.

Take each of the two recent epochs and the source of its link.

The block of that source must be in the chain of the block of the epoch.

That block is the block of the root that the state records for the start of the epoch.

For the genesis state, choose the block of the zero root as the genesis block of the model.

The hypothesis on the chain then needs that block below the block of each recent epoch. -/
theorem processJustificationAndFinalization_slackJustifiedCheckpoints
    (flagsVoted : TargetFlagsVoted attested state)
    (pendingVoted : PendingVoted attested state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β)
    (contains : ffgVotes block attested ⊆ votes)
    (settled : JustifiedSettled state)
    (separated : JustifiedSeparated state)
    (sets : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint →
      TargetSetsMatch V U W block state after.currentJustifiedCheckpoint.epoch)
    (chain : ∀ (current : Bool) (root : Root),
      getBlockRoot state (if current then getCurrentEpoch state else getPreviousEpoch state) =
          .ok root →
        block (if current then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint).root ≤ block root)
    (holds : SlackJustifiedCheckpoints V U W genesis votes block state)
    (computed : processJustificationAndFinalization state = .ok after) :
    SlackJustifiedCheckpoints V U W genesis votes block after := by
  by_cases early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1
  · exact processJustificationAndFinalization_early_eq early computed ▸ holds
  have one : (GENESIS_EPOCH + 1 : Epoch).toNat = 1 := by decide
  have late : 1 < (getCurrentEpoch state).toNat := by
    have := mt UInt64.le_iff_toNat_le.mpr early
    omega
  rcases processJustificationAndFinalization_ok computed with same | ⟨_, _, _, weighed⟩
  · exact same ▸ holds
  refine ⟨?_, ?_⟩
  · -- The old current justified checkpoint becomes the previous one.
    rw [(weighJustificationAndFinalization_checkpoints weighed).1]
    exact holds.2
  rcases processJustificationAndFinalization_linkWithChurn flagsVoted pendingVoted large block
    contains computed with same | ⟨current, epoch, rootOk, link⟩
  · rw [same]
    exact holds.2
  by_cases kept : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  · rw [kept]
    exact holds.2
  have targetSets := sets kept
  rw [epoch] at rootOk targetSets
  have before := chain current _ rootOk
  have settled' := UInt64.le_iff_toNat_le.mp settled
  have previous := getPreviousEpoch_toNat state
  -- The new checkpoint is the checkpoint of its epoch, with the root of its first slot.
  have target : after.currentJustifiedCheckpoint.toFfg block =
      ⟨block after.currentJustifiedCheckpoint.root,
        (if current then getCurrentEpoch state else getPreviousEpoch state).toNat⟩ := by
    simp only [Checkpoint.toFfg, epoch]
  rw [target] at link ⊢
  cases current
  · -- The previous epoch: its source is the previous justified checkpoint.
    simp only [Bool.false_eq_true, ↓reduceIte] at link before rootOk targetSets ⊢
    have below := UInt64.lt_iff_toNat_lt.mp
      (separated (UInt64.lt_iff_toNat_lt.mpr (by rw [one]; exact late)))
    exact .link holds.1 (link.slackLink targetSets rootOk below before)
  · -- The current epoch: its source is the current justified checkpoint.
    simp only [↓reduceIte] at link before rootOk targetSets ⊢
    exact .link holds.2 (link.slackLink targetSets rootOk (by simp only [Checkpoint.toFfg]; omega)
      before)

/-- An epoch has at least one slot when the slot after another one starts an epoch. -/
private theorem slotsPerEpoch_pos_of_mod {slot next : Slot} (sum : next.toNat = slot.toNat + 1)
    (boundary : next % preset.SLOTS_PER_EPOCH = 0) : 0 < preset.SLOTS_PER_EPOCH.toNat := by
  apply Nat.pos_of_ne_zero
  intro zero
  have mod := congrArg UInt64.toNat boundary
  rw [UInt64.toNat_mod, zero, Nat.mod_zero] at mod
  simp only [UInt64.toNat_zero] at mod
  omega

/-- One slot that changes the current justified checkpoint makes it that of a recent epoch.

A recent epoch is the previous or the current epoch of the state before.

The root of the new checkpoint is the root that the state before records for the epoch.

The buffer of roots must cover two epochs. -/
theorem advanceSlot_getBlockRoot_currentJustified_of_ne
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (computed : advanceSlot config checks state = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    (after.currentJustifiedCheckpoint.epoch = getPreviousEpoch state ∨
        after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state) ∧
      getBlockRoot state after.currentJustifiedCheckpoint.epoch =
        .ok after.currentJustifiedCheckpoint.root := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  dsimp only at changed ⊢
  clear computed
  have currentEq : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, cachedFrame.slot]
  have previousEq : getPreviousEpoch cached = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    rw [frame.currentJustified] at changed ⊢
    rcases processJustificationAndFinalization_currentJustified justifiedOk with same |
      ⟨recent, rootOk⟩
    · rw [same, cachedFrame.currentJustified] at changed
      exact absurd rfl changed
    rw [currentEq, previousEq] at recent
    -- The caching keeps the root of the recent epoch.
    rw [getBlockRoot_processSlot cachedOk (slot_lt_epoch_add_historical
      (slotsPerEpoch_pos_of_mod sum boundary) window recent.symm)] at rootOk
    exact ⟨recent, rootOk⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact absurd cachedFrame.currentJustified changed

/-- One slot keeps the two justified checkpoints slack-justified in the model.

When the slot ends an epoch, justification runs at the state after the caching of the slot.

That caching keeps the roots of the recent epochs, the flags, the checkpoints and the stakes.

So the hypotheses of justification are asked of the state before the slot.

The bound on the active stake and the chain are asked only when the slot ends an epoch.

The buffer of roots must cover two epochs, as both presets do, so that the caching keeps them.

The previous justified epoch must be below the previous epoch once justification runs.

If the slot changes the current justified checkpoint, the sets and weights of the model must match.

They must match the state before the slot for the epoch of the new checkpoint.

The chain hypothesis also reads the roots of the state before the slot. -/
theorem advanceSlot_slackJustifiedCheckpoints
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (flagsVoted : TargetFlagsVoted attested state)
    (pendingVoted : PendingVoted attested state)
    (large : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt state index.toNat)
          (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β)
    (contains : ffgVotes block attested ⊆ votes)
    (settled : JustifiedSettled state) (separated : JustifiedSeparated state)
    (sets : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint →
      TargetSetsMatch V U W block state after.currentJustifiedCheckpoint.epoch)
    (chain : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 → ∀ (current : Bool) (root : Root),
      getBlockRoot state (if current then getCurrentEpoch state else getPreviousEpoch state) =
          .ok root →
        block (if current then state.currentJustifiedCheckpoint
          else state.previousJustifiedCheckpoint).root ≤ block root)
    (holds : SlackJustifiedCheckpoints V U W genesis votes block state)
    (computed : advanceSlot config checks state = .ok after) :
    SlackJustifiedCheckpoints V U W genesis votes block after := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have validators : cached.validators = state.validators := by rw [cachedEq]
  have currentEq : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, cachedFrame.slot]
  have previousEq : getPreviousEpoch cached = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have positive := slotsPerEpoch_pos_of_mod sum boundary
    -- The caching keeps the roots of both recent epochs.
    have roots : ∀ current : Bool,
        getBlockRoot cached (if current then getCurrentEpoch state else getPreviousEpoch state) =
          getBlockRoot state
            (if current then getCurrentEpoch state else getPreviousEpoch state) := by
      intro current
      refine getBlockRoot_processSlot cachedOk (slot_lt_epoch_add_historical positive window ?_)
      cases current
      · exact .inr rfl
      · exact .inl rfl
    have last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := by
      have nextEq : next = state.slot + 1 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_one, ← sum, Nat.mod_eq_of_lt next.toNat_lt]
      rw [← nextEq]
      exact boundary
    have active : ∀ epoch, getActiveValidatorIndices cached epoch =
        getActiveValidatorIndices state epoch := by
      intro epoch
      unfold getActiveValidatorIndices
      rw [validators]
    have balances : ∀ index, balanceAt cached index = balanceAt state index := by
      intro index
      unfold balanceAt
      rw [validators]
    have flagsCached : TargetFlagsVoted attested cached :=
      flagsVoted.of_processSlot positive window cachedOk
    have pendingCached : PendingVoted attested cached :=
      pendingVoted.of_processSlot cachedOk
    have largeCached : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt cached index.toNat)
          (getActiveValidatorIndices cached (getCurrentEpoch cached)).toFinset := by
      simp only [balances, active, currentEq]
      exact large last
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    suffices key : SlackJustifiedCheckpoints V U W genesis votes block justified by
      unfold SlackJustifiedCheckpoints at key ⊢
      rw [frame.previousJustified, frame.currentJustified]
      exact key
    refine processJustificationAndFinalization_slackJustifiedCheckpoints flagsCached pendingCached
      largeCached block contains ?_ ?_ ?_ ?_ ?_ justifiedOk
    · unfold JustifiedSettled
      rw [cachedFrame.currentJustified, previousEq]
      exact settled
    · exact separated.of_frame cachedFrame
    · intro changed
      dsimp only at sets
      rw [frame.currentJustified] at sets
      rw [cachedFrame.currentJustified] at changed
      rcases processJustificationAndFinalization_currentJustified justifiedOk with same |
        ⟨recent, -⟩
      · exact absurd (same.trans cachedFrame.currentJustified) changed
      rw [currentEq, previousEq] at recent
      have targetSets := sets changed
      intro root rootOk
      rw [getBlockRoot_processSlot cachedOk
        (slot_lt_epoch_add_historical positive window recent.symm)] at rootOk
      simp only [active, balances, currentEq]
      exact targetSets root rootOk
    · intro current root rootOk
      rw [currentEq, previousEq, roots] at rootOk
      rw [cachedFrame.currentJustified, cachedFrame.previousJustified]
      exact chain last current root rootOk
    · unfold SlackJustifiedCheckpoints
      rw [cachedFrame.previousJustified, cachedFrame.currentJustified]
      exact holds
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    unfold SlackJustifiedCheckpoints
    rw [cachedFrame.previousJustified, cachedFrame.currentJustified]
    exact holds

end EthLib.Consensus
