module

public import EthLib.Consensus.Proofs.Transition.FfgFinality
public import EthLib.Consensus.Proofs.Transition.FfgSlackActive

/-!
# Proofs: along a chain, the finalized checkpoint is slack-finalized in Casper FFG

The genesis checkpoint is finalized in the model, as the genesis state finalizes it.

Each step of a chain keeps the finalized checkpoint slack-finalized, with two facts of the bits.

A set bit 0 gives a slack link from the previous to the current justified checkpoint.

A set bit 1 makes the checkpoint two epochs back slack-justified.

So along a chain from the genesis state built from deposits, it is slack-finalized in the model.

The sets, weights and votes are those of the theorem on justified checkpoints.

The step asks the sets and weights to match for both recent epochs at each end of an epoch.

The rules of finalization read epochs as justified that no field of the state holds.

The buffer of roots must cover three epochs, as both presets do.

Gasper Definition 4.9 defines `k`-finalization.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {β : Type*} [Preorder β]
  {V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex}
  {W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)} {genesis : β}
  {attested : Set (ValidatorIndex × AttestationData)} {block : Root → β}

/-- The properties of a state that the steps of a chain keep, with finality.

They are those for the justified checkpoints, and three more.

The map from roots to blocks keeps in order the roots the state records at consecutive slots.

The two newest bits carry their facts for the current epoch.

The finalized checkpoint is slack-finalized in the model. -/
structure SlackFinalityInvariant (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)) (genesis : β)
    (attested : Set (ValidatorIndex × AttestationData)) (block : Root → β)
    (forked : ForkedBeaconState preset) : Prop
    extends SlackChainInvariant V U W genesis attested block forked where
  /-- The map from roots to blocks keeps the roots of consecutive slots in order. -/
  links : ∀ link ∈ rootLinks forked.state, block link.1 ≤ block link.2
  /-- The two newest bits carry their facts for the current epoch. -/
  bits : SlackBits V U W genesis (ffgVotes block attested) block
    (getCurrentEpoch forked.state).toNat forked.state
  /-- The finalized checkpoint is slack-finalized. -/
  finalized : SlackFinalized V U W genesis (ffgVotes block attested)
    (forked.state.finalizedCheckpoint.toFfg block)

/-- One step of a chain keeps the properties of its states, with finality.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes. -/
theorem SlackFinalityInvariant.of_chainStep (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {forked after : ForkedBeaconState preset}
    (holds : SlackFinalityInvariant V U W genesis attested block forked)
    (hypotheses : SlackStepHypotheses config checks V U W attested block forked after)
    (step : ChainStep config checks forked after) :
    SlackFinalityInvariant V U W genesis attested block after := by
  have base := holds.toSlackChainInvariant.of_chainStep positive (by omega) apart hypotheses step
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    -- The upgrades keep the slot, the roots, the bits and the three checkpoints.
    have slot := processUpgrades_slot upgraded
    have roots := processUpgrades_blockRoots upgraded
    have bitsEq := processUpgrades_justificationBits upgraded
    obtain ⟨previous, current⟩ := processUpgrades_justified upgraded
    have finalizedEq := (processUpgrades_invariant
      (advanceSlot_invariant holds.invariant advancedOk).1 upgraded).2
    have moved := advanceSlotAcross_slot_ne computed
    obtain ⟨bits, finalized⟩ := advanceSlot_slackBits window holds.flagsVoted
      holds.pendingVoted (hypotheses.large moved) block subset_rfl holds.invariant.settled
      holds.separated (hypotheses.sets moved) holds.roots holds.links holds.slack holds.bits
      holds.finalized advancedOk
    have currentEq : getCurrentEpoch after.state = getCurrentEpoch advanced := by
      simp only [getCurrentEpoch, slot]
    refine ⟨base, hypotheses.links, ?_, ?_⟩
    · rw [currentEq]
      exact bits.congr slot roots bitsEq previous current
    · rw [finalizedEq]
      exact finalized
  | @block _ pre post engine signed validateResult applied =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
    have frame := frame_processBlock blockOk
    have currentEq : getCurrentEpoch post = getCurrentEpoch pre := by
      simp only [getCurrentEpoch, frame.slot]
    refine ⟨base, hypotheses.links, ?_, ?_⟩
    · rw [currentEq]
      exact holds.bits.congr frame.slot (processBlock_blockRoots blockOk) frame.justificationBits
        frame.previousJustified frame.currentJustified
    · rw [frame.finalized]
      exact holds.finalized

/-- The genesis state has the properties of the states of a chain, with finality.

The genesis block of the model is the block of the zero root, the root of its checkpoints. -/
theorem initializeBeaconStateFromEth1_slackFinalityInvariant {fork : Fork}
    {state : BeaconState preset fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    SlackFinalityInvariant V U W (block (Vector.replicate 32 0)) attested block
      ⟨fork, state⟩ := by
  obtain ⟨bitsEq, finalizedEq⟩ := initializeBeaconStateFromEth1_finality computed
  refine ⟨initializeBeaconStateFromEth1_slackChainInvariant computed, fun link member => ?_,
    ⟨fun _ => ?_, fun set => ?_, fun set => ?_⟩, ?_⟩
  · rcases member with ⟨_, read, -⟩ | ⟨-, read⟩ <;>
      exact absurd read (getBlockRootAtSlot_initializeBeaconStateFromEth1 computed _ _)
  · simp [bitsEq]
  · simp [bitsEq] at set
  · simp [bitsEq] at set
  · rw [finalizedEq]
    exact .inl rfl

/-- Along a run of steps of a chain from genesis, the finalized checkpoint is slack-finalized.

Each step must meet its hypotheses when a run from genesis reaches it and it reaches the last state.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis block of the model is the block of the zero root.

The genesis state built from deposits exists only before Altair. -/
theorem slackFinalized_of_chainSteps (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last)
    (meets : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last →
      SlackStepHypotheses config checks V U W attested block forked after) :
    SlackFinalized V U W (block (Vector.replicate 32 0)) (ffgVotes block attested)
      (last.state.finalizedCheckpoint.toFfg block) := by
  have chain := chainSteps_and steps meets
  clear steps meets
  suffices holds : SlackFinalityInvariant V U W (block (Vector.replicate 32 0)) attested block
      last from holds.finalized
  induction chain with
  | refl => exact initializeBeaconStateFromEth1_slackFinalityInvariant computed
  | tail _ step ih => exact ih.of_chainStep positive window apart step.2 step.1

/-- Along a run of steps of a chain from genesis, the finalized checkpoint is slack-finalized.

The validator set of a checkpoint is the active set of its epoch in the last state.

Its second set is the active set of the next epoch in the last state.

Its weights are the effective balances of each state at the end of its epoch or the next one.

That state must record its root for its epoch.

The votes are those that the block steps between genesis and the last state cast.

Each step on any run between them must meet the bounds on the stake, the blocks and the registry.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis block of the model is the block of the zero root.

The genesis state built from deposits exists only before Altair. -/
theorem slackFinalized_activeSetAt_of_chainSteps
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last)
    (meets : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last →
      SlackStepBounds block forked after) :
    SlackFinalized (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1))
      (justifyingBalances config checks block ⟨fork, state⟩ last) (block (Vector.replicate 32 0))
      (ffgVotes block (runVotes config checks ⟨fork, state⟩ last))
      (last.state.finalizedCheckpoint.toFfg block) :=
  slackFinalized_of_chainSteps positive window apart computed steps
    (SlackStepHypotheses.of_activeSetAt_of_chainSteps meets)

/-- Along a run of steps of a chain from genesis, the finalized checkpoint is slack-finalized.

The blocks of the model are the roots, ordered by the links of the states that genesis reaches.

The sets are the active sets, the weights the effective balances, and the votes those of the run.

Each step on any run between them must meet the bound on the stake and on the registry.

An epoch must have at least one slot, and the buffer of roots must cover three epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis block of the model is the zero root.

The genesis state built from deposits exists only before Altair. -/
theorem slackFinalized_chainRoot_of_chainSteps
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ last)
    (large : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last →
      after.state.slot ≠ forked.state.slot →
      (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt forked.state index.toNat)
          (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset)
    (small : ∀ forked after,
      Relation.ReflTransGen (ChainStep config checks) ⟨fork, state⟩ forked →
      ChainStep config checks forked after →
      Relation.ReflTransGen (ChainStep config checks) after last →
      after.state.validators.data.size < 2 ^ 64) :
    SlackFinalized (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1))
      (justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
        ⟨fork, state⟩ last)
      (toChainRoot config checks ⟨fork, state⟩ (Vector.replicate 32 0))
      (ffgVotes (toChainRoot config checks ⟨fork, state⟩)
        (runVotes config checks ⟨fork, state⟩ last))
      (last.state.finalizedCheckpoint.toFfg (toChainRoot config checks ⟨fork, state⟩)) :=
  slackFinalized_activeSetAt_of_chainSteps positive window apart computed steps
    (SlackStepBounds.of_toChainRoot large small)

end EthLib.Consensus
