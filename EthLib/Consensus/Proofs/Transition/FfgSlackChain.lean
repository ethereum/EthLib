module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.FfgSlack
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Proofs: a chain of beacon states keeps its justified checkpoints slack-justified

The genesis checkpoint is slack-justified, and each step of a chain keeps both justified ones so.

So along a chain from the genesis state built from deposits, both are slack-justified in the model.

That genesis state exists only before Altair, so a chain whose genesis is later is out of scope.

Each step needs hypotheses on the states before and after it.

The votes of the model must hold the data that the state before the step signs.

The sets and weights of the model must match the state for each new current justified checkpoint.

The theorem takes the sets and weights as parameters, matched where a step justifies.

One choice of them can serve a whole chain, as each step that justifies does so for a later epoch.

Nothing bounds them from below, so a choice far from the active sets and balances gives little.

Another module instantiates them with the active sets and balances that the chain reads.

An empty second set, or the zero weights, makes every ordered link a slack link.

Each step at the end of an epoch also asks that each justified block is in the chain of its target.

That is a hypothesis on the map from roots to blocks of the model, which no theorem gives yet.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {β : Type*} [Preorder β]
  {V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex}
  {W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)} {genesis : β}
  {votes : Set (Vote ValidatorIndex β)} {block : Root → β}

/-- The properties of a state that the steps of a chain keep.

The state keeps the invariant of valid blocks.

In the first two epochs, its two justified checkpoints are equal.

Once justification runs, its previous justified epoch is below its previous epoch.

Its target flags and pending attestations are signed votes for their links.

Its fork versions are those of forks in the schedule of the configuration.

Its two justified checkpoints are slack-justified in the model. -/
structure SlackChainInvariant (config : Config) (checks : SignatureChecks)
    (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ)) (genesis : β)
    (votes : Set (Vote ValidatorIndex β)) (block : Root → β)
    (forked : ForkedBeaconState preset) : Prop where
  /-- The invariant of valid blocks. -/
  invariant : Invariant forked.state
  /-- In the first two epochs, the two justified checkpoints are equal. -/
  early : JustifiedEarly forked.state
  /-- Once justification runs, the previous justified epoch is below the previous epoch. -/
  separated : JustifiedSeparated forked.state
  /-- From Altair, each target flag comes from a signed vote for its link. -/
  flagsSigned : TargetFlagsSigned config checks forked.state
  /-- Before Altair, each pending attestation is a signed vote for its link. -/
  pendingSigned : PendingSigned config checks forked.state
  /-- The fork versions are those of forks in the schedule of the configuration. -/
  known : ForkVersionsKnown config forked.state
  /-- The two justified checkpoints are slack-justified in the model. -/
  slack : SlackJustifiedCheckpoints V U W genesis votes block forked.state

/-- The bounds that one step of a chain needs, apart from the sets, weights and votes of the model.

Two of them are asked only of a step that moves the slot, when that slot ends an epoch.

Then the active stake of the current epoch must be more than one and a half increments.

The block of each justified checkpoint must be in the chain of the block of its recent epoch.

After the step, the registry must stay below 2^64 validators.

A block keeps the slot and the justified checkpoints, so it is asked only the size of the registry.

The order of the blocks of the model is an assumption on the map from roots to blocks.

The meaningful choice takes roots ordered by ancestry, with the zero root lowest. -/
structure SlackStepBounds (block : Root → β) (forked after : ForkedBeaconState preset) : Prop where
  /-- At the end of an epoch, the active stake is more than one and a half increments.

  It is asked only when the slot moves, as is the next one. -/
  large : after.state.slot ≠ forked.state.slot →
    (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt forked.state index.toNat)
        (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset
  /-- At the end of an epoch, each justified block is below the block of its recent epoch. -/
  chain : after.state.slot ≠ forked.state.slot →
    (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 → ∀ (current : Bool) (root : Root),
    getBlockRoot forked.state
        (if current then getCurrentEpoch forked.state else getPreviousEpoch forked.state) =
      .ok root →
    block (if current then forked.state.currentJustifiedCheckpoint
      else forked.state.previousJustifiedCheckpoint).root ≤ block root
  /-- The registry stays below 2^64 validators. -/
  small : after.state.validators.data.size < 2 ^ 64

/-- The hypotheses that one step of a chain needs, on the states before and after it.

They are the bounds of a step, and two conditions on the sets, weights and votes of the model.

At the end of an epoch, the votes of the model must hold those of the data that the state signs.

If the step changes the current justified checkpoint, the sets and weights must match.

They must match the state before for the epoch of the new checkpoint.

The meaningful sets are the active sets of the epoch and the next one.

The meaningful weights are the effective balances. -/
structure SlackStepHypotheses (config : Config) (checks : SignatureChecks)
    (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ))
    (votes : Set (Vote ValidatorIndex β)) (block : Root → β)
    (forked after : ForkedBeaconState preset) : Prop extends SlackStepBounds block forked after
    where
  /-- At the end of an epoch, the votes of the model hold the data that the state signs. -/
  contains : after.state.slot ≠ forked.state.slot →
    (forked.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
    ffgVotes block {vote | SignedVote config checks forked.state vote} ⊆ votes
  /-- The sets and weights match the state for a new current justified checkpoint. -/
  sets : after.state.currentJustifiedCheckpoint ≠ forked.state.currentJustifiedCheckpoint →
    TargetSetsMatch V U W block forked.state after.state.currentJustifiedCheckpoint.epoch

/-- One step of a chain that meets the hypotheses of a step. -/
def SlackStep (config : Config) (checks : SignatureChecks)
    (V U : Models.Ffg.Checkpoint β → Finset ValidatorIndex)
    (W : Models.Ffg.Checkpoint β → Set (ValidatorIndex → ℕ))
    (votes : Set (Vote ValidatorIndex β)) (block : Root → β)
    (forked after : ForkedBeaconState preset) : Prop :=
  ChainStep config checks forked after ∧
    SlackStepHypotheses config checks V U W votes block forked after

/-- A step that changes the current justified checkpoint makes it that of a recent epoch.

That epoch is the previous or the current epoch of the state before the step.

The root of the new checkpoint is the root that this state records for the epoch.

The buffer of roots must cover two epochs. -/
theorem ChainStep.getBlockRoot_currentJustified_of_ne
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {forked after : ForkedBeaconState preset} (step : ChainStep config checks forked after)
    (changed : after.state.currentJustifiedCheckpoint ≠ forked.state.currentJustifiedCheckpoint) :
    (after.state.currentJustifiedCheckpoint.epoch = getPreviousEpoch forked.state ∨
        after.state.currentJustifiedCheckpoint.epoch = getCurrentEpoch forked.state) ∧
      getBlockRoot forked.state after.state.currentJustifiedCheckpoint.epoch =
        .ok after.state.currentJustifiedCheckpoint.root := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    have currentKept := (processUpgrades_justified upgraded).2
    dsimp only at currentKept
    rw [currentKept] at changed ⊢
    exact advanceSlot_getBlockRoot_currentJustified_of_ne window advancedOk changed
  | block engine signed validateResult applied =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
    exact absurd (frame_processBlock blockOk).currentJustified changed

/-- One step of a chain keeps the properties of its states.

An epoch must have at least one slot, and the buffer of roots must cover two epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes. -/
theorem SlackChainInvariant.of_chainStep (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {forked after : ForkedBeaconState preset}
    (holds : SlackChainInvariant config checks V U W genesis votes block forked)
    (hypotheses : SlackStepHypotheses config checks V U W votes block forked after)
    (step : ChainStep config checks forked after) :
    SlackChainInvariant config checks V U W genesis votes block after := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    have small : advanced.validators.data.size < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (processUpgrades_registryGrows upgraded) hypotheses.small
    have early := holds.early.of_advanceSlot advancedOk
    -- The slot moves on by one, and the upgrades keep it.
    have moved : after.state.slot ≠ forked.state.slot := by
      have kept : after.state.slot = advanced.slot :=
        processUpgrades_induction (property := fun state => state.state.slot = advanced.slot)
          (fun same stepOk => (upgradeFrame_upgradeNext stepOk).slot.trans same) rfl upgraded
      intro same
      have next := advanceSlot_slot advancedOk
      rw [← kept, same] at next
      omega
    obtain ⟨previousKept, currentKept⟩ := processUpgrades_justified upgraded
    have pending : PendingSigned config checks advanced := by
      by_cases before : forked.fork < .altair
      · exact holds.pendingSigned.of_advanceSlot before apart holds.early small advancedOk
      · exact fun before' => absurd before' before
    have known : ForkVersionsKnown config forked.state → ForkVersionsKnown config advanced :=
      fun known => (ForkVersionsKnown.congr (advanceSlot_keys advancedOk).1).mpr known
    have flags := holds.flagsSigned.of_advanceSlot positive window holds.early small advancedOk
    have slack := advanceSlot_slackJustifiedCheckpoints window holds.flagsSigned
      holds.pendingSigned (hypotheses.large moved) block (hypotheses.contains moved)
      holds.invariant.settled
      holds.separated (fun ne => by
        rw [← currentKept] at ne ⊢
        exact hypotheses.sets ne) (hypotheses.chain moved) holds.slack advancedOk
    refine ⟨(advanceSlotAcross_invariant holds.invariant computed).1,
      early.of_processUpgrades upgraded,
      (holds.separated.of_advanceSlot holds.early holds.invariant.settled
        advancedOk).of_processUpgrades upgraded, ?_, pending.of_processUpgrades upgraded,
      ForkVersionsKnown.of_processUpgrades (known holds.known) upgraded, ?_⟩
    · by_cases altair : .altair ≤ forked.fork
      · exact TargetFlagsSigned.of_processUpgrades (forked := ⟨forked.fork, advanced⟩) altair
          hypotheses.small flags upgraded
      · exact TargetFlagsSigned.of_processUpgrades_of_lt_altair (forked := ⟨forked.fork, advanced⟩)
          (Nat.lt_of_not_le altair) hypotheses.small pending upgraded
    · unfold SlackJustifiedCheckpoints
      rw [previousKept, currentKept]
      exact slack
  | block engine signed validateResult applied =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok applied
    have frame := frame_processBlock blockOk
    obtain ⟨_, voteFrame, -⟩ := voteFrame_processBlock blockOk
    have known := ForkVersionsKnown.of_frame frame holds.known
    refine ⟨frame.invariant holds.invariant, holds.early.of_frame frame,
      holds.separated.of_frame frame,
      holds.flagsSigned.of_voteFrame hypotheses.small known voteFrame,
      fun before => PendingSigned.of_processBlock before apart hypotheses.small known
        holds.pendingSigned blockOk before, known, ?_⟩
    unfold SlackJustifiedCheckpoints
    rw [frame.previousJustified, frame.currentJustified]
    exact holds.slack

/-- A chain keeps the properties of its states, from its first state to its last.

Each step must meet its hypotheses. -/
theorem SlackChainInvariant.of_chain (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {first last : ForkedBeaconState preset}
    (holds : SlackChainInvariant config checks V U W genesis votes block first)
    (steps : Relation.ReflTransGen (SlackStep config checks V U W votes block) first last) :
    SlackChainInvariant config checks V U W genesis votes block last := by
  induction steps with
  | refl => exact holds
  | tail _ step ih => exact ih.of_chainStep positive window apart step.2 step.1

/-- The genesis state has the properties of the states of a chain.

The genesis block of the model is the block of the zero root, the root of its checkpoints. -/
theorem initializeBeaconStateFromEth1_slackChainInvariant {fork : Fork}
    {state : BeaconState preset fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    SlackChainInvariant config checks V U W (block (Vector.replicate 32 0)) votes block
      ⟨fork, state⟩ := by
  obtain ⟨before, holds⟩ := initializeBeaconStateFromEth1_invariant computed
  obtain ⟨slot, previous, current⟩ := initializeBeaconStateFromEth1_checkpoints computed
  refine ⟨holds, (initializeBeaconStateFromEth1_target computed).2, fun later => ?_,
    fun altair => absurd altair (Nat.not_le_of_lt before), fun _ current pending member => ?_,
    (initializeBeaconStateFromEth1_target computed).1, ?_⟩
  · simp [getCurrentEpoch, slot, computeEpochAtSlot, GENESIS_SLOT, GENESIS_EPOCH] at later
  · rw [initializeBeaconStateFromEth1_pending computed] at member
    simp at member
  · unfold SlackJustifiedCheckpoints
    rw [previous, current]
    exact ⟨JustifiedBy.root, JustifiedBy.root⟩

/-- Along a chain from genesis, the two justified checkpoints are slack-justified in the model.

Each step must meet its hypotheses.

The genesis block of the model is the block of the zero root.

The sets, weights and votes are bounded from one side only.

So the result is meaningful for the active sets and the effective balances.

The signed votes do not yet bound who voted. -/
theorem slackJustifiedCheckpoints_of_chain (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state)
    {last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (SlackStep config checks V U W votes block) ⟨fork, state⟩ last) :
    SlackJustifiedCheckpoints V U W (block (Vector.replicate 32 0)) votes block last.state :=
  (SlackChainInvariant.of_chain positive window apart
    (initializeBeaconStateFromEth1_slackChainInvariant computed) steps).slack

/-- Along a run of steps of a chain from genesis, the two justified checkpoints are slack-justified.

Each step must meet its hypotheses when a run from genesis reaches it and it reaches the last state.

That is every step between the two, on any run, not only the steps of one run.

A block that the state transition accepts is such a run.

The genesis block of the model is the block of the zero root. -/
theorem slackJustifiedCheckpoints_of_chainSteps (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
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
      SlackStepHypotheses config checks V U W votes block forked after) :
    SlackJustifiedCheckpoints V U W (block (Vector.replicate 32 0)) votes block last.state :=
  slackJustifiedCheckpoints_of_chain positive window apart computed (chainSteps_and steps meets)

end EthLib.Consensus
