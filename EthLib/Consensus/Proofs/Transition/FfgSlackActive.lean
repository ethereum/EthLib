module

public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.FfgSlackChain

/-!
# Proofs: along a chain, the justified checkpoints are slack-justified for the active sets

The theorem on chains takes the sets, weights and votes of the model as parameters.

Here they come from the chain itself.

The validator set of a checkpoint is the active set of its epoch.

Its second set is the active set of the next epoch.

Both are read in the last state of the run.

From the step that justifies a checkpoint of an epoch on, the active set of that epoch stays fixed.

So the last state gives the validator set that this step reads.

For a checkpoint of the previous epoch, it also gives the second set that the step reads.

For a checkpoint of the current epoch, the step reads no second set.

Its validators that exit at the next epoch then count as slack, which that step does not need.

Its weights are the effective balances of each state whose step makes it current justified.

That step may lie on any run between the first and the last state.

The votes are those that the block steps between the first and the last state cast.

A block casts a vote for each validator that the bits of one of its attestations show.

The committees are those of the state before the block.

The block accepts each of its attestations only when the signature checks accept it.

Reading such a vote as signed by its validator assumes the BLS checks and unforgeable aggregates.

So the voters of a link are validators whose attestations a block of some run applied.

The step asks only the stake, the order of the blocks and the preset.

The blocks of the model can also be the roots themselves, ordered by the links of reached states.

Two roots are linked when a state that genesis reaches records them at consecutive slots.

The zero root is also linked to the root recorded at slot zero.

Then the order of the blocks holds by construction, and the step asks only the stake.

The slack is the stake of the set `E(V t, U t)` of Gasper §8.6, Definition 8.1.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {β : Type*} [Preorder β]
  {block : Root → β}

/-- The active set of an epoch of the model in a state.

An epoch of 2^64 or more wraps to a smaller one, so the next set of the last epoch is that of 0. -/
def activeSetAt {fork : Fork} (state : BeaconState preset fork) (epoch : ℕ) :
    Finset ValidatorIndex :=
  (getActiveValidatorIndices state epoch.toUInt64).toFinset

/-- The active set of an epoch of the model, read at the number of an epoch of the state. -/
@[simp] theorem activeSetAt_toNat {fork : Fork} (state : BeaconState preset fork) (epoch : Epoch) :
    activeSetAt state epoch.toNat = (getActiveValidatorIndices state epoch).toFinset := by
  simp only [activeSetAt, UInt64.ofNat_toNat]

/-- The effective balances of each state whose step makes a checkpoint the current justified one.

The step lies on any run of steps from the first state to the last one.

It changes the current justified checkpoint to that checkpoint. -/
def justifyingBalances (config : Config) (checks : SignatureChecks) (block : Root → β)
    (first last : ForkedBeaconState preset) (c : Models.Ffg.Checkpoint β) :
    Set (ValidatorIndex → ℕ) :=
  {weights | ∃ forked after, Relation.ReflTransGen (ChainStep config checks) first forked ∧
    ChainStep config checks forked after ∧
    Relation.ReflTransGen (ChainStep config checks) after last ∧
    after.state.currentJustifiedCheckpoint ≠ forked.state.currentJustifiedCheckpoint ∧
    after.state.currentJustifiedCheckpoint.toFfg block = c ∧
    weights = fun index => balanceAt forked.state index.toNat}

/-- The votes that the block steps between the first and the last state cast.

The step lies on any run of steps from the first state to the last one.

So the set may hold votes of several runs, which only widens the voters that the theorem allows. -/
def runVotes (config : Config) (checks : SignatureChecks)
    (first last : ForkedBeaconState preset) : Set (ValidatorIndex × AttestationData) :=
  {vote | ∃ forked after, Relation.ReflTransGen (ChainStep config checks) first forked ∧
    Relation.ReflTransGen (ChainStep config checks) after last ∧
    vote ∈ blockStepVotes config checks forked after}

/-- Along a run of steps of a chain from genesis, both justified checkpoints are slack-justified.

The validator set of a checkpoint is the active set of its epoch in the last state.

Its second set is the active set of the next epoch in the last state.

Its weights are the effective balances of each state whose step makes it current justified.

The votes are those that the block steps between genesis and the last state cast.

Each vote comes from an attestation that a block of some run between them applied.

Each step on any run between them must meet the bounds on the stake and the blocks.

The order of the blocks is an assumption on the map from roots to blocks.

An epoch must have at least one slot, and the buffer of roots must cover two epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis block of the model is the block of the zero root. -/
theorem slackJustifiedCheckpoints_activeSetAt_of_chainSteps
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
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
      SlackStepBounds block forked after) :
    SlackJustifiedCheckpoints (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1))
      (justifyingBalances config checks block ⟨fork, state⟩ last) (block (Vector.replicate 32 0))
      (ffgVotes block (runVotes config checks ⟨fork, state⟩ last)) block last.state := by
  refine slackJustifiedCheckpoints_of_chainSteps positive window apart computed steps
    fun forked after reach step rest => ?_
  have bounds := meets forked after reach step rest
  have kept : ActiveKept (getCurrentEpoch forked.state) forked.state last.state :=
    (step.activeKept.trans ((activeKept_of_chainSteps rest).mono
      (activityFixedEpoch_mono step.currentEpoch_le))).mono
        (getCurrentEpoch_le_activityFixedEpoch _)
  refine ⟨bounds, fun vote member => ⟨forked, after, reach, rest, member⟩,
    fun changed root rootOk => ?_⟩
  obtain ⟨recent, rootAfter⟩ := step.getBlockRoot_currentJustified_of_ne window changed
  rw [rootOk, Except.ok.injEq] at rootAfter
  have previous := getPreviousEpoch_toNat forked.state
  set epoch := after.state.currentJustifiedCheckpoint.epoch with epochEq
  have below : epoch ≤ getCurrentEpoch forked.state := by
    rcases recent with same | same
    · rw [same, UInt64.le_iff_toNat_le, previous]
      omega
    · rw [same]
      exact UInt64.le_refl _
  have activeEq : activeSetAt last.state epoch.toNat =
      (getActiveValidatorIndices forked.state epoch).toFinset := by
    rw [activeSetAt_toNat, kept.getActiveValidatorIndices_eq below]
  refine ⟨activeEq, ⟨forked, after, reach, step, rest, changed, ?_, rfl⟩, ?_⟩
  · simp only [Checkpoint.toFfg, rootAfter, epochEq]
  · dsimp only
    by_cases current : epoch = getCurrentEpoch forked.state
    · rw [activeEq, current]
      exact Finset.inter_subset_left
    -- The previous epoch is then below the current one, so its next epoch is the current one.
    have previousEq : epoch = getPreviousEpoch forked.state := recent.resolve_right current
    have next : epoch.toNat + 1 = (getCurrentEpoch forked.state).toNat := by
      have ne := mt UInt64.toNat_inj.mp current
      rw [previousEq, previous] at ne ⊢
      omega
    rw [next, activeSetAt_toNat _ (getCurrentEpoch forked.state),
      kept.getActiveValidatorIndices_eq (UInt64.le_refl _)]
    exact Finset.inter_subset_right

/-- Along a run of steps of a chain from genesis, both justified checkpoints are slack-justified.

The blocks of the model are the roots, ordered by the links of the states that genesis reaches.

The sets are the active sets, the weights the effective balances, and the votes those of the run.

Each step on any run between them must meet the bound on the stake.

An epoch must have at least one slot, and the buffer of roots must cover two epochs.

The seed lookahead must leave room in the buffer of RANDAO mixes.

The genesis block of the model is the zero root. -/
theorem slackJustifiedCheckpoints_chainRoot_of_chainSteps
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
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
          (getActiveValidatorIndices forked.state (getCurrentEpoch forked.state)).toFinset) :
    SlackJustifiedCheckpoints (fun c => activeSetAt last.state c.epoch)
      (fun c => activeSetAt last.state (c.epoch + 1))
      (justifyingBalances config checks (toChainRoot config checks ⟨fork, state⟩)
        ⟨fork, state⟩ last)
      (toChainRoot config checks ⟨fork, state⟩ (Vector.replicate 32 0))
      (ffgVotes (toChainRoot config checks ⟨fork, state⟩)
        (runVotes config checks ⟨fork, state⟩ last))
      (toChainRoot config checks ⟨fork, state⟩) last.state :=
  slackJustifiedCheckpoints_activeSetAt_of_chainSteps positive window apart computed steps
    fun forked after reach step rest =>
      ⟨large forked after reach step rest,
        fun _ member => Relation.ReflTransGen.single ⟨after, reach.tail step, member⟩⟩

end EthLib.Consensus
