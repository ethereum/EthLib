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

The votes are those of the data that some state between the first and the last accepts as signed.

That acceptance asks only that some signature of the keys verifies on the data.

So under the BLS checks it holds for every data that a key of the registry can sign.

So each validator of the set of a target counts as a voter for each link.

The theorem then bounds the epochs, blocks, sets and weights of the justified checkpoints.

It does not bound who voted.

The step asks only the stake, the order of the blocks and the preset.

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

/-- The votes of the model that some state between the first and the last state accepts as signed.

The state lies on any run of steps from the first state to the last one.

It accepts data as signed when some signature of the keys verifies on it. -/
def runVotes (config : Config) (checks : SignatureChecks) (block : Root → β)
    (first last : ForkedBeaconState preset) : Set (Vote ValidatorIndex β) :=
  {vote | ∃ forked, Relation.ReflTransGen (ChainStep config checks) first forked ∧
    Relation.ReflTransGen (ChainStep config checks) forked last ∧
    vote ∈ ffgVotes block {signed | SignedVote config checks forked.state signed}}

/-- Along a run of steps of a chain from genesis, both justified checkpoints are slack-justified.

The validator set of a checkpoint is the active set of its epoch in the last state.

Its second set is the active set of the next epoch in the last state.

Its weights are the effective balances of each state whose step makes it current justified.

The votes are those of the data that some state between genesis and the last accepts as signed.

Each step on any run between them must meet the bounds on the stake and the blocks.

A state accepts data as signed when some signature of the keys verifies on it.

So the votes do not bound who voted.

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
      (runVotes config checks block ⟨fork, state⟩ last) block last.state := by
  refine slackJustifiedCheckpoints_of_chainSteps positive window apart computed steps
    fun forked after reach step rest => ?_
  have bounds := meets forked after reach step rest
  have kept : ActiveKept (getCurrentEpoch forked.state) forked.state last.state :=
    step.activeKept.trans ((activeKept_of_chainSteps rest).mono step.currentEpoch_le)
  refine ⟨bounds, fun _ _ => ?_, fun changed root rootOk => ?_⟩
  · rintro _ ⟨signer, signed, rfl⟩
    exact ⟨forked, reach, .head step rest, signer, signed, rfl⟩
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

end EthLib.Consensus
