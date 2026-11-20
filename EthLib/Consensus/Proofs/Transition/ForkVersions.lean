module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.TargetSlots

/-!
# Proofs: the fork versions along a chain

A slot keeps the fork versions of a state, and so does a block.

An upgrade moves the current version to the previous one, and writes the version of its fork.

So a property of the fork and of the fork versions holds along a chain when each upgrade keeps it.

The genesis state that deposits build holds the genesis version twice, the version of Phase 0.

So along a chain from it, both versions of each state are versions of forks of the config.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- One step of a chain keeps a property of the fork and of the fork versions.

It needs each upgrade that is due to keep that property. -/
theorem chainStep_forkVersions {property : Fork → ForkVersions → Prop}
    (upgrade : ∀ {pre : ForkedBeaconState preset}
      {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
      upgradeNext config checks pre = .ok post → upgradeDue config pre = true →
      property pre.fork pre.state.forkVersions →
      property post.val.fork post.val.state.forkVersions)
    {forked after : ForkedBeaconState preset} (step : ChainStep config checks forked after)
    (holds : property forked.fork forked.state.forkVersions) :
    property after.fork after.state.forkVersions := by
  cases step with
  | slot computed =>
    -- One slot keeps the fork versions, and the upgrades due at the slot it reaches follow.
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    refine processUpgrades_induction_due
      (property := fun forked => property forked.fork forked.state.forkVersions)
      (fun due holds stepOk => upgrade stepOk due holds) ?_ upgraded
    show property forked.fork advanced.forkVersions
    rw [(advanceSlot_kept advancedOk).1]
    exact holds
  | @block blockFork blockState blockAfter engine signed _ computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    show property blockFork blockAfter.forkVersions
    rw [(frame_processBlock blockOk).forkVersions]
    exact holds

/-- Along a run of steps of a chain, a property of the fork and of the fork versions holds.

It needs the first state to meet the property, and each upgrade that is due to keep it. -/
theorem chainSteps_forkVersions {property : Fork → ForkVersions → Prop}
    (upgrade : ∀ {pre : ForkedBeaconState preset}
      {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
      upgradeNext config checks pre = .ok post → upgradeDue config pre = true →
      property pre.fork pre.state.forkVersions →
      property post.val.fork post.val.state.forkVersions)
    {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last)
    (holds : property first.fork first.state.forkVersions) :
    property last.fork last.state.forkVersions := by
  induction steps with
  | refl => exact holds
  | tail _ step more => exact chainStep_forkVersions upgrade step more

/-- The genesis state that deposits build holds the genesis version twice, from epoch 0. -/
theorem initializeBeaconStateFromEth1_forkVersions {fork : Fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {state : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    state.forkVersions =
      ⟨config.GENESIS_FORK_VERSION, config.GENESIS_FORK_VERSION, GENESIS_EPOCH⟩ := by
  obtain ⟨_, _, _, activated, _, frame, rfl⟩ := initializeBeaconStateFromEth1_frame computed
  exact frame.forkVersions

/-- Both fork versions are versions of forks of the config. -/
def ForkVersions.OfConfig (config : Config) (versions : ForkVersions) : Prop :=
  (∃ previous : Fork, versions.previousVersion = config.forkVersion previous) ∧
    ∃ current : Fork, versions.currentVersion = config.forkVersion current

/-- Fork versions of the config give a version of the config at every epoch. -/
theorem ForkVersions.OfConfig.versionAt {versions : ForkVersions}
    (ofConfig : versions.OfConfig config) (epoch : Epoch) :
    ∃ read : Fork, versions.versionAt epoch = config.forkVersion read := by
  unfold ForkVersions.versionAt
  split
  · exact ofConfig.1
  · exact ofConfig.2

/-- Along a chain from the genesis state of deposits, each state holds versions of the config.

That genesis state holds the genesis version twice, which is the version of Phase 0.

An upgrade moves the current version to the previous one, and writes the version of its fork. -/
theorem forkVersions_ofConfig_of_genesis_chainSteps {fork : Fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {genesis : BeaconState preset fork}
    {last : ForkedBeaconState preset}
    (initialized :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
        .ok genesis)
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, genesis⟩ last) :
    last.state.forkVersions.OfConfig config := by
  refine chainSteps_forkVersions (property := fun _ versions => versions.OfConfig config)
    (fun computed _ holds => ⟨?_, _, (upgradeFrame_upgradeNext computed).currentVersion⟩)
    steps ?_
  · -- The previous version after an upgrade is the current version before it.
    obtain ⟨current, same⟩ := holds.2
    exact ⟨current, (upgradeFrame_upgradeNext computed).previousVersion.trans same⟩
  · show genesis.forkVersions.OfConfig config
    rw [initializeBeaconStateFromEth1_forkVersions initialized]
    exact ⟨⟨.phase0, rfl⟩, ⟨.phase0, rfl⟩⟩

end EthLib.Consensus
