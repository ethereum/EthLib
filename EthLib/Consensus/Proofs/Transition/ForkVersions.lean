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

/-- An upgrade writes the current version before it as the previous version of the state.

It writes the version of its fork as the current version, and the current epoch as its epoch. -/
theorem upgradeNext_forkVersions {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.forkVersions = ⟨pre.state.forkVersions.currentVersion,
      config.forkVersion post.val.fork, getCurrentEpoch pre.state⟩ := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToAltair_spec upgraded).2.2.2.2.2.2
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToElectra_spec upgraded).2.2.2
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToFulu_spec upgraded).2.2
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (upgradeToGloas_spec upgraded).2.2.2.2
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl
  all_goals
    simp only [upgradeNext] at computed
    cases computed

/-- A fork before Altair has the genesis fork version. -/
theorem forkVersion_of_lt_altair {fork : Fork} (before : fork < .altair) :
    config.forkVersion fork = config.GENESIS_FORK_VERSION := by
  cases fork <;> first | rfl | exact absurd before (by decide)

/-- The versions that a chain from a genesis of deposits holds at a fork.

Before Altair it is the genesis version twice, from epoch 0.

At a later fork the previous version is that of the fork before it, and the current one its own.

The epoch is the one of the config at which the fork is due. -/
private def ForkEntry (config : Config) (fork : Fork) (versions : ForkVersions) : Prop :=
  (fork < .altair ∧
      versions = ⟨config.GENESIS_FORK_VERSION, config.GENESIS_FORK_VERSION, GENESIS_EPOCH⟩) ∨
    ∃ previous epoch, config.nextFork previous = some (fork, epoch) ∧
      versions = ⟨config.forkVersion previous, config.forkVersion fork, epoch⟩

/-- A fork follows at most one fork in the schedule, at one epoch. -/
private theorem nextFork_unique {previous other fork : Fork} {epoch later : Epoch}
    (one : config.nextFork previous = some (fork, epoch))
    (two : config.nextFork other = some (fork, later)) : previous = other ∧ epoch = later := by
  cases previous <;>
    simp only [Config.nextFork, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at one <;>
    obtain ⟨rfl, rfl⟩ := one <;>
    cases other <;> simp_all [Config.nextFork]

/-- A fork that follows another in the schedule is Altair or later. -/
private theorem altair_le_of_nextFork {previous fork : Fork} {epoch : Epoch}
    (next : config.nextFork previous = some (fork, epoch)) : .altair ≤ fork := by
  cases previous <;>
    simp only [Config.nextFork, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at next <;>
    obtain ⟨rfl, -⟩ := next <;> decide

/-- An upgrade that is due keeps the versions equal to the entry of the fork. -/
private theorem forkEntry_upgrade {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) (due : upgradeDue config pre = true)
    (holds : ForkEntry config pre.fork pre.state.forkVersions) :
    ForkEntry config post.val.fork post.val.state.forkVersions := by
  have versions := upgradeNext_forkVersions computed
  have fork := upgradeNext_fork computed
  -- The upgrade is due at the epoch of the next fork.
  have next : config.nextFork pre.fork = some (post.val.fork, getCurrentEpoch pre.state) := by
    cases found : config.nextFork pre.fork with
    | none => simp [found] at fork
    | some entry =>
      obtain ⟨nextFork, epoch⟩ := entry
      rw [found] at fork
      simp only [Option.map_some, Option.some.injEq] at fork
      simp only [upgradeDue, found, Bool.and_eq_true, Option.any_some, beq_iff_eq] at due
      simp [fork, getCurrentEpoch, due.2]
  refine .inr ⟨pre.fork, getCurrentEpoch pre.state, next, ?_⟩
  rw [versions]
  rcases holds with ⟨early, same⟩ | ⟨previous, epoch, -, same⟩
  · -- A fork before Altair has the genesis version.
    rw [same, forkVersion_of_lt_altair early]
  · rw [same]

/-- Two states that chains from one genesis of deposits reach at one fork hold the same versions.

The genesis holds the genesis version twice.

Each upgrade writes the current version before it, the version of its fork, and its epoch. -/
theorem forkVersions_eq_of_fork {fork0 : Fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit} {genesis : BeaconState preset fork0}
    {a b : ForkedBeaconState preset}
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (toA : Relation.ReflTransGen (ChainStep config checks) ⟨fork0, genesis⟩ a)
    (toB : Relation.ReflTransGen (ChainStep config checks) ⟨fork0, genesis⟩ b)
    (same : a.fork = b.fork) :
    a.state.forkVersions = b.state.forkVersions := by
  obtain ⟨before, -⟩ := initializeBeaconStateFromEth1_frame initialized
  have start : ForkEntry config fork0 genesis.forkVersions :=
    .inl ⟨before, initializeBeaconStateFromEth1_forkVersions initialized⟩
  have entryA := chainSteps_forkVersions (property := ForkEntry config)
    (fun computed due holds => forkEntry_upgrade computed due holds) toA start
  have entryB := chainSteps_forkVersions (property := ForkEntry config)
    (fun computed due holds => forkEntry_upgrade computed due holds) toB start
  generalize a.state.forkVersions = versionsA at entryA ⊢
  generalize b.state.forkVersions = versionsB at entryB ⊢
  rw [same] at entryA
  rcases entryA with ⟨earlyA, sameA⟩ | ⟨previous, epoch, nextA, sameA⟩ <;>
    rcases entryB with ⟨earlyB, sameB⟩ | ⟨other, later, nextB, sameB⟩
  · rw [sameA, sameB]
  · exact absurd (altair_le_of_nextFork nextB) (Nat.not_le_of_lt earlyA)
  · exact absurd (altair_le_of_nextFork nextA) (Nat.not_le_of_lt earlyB)
  · obtain ⟨rfl, rfl⟩ := nextFork_unique nextA nextB
    rw [sameA, sameB]

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
