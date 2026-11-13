module

public import EthLib.Consensus.BeaconApi.Config
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Proofs: the answers of the Beacon API that describe the chain

No name appears twice in the spec map.

Each upgrade writes into the state the entry of its fork in the fork schedule that the API reports.

It does so when the upgrade is due and the state before it holds the version of its own fork.

The last entry that has started at an epoch gives the fork version at that epoch.

With fork epochs that do not decrease, the entry with the largest started epoch gives it too.

The genesis state that deposits build holds the genesis fork version that the API reports.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- An upgrade writes the version of its fork, and the current epoch, into the state. -/
private theorem upgradeNext_forkVersions {pre : ForkedBeaconState preset}
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

/-- No name appears twice in the spec map. -/
theorem specMap_keys_nodup (config : Config) (preset : Preset) :
    ((specMap config preset).map (·.1)).Nodup := by
  simp only [specMap, configEntries, presetEntries, List.map_append, List.map_cons, List.map_nil]
  decide +kernel

/-- The entry of the fork after a consensus fork is in the fork schedule. -/
theorem nextForkEntry_mem_forkSchedule {entry : ForkVersions}
    (found : nextForkEntry config fork = some entry) : entry ∈ forkSchedule config := by
  refine List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨fork, ?_, found⟩)
  cases fork <;> simp_all [forksBeforeHeze, nextForkEntry, Config.nextFork]

/--
Consider an upgrade that is due at the slot of a state.

Let the state hold the version of its fork as its current version.

Then the upgrade writes into the state the entry of the next fork in the fork schedule.
-/
theorem forkSchedule_upgrade {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post)
    (due : upgradeDue config pre = true)
    (current : pre.state.forkVersions.currentVersion = config.forkVersion pre.fork) :
    nextForkEntry config pre.fork = some post.val.state.forkVersions ∧
      post.val.state.forkVersions ∈ forkSchedule config := by
  have entry : nextForkEntry config pre.fork = some post.val.state.forkVersions := by
    have fork := upgradeNext_fork computed
    have versions := upgradeNext_forkVersions computed
    cases next : config.nextFork pre.fork with
    | none => simp [next] at fork
    | some found =>
      obtain ⟨nextFork, epoch⟩ := found
      rw [next] at fork
      simp only [Option.map_some, Option.some.injEq] at fork
      simp only [upgradeDue, next, Bool.and_eq_true, Option.any_some, beq_iff_eq] at due
      rw [versions, nextForkEntry, next, fork]
      simp [current, getCurrentEpoch, due.2]
  exact ⟨entry, nextForkEntry_mem_forkSchedule entry⟩

/-- The last entry of the fork schedule that has started at an epoch has the fork version there.

An entry has started when its epoch is at or before the epoch.

This holds for every configuration, whatever the order of its fork epochs. -/
theorem forkSchedule_lastStarted (epoch : Epoch) :
    ((forkSchedule config).reverse.find? (·.epoch ≤ epoch)).map (·.currentVersion) =
      some (config.computeForkVersion epoch) := by
  simp only [forkSchedule, forksBeforeHeze, nextForkEntry, Config.nextFork, List.filterMap_cons,
    Option.map_some, List.filterMap_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.find?_cons, List.find?_nil, Config.computeForkVersion,
    Config.forkAtEpoch]
  have zero : (0 : Epoch) ≤ epoch := UInt64.zero_le
  by_cases h1 : config.HEZE_FORK_EPOCH ≤ epoch <;> simp only [h1, decide_true, decide_false,
    ite_true, ite_false]
  · rfl
  by_cases h2 : config.GLOAS_FORK_EPOCH ≤ epoch <;> simp only [h2, decide_true, decide_false,
    ite_true, ite_false]
  · simp +decide [Config.forkVersion]
  by_cases h3 : config.FULU_FORK_EPOCH ≤ epoch <;> simp only [h3, decide_true, decide_false,
    ite_true, ite_false]
  · simp +decide [Config.forkVersion]
  by_cases h4 : config.ELECTRA_FORK_EPOCH ≤ epoch <;> simp only [h4, decide_true, decide_false,
    ite_true, ite_false]
  · simp +decide [Config.forkVersion]
  by_cases h5 : config.DENEB_FORK_EPOCH ≤ epoch <;> simp only [h5, decide_true, decide_false,
    ite_true, ite_false]
  · simp +decide [Config.forkVersion]
  by_cases h6 : config.CAPELLA_FORK_EPOCH ≤ epoch <;> simp only [h6, decide_true, decide_false,
    ite_true, ite_false]
  · simp +decide [Config.forkVersion]
  by_cases h7 : config.BELLATRIX_FORK_EPOCH ≤ epoch <;> simp only [h7, decide_true, decide_false,
    ite_true, ite_false]
  · simp +decide [Config.forkVersion]
  by_cases h8 : config.ALTAIR_FORK_EPOCH ≤ epoch <;> simp only [h8, decide_true, decide_false,
    ite_true, ite_false]
  · simp +decide [Config.forkVersion]
  · simp +decide [Config.forkVersion, zero]

/--
Let the epochs of the fork schedule not decrease along it.

Take the entry with the largest epoch at or before an epoch, and the later one on a tie.

It has the fork version at that epoch.

The order is needed: take Altair at epoch 10, Bellatrix at epoch 5, and epoch 12.

That entry is then the one of Altair, while the fork version is the one of Bellatrix.
-/
theorem forkSchedule_version
    (ordered : (forkSchedule config).Pairwise fun earlier later => earlier.epoch ≤ later.epoch)
    (epoch : Epoch) :
    (latestStarted (·.epoch) (forkSchedule config).reverse epoch).map (·.currentVersion) =
      some (config.computeForkVersion epoch) := by
  have sorted : (forkSchedule config).reverse.Pairwise
      fun earlier later => later.epoch ≤ earlier.epoch := by
    rw [List.pairwise_reverse]
    exact ordered
  unfold latestStarted
  rw [List.mergeSort_of_pairwise (by simpa using sorted)]
  exact forkSchedule_lastStarted epoch

/-- The genesis state that deposits build holds the genesis fork version that the API reports. -/
theorem genesisInfo_version {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit} {state : BeaconState preset fork}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    state.forkVersions.currentVersion = (genesisInfo config state).genesisForkVersion := by
  obtain ⟨before, genesisTime, bodyRoot, activated, root, frame, rfl⟩ :=
    initializeBeaconStateFromEth1_frame computed
  exact congrArg ForkVersions.currentVersion frame.forkVersions

end EthLib.Consensus.BeaconApi
