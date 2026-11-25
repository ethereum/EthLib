module

public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.Proofs.BeaconApi.Config
public import EthLib.Consensus.Proofs.BeaconApi.Identifiers
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates

/-!
# Proofs: the fork answer on a store that the handlers build

In a store that the handlers build, each block state holds the fork versions of the anchor state.

Consider a chain from the genesis state that deposits build, ending at the anchor state.

Then the fork answer to each state identifier that names a state is in the fork schedule.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

namespace Store

/-- The state after each block of a reachable store holds the fork versions of the anchor state. -/
theorem Reachable.blockState_forkVersions
    (reachable : Reachable config anchorState anchorBlock store) {root : Root}
    {state : BeaconState preset fork} (stored : store.blockStates[root]? = some state) :
    state.forkVersions = anchorState.forkVersions := by
  refine reachable.blockState_induction reachable.blockStatesFromParents
    (fun _ kept => kept.forkVersions = anchorState.forkVersions) (fun _ _ => rfl) ?_ stored
  -- The transition from the state of the parent keeps the fork versions.
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ transitioned parentVersions
  exact (stateTransition_forkVersions transitioned).trans parentVersions

/--
Consider an anchor state that holds the version of its fork as its current version.

In a store that the handlers build from it, each state holds that version too.
-/
theorem Reachable.blockState_currentVersion
    (reachable : Reachable config anchorState anchorBlock store)
    (current : anchorState.forkVersions.currentVersion = config.forkVersion fork) {root : Root}
    {state : BeaconState preset fork} (stored : store.blockStates[root]? = some state) :
    state.forkVersions.currentVersion = config.forkVersion fork := by
  rw [reachable.blockState_forkVersions stored]
  exact current

end Store

namespace BeaconApi

/--
Consider a chain from the genesis state that deposits build, ending at the anchor state.

In a store that the handlers build from it, the fork of each kept state is in the fork schedule.
-/
theorem stateFork_mem_forkSchedule_of_reachable {checks : SignatureChecks} {genesisFork : Fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {genesis : BeaconState preset genesisFork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {before : genesisFork < .altair}
    (initialized :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok genesis)
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨genesisFork, genesis⟩
      ⟨fork, anchorState⟩)
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    stateFork state ∈ forkSchedule config := by
  rw [stateFork, reachable.blockState_forkVersions stored]
  exact forkVersions_mem_forkSchedule_of_genesis_chainSteps initialized steps

/--
Consider a chain from the genesis state that deposits build, ending at the anchor state.

In a store that the handlers build from it, the fork answer to each named state is in the schedule.
-/
theorem stateFork_mem_forkSchedule_of_resolveStateId {checks : SignatureChecks}
    {genesisFork : Fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit} {genesis : BeaconState preset genesisFork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {before : genesisFork < .altair}
    (initialized :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok genesis)
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨genesisFork, genesis⟩
      ⟨fork, anchorState⟩)
    {stateId : StateId} {root : Root} {state : BeaconState preset fork}
    (resolved : resolveStateId config store stateId = some (root, state)) :
    stateFork state ∈ forkSchedule config :=
  stateFork_mem_forkSchedule_of_reachable reachable initialized steps
    (blockStates_of_resolveStateId resolved)

end BeaconApi

end EthLib.Consensus
