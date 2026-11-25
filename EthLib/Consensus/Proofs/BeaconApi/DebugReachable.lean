module

public import EthLib.Consensus.Proofs.BeaconApi.Debug
public import EthLib.Consensus.Proofs.ForkChoice.HeadTotality
import EthLib.Base.Proofs.MapM
import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.Ghost
import EthLib.Consensus.Proofs.ForkChoice.OptimisticSync

/-!
# Proofs: the fork choice answer on a reachable store

A store that the handlers build with a forward clock never answers the fork choice with code 500.

That needs the state of the justified checkpoint, which a block alone does not store.

The bounds are those of the head computation.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models

variable {preset : Preset} {fork : Fork} {config : Config}

namespace BeaconApi

variable {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork} {optimistic : OptimisticStore preset fork}

/-- The response succeeds when each node of the tree has a weight and a validity. -/
private theorem forkChoiceResponse_exists_ok_of_nodes
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    -- Each node of a held block has a weight.
    (weight : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block →
        ∃ w, store.getWeight config store.justifiedTally node = .ok w)
    -- Each node of the tree has a validity.
    (validity : ∀ node ∈ treeNodes store, ∃ v, nodeValidity optimistic node = .ok v) :
    ∃ envelope, forkChoiceResponse config store optimistic = .ok envelope := by
  have views : ∃ views, nodeViews config store optimistic = .ok views := by
    refine Base.mapM_exists_ok fun node mem => ?_
    obtain ⟨block, found⟩ := known_of_isTreeNode (mem_treeNodes.mp mem)
    obtain ⟨state, stateFound, -⟩ := forward.reachable.blockStatesFromParents found
    obtain ⟨w, wOk⟩ := weight node block found
    obtain ⟨v, vOk⟩ := validity node mem
    simp [nodeView, Store.block, Store.blockState, found, stateFound, wOk, vOk, bind,
      Except.bind, pure, Except.pure]
  obtain ⟨views, viewsOk⟩ := views
  simp [forkChoiceResponse, viewsOk, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Before Gloas, a forward store with its justified state never answers the fork choice with 500.

The hypotheses are those of the head computation, without the viable nodes. -/
theorem forkChoiceResponse_exists_ok (before : fork < .glamsterdam)
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    -- The anchor block must not be after the anchor state.
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    -- The parent root of the anchor block must name no held block.
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    -- An epoch must have a slot.
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    -- The proposer boost must fit the cap of `2 * 10^17` Gwei.
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17)) {state : BeaconState preset fork}
    -- The store must hold the state of the justified checkpoint.
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    -- That state must have active stake at most `2 * 10^17` Gwei.
    (bounded : stake (fun v => balanceAt state v.toNat)
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤ 2 * 10 ^ 17) :
    ∃ envelope, forkChoiceResponse config store optimistic = .ok envelope := by
  refine forkChoiceResponse_exists_ok_of_nodes forward
    (fun _ _ found => Store.getWeight_exists before forward anchorSlot unknown
      positive fits stateOk bounded found) fun node _ => ?_
  -- Before Gloas the chain ends at the block, so the validity is read.
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [nodeValidity, notGloas, bind, Except.bind, pure, Except.pure]

/-- From Gloas, a forward store with its justified state never answers the fork choice with 500.

The hypotheses are those of the head computation, without the viable nodes. -/
theorem forkChoiceResponse_exists_ok_of_gloas (gloas : .glamsterdam ≤ fork)
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    -- The anchor block must not be after the anchor state.
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    -- The parent root of the anchor block must name no held block.
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    -- The committee windows must fit.
    (fit : config.CommitteeWindowsFit preset)
    -- The proposer boost must fit the cap of `2 * 10^17` Gwei.
    (fits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    -- The head reads must fit that cap too.
    (weights : config.HeadWeightsFit preset (2 * 10 ^ 17)) {state : BeaconState preset fork}
    -- The store must hold the state of the justified checkpoint.
    (stateOk : store.checkpointState store.justifiedCheckpoint = .ok state)
    -- That state must have its registry within the limit.
    --
    -- Each held state must have its registry within the limit too.
    (within : state.RegistryWithinLimit) (held : HeldRegistriesWithinLimit store)
    -- Each set of active or known equivocating validators of that state weighs at most the cap.
    (heads : store.HeadWeightAtMost (2 * 10 ^ 17) state)
    -- An equivocator active in a held block's state has a place in the justified state.
    (registered : ActiveEquivocatorsRegistered store state)
    -- The optimistic store holds the blocks of the store, as the exports build it.
    (sameBlocks : optimistic.blocks = store.blocks) :
    ∃ envelope, forkChoiceResponse config store optimistic = .ok envelope := by
  refine forkChoiceResponse_exists_ok_of_nodes forward
    (fun _ _ found => Store.getWeight_exists_of_gloas gloas forward anchorSlot unknown fit fits
      weights stateOk within held heads registered found) fun node mem => ?_
  obtain ⟨block, found⟩ := known_of_isTreeNode (mem_treeNodes.mp mem)
  -- The payload chain of the block is read, as the blocks are those of the store.
  obtain ⟨roots, rootsOk⟩ := OptimisticStore.payloadChain_exists (store := optimistic)
    (sameBlocks ▸ forward.reachable.parentsBelow anchorSlot unknown) (root := node.root)
    (block := block) (sameBlocks ▸ found)
  by_cases full : node.payloadStatus = .full
  · simp [nodeValidity, full, bind, Except.bind, pure, Except.pure]
  · simp [nodeValidity, full, gloas, rootsOk, bind, Except.bind, pure, Except.pure]

end BeaconApi

end EthLib.Consensus
