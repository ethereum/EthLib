module

public import EthLib.Consensus.BeaconApi.LightClient
public import EthLib.Consensus.Proofs.ForkChoice.Reachable
import EthLib.Consensus.Proofs.BeaconApi.LightClientBootstrap
import EthLib.Consensus.Proofs.BeaconApi.StateQueries
import EthLib.Consensus.Proofs.ForkSchedule

/-!
# Proofs: a light client bootstrap served from a store that the handlers reach

A bootstrap that the node serves from such a store starts a light client that trusts its block.

The store holds the block under its own root, and the state after it with the state root it names.

That result needs the forks from Capella to Heze in order.

It also needs a lawful state type and nonzero preset sizes.

Such a store also serves the bootstrap of each block of the fork of its slot.

It refuses every other block.

These served and refused cases need the post state of the block to be from the Altair fork epoch on.

They need the anchor state at the slot of the anchor block, with the header of that block.

Only the state roots of the two headers may differ.

They also need Electra at or before Fulu and Gloas at or before Heze, with the same type and sizes.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- A bootstrap served from a reachable store starts a light client that trusts its block.

It needs the schedule to put the forks from Capella to Heze in order.

It needs the sizes of the preset that the block and the state hold to be nonzero.

It needs the state type to be lawful. -/
theorem bootstrapFor_valid_of_reachable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store) {root : Root}
    {bootstrap : LightClientBootstrap preset fork}
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
      config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
      config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
      config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
      config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    (served : bootstrapFor config store root = .ok bootstrap) :
    ∃ lightClient, initializeLightClientStore config root bootstrap = .ok lightClient := by
  cases held : store.blocks[root]? with
  | none =>
    rw [bootstrapFor_of_missing (.inl held)] at served
    cases served
  | some block =>
    cases heldState : store.blockStates[root]? with
    | none =>
      rw [bootstrapFor_of_missing (.inr heldState)] at served
      cases served
    | some state =>
      exact bootstrapFor_valid held heldState (reachable.root held)
        (stateRoot_blockStates reachable heldState held) ordered served

/-- A reachable store serves the bootstrap of a root whose block and post state it holds.

It needs that state to be from the Altair fork epoch on.

It needs the schedule to give the fork of the store at the slot of the block.

It needs the anchor state to sit at the slot of the anchor block.

It needs the latest block header of the anchor state to match that block but for the state root.

It needs the schedule to put Electra at or before Fulu, and Gloas at or before Heze.

It needs the state type to be lawful, and the sizes of the preset in the block to be nonzero.

It holds for a store of any fork from Altair, under any schedule with those two orders. -/
theorem bootstrapFor_ok_of_reachable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (electraFulu : config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH)
    (gloasHeze : config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (held : store.blocks[root]? = some block) (heldState : store.blockStates[root]? = some state)
    (fromAltair : config.ALTAIR_FORK_EPOCH ≤ computeEpochAtSlot preset state.slot)
    (scheduled : config.forkAtEpoch (computeEpochAtSlot preset block.slot) = fork) :
    ∃ bootstrap, bootstrapFor config store root = .ok bootstrap := by
  obtain ⟨atBlock, slotHeld, proposerHeld, parentHeld, bodyHeld⟩ :=
    reachable.blockState_latestBlockHeader anchorSlot anchorHeader held heldState
  -- The schedule gives the fork of the store at an epoch from Altair on, so it is from Altair.
  have altair : Fork.altair ≤ fork :=
    scheduled ▸ Config.le_forkAtEpoch (fork := .altair) rfl (atBlock ▸ fromAltair)
  have layout := (stateForkAtSlot_gindices altair (Nat.le_refl _) (atBlock ▸ scheduled)
    electraFulu gloasHeze).2.1
  -- The state gives the header of the block, since its root is the state root of the block.
  have stated : SszType.hashTreeRoot state = .ok block.stateRoot :=
    stateRoot_blockStates reachable heldState held
  have headed : state.blockHeader =
      .ok { state.latestBlockHeader with stateRoot := block.stateRoot } := by
    simp [BeaconState.blockHeader, stated, LightClientError.liftRoot, Except.mapError, bind,
      Except.bind, pure, Except.pure]
  have same : { state.latestBlockHeader with stateRoot := block.stateRoot } =
      BeaconBlockHeader.mk block.slot block.proposerIndex block.parentRoot block.stateRoot
        state.latestBlockHeader.bodyRoot := by
    rw [← slotHeld, ← proposerHeld, ← parentHeld]
  obtain ⟨bootstrap, created⟩ := createLightClientBootstrap_exists
    (block := ⟨block, Vector.replicate 96 0⟩) altair fromAltair (atBlock.trans slotHeld.symm)
    headed (same ▸ BeaconBlock.hashTreeRoot_header bodyHeld) layout
  refine ⟨bootstrap, ?_⟩
  simp [bootstrapFor, held, heldState, scheduled, created, Except.mapError]

/-- A reachable store gives a root the error with code 404 that names it in one case only.

That case is a block whose fork is not the fork that the schedule gives at its slot.

It needs the store to hold the block and the post state of the root.

It needs that state to be from the Altair fork epoch on.

It needs the anchor state to sit at the slot of the anchor block.

It needs the latest block header of the anchor state to match that block but for the state root.

It needs the schedule to put Electra at or before Fulu, and Gloas at or before Heze.

It needs the state type to be lawful, and the sizes of the preset in the block to be nonzero. -/
theorem bootstrapFor_error_iff_of_reachable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (electraFulu : config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH)
    (gloasHeze : config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (held : store.blocks[root]? = some block) (heldState : store.blockStates[root]? = some state)
    (fromAltair : config.ALTAIR_FORK_EPOCH ≤ computeEpochAtSlot preset state.slot) :
    bootstrapFor config store root = .error (noBootstrap root) ↔
      config.forkAtEpoch (computeEpochAtSlot preset block.slot) ≠ fork := by
  constructor
  · intro refused scheduled
    obtain ⟨bootstrap, served⟩ := bootstrapFor_ok_of_reachable reachable anchorSlot
      anchorHeader electraFulu gloasHeze held heldState fromAltair scheduled
    rw [served] at refused
    cases refused
  · intro other
    simp [bootstrapFor, held, heldState, other]

end EthLib.Consensus.BeaconApi
