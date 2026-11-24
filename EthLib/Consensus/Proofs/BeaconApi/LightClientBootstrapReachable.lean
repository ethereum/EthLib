module

public import EthLib.Consensus.BeaconApi.LightClient
public import EthLib.Consensus.ForkChoice.Optimistic
public import EthLib.Consensus.ForkChoice.OptimisticSync
public import EthLib.Consensus.Proofs.ForkChoice.Reachable
import EthLib.Consensus.Proofs.BeaconApi.LightClientBootstrap
import EthLib.Consensus.Proofs.BeaconApi.StateQueries
import EthLib.Consensus.Proofs.ForkChoice.OptimisticSync
import EthLib.Consensus.Proofs.ForkSchedule

/-!
# Proofs: a light client bootstrap served from a store that the handlers reach

A bootstrap that the node serves from such a store starts a light client that trusts its block.

Such a store also serves the bootstrap of each block of the fork of its slot.

It refuses every other block.

An invalid payload keeps the answer of each root whose block stays in the store.

Recording whether a validated payload satisfies its inclusion lists keeps each bootstrap answer.

So a bootstrap served after either step on a reachable store starts a light client too.
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
      -- The store holds the block under its own root.
      --
      -- It holds the state after the block with the state root that the block names.
      exact bootstrapFor_valid held heldState (reachable.root held)
        (stateRoot_blockStates reachable heldState held) ordered served

/-- A reachable store serves the bootstrap of a root whose block and post state it holds.

It needs the state type to be lawful, and the sizes of the preset in the block to be nonzero.

It holds for a store of any fork from Altair.

It holds under any schedule that puts Electra at or before Fulu, and Gloas at or before Heze. -/
theorem bootstrapFor_ok_of_reachable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store)
    -- The anchor state sits at the slot of the anchor block.
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    -- The latest block header of the anchor state matches that block but for the state root.
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    -- The schedule puts Electra at or before Fulu.
    (electraFulu : config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH)
    -- It puts Gloas at or before Heze.
    (gloasHeze : config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (held : store.blocks[root]? = some block) (heldState : store.blockStates[root]? = some state)
    -- That state is from the Altair fork epoch on.
    (fromAltair : config.ALTAIR_FORK_EPOCH ≤ computeEpochAtSlot preset state.slot)
    -- The schedule gives the fork of the store at the slot of the block.
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

It needs the state type to be lawful, and the sizes of the preset in the block to be nonzero. -/
theorem bootstrapFor_error_iff_of_reachable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store)
    -- The anchor state sits at the slot of the anchor block.
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    -- The latest block header of the anchor state matches that block but for the state root.
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    -- The schedule puts Electra at or before Fulu.
    (electraFulu : config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH)
    -- It puts Gloas at or before Heze.
    (gloasHeze : config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    -- The store holds the block and the post state of the root.
    (held : store.blocks[root]? = some block) (heldState : store.blockStates[root]? = some state)
    -- That state is from the Altair fork epoch on.
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

/-- After an invalid payload, a root whose block stays keeps its bootstrap answer. -/
theorem bootstrapFor_onInvalidPayload {invalid : BeaconBlock preset fork}
    {latestValidHash : Option Hash32} {after : Store preset fork}
    (invalidated : store.onInvalidPayload invalid latestValidHash = .ok after) {root : Root}
    (kept : after.blocks.contains root) :
    bootstrapFor config after root = bootstrapFor config store root := by
  rcases Store.onInvalidPayload_blocks_blockStates invalidated root with ⟨blocks, states⟩ |
    ⟨gone, -⟩
  · unfold bootstrapFor
    rw [blocks, states]
  · simp [Std.TreeMap.contains_eq_isSome_getElem?, gone] at kept

/-- Recording whether a validated payload satisfies its inclusion lists keeps each bootstrap answer.

Each root gets the same bootstrap or the same refusal as before. -/
theorem bootstrapFor_recordValidatedInclusionListSatisfaction {heze : .hegota ≤ fork}
    {validated : Root} {satisfied : Bool} {after : Store preset fork}
    (recorded :
      store.recordValidatedInclusionListSatisfaction heze validated satisfied = .ok after)
    (root : Root) : bootstrapFor config after root = bootstrapFor config store root := by
  obtain rfl := Store.recordValidatedInclusionListSatisfaction_eq recorded
  rfl

/-- A bootstrap served after an invalid payload on a reachable store starts a light client.

That light client trusts the block of the bootstrap.

It needs the sizes of the preset that the block and the state hold to be nonzero.

It needs the state type to be lawful. -/
theorem bootstrapFor_valid_of_onInvalidPayload [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {invalid : BeaconBlock preset fork} {latestValidHash : Option Hash32}
    {after : Store preset fork}
    (invalidated : store.onInvalidPayload invalid latestValidHash = .ok after) {root : Root}
    {bootstrap : LightClientBootstrap preset fork}
    -- The schedule puts the forks from Capella to Heze in order.
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
      config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
      config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
      config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
      config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    (served : bootstrapFor config after root = .ok bootstrap) :
    ∃ lightClient, initializeLightClientStore config root bootstrap = .ok lightClient := by
  -- A served root still has its block, since a root without one gets the error.
  cases kept : after.blocks.contains root
  · have missing := Std.TreeMap.getElem?_eq_none_of_contains_eq_false kept
    rw [bootstrapFor_of_missing (.inl missing)] at served
    cases served
  · exact bootstrapFor_valid_of_reachable reachable ordered
      ((bootstrapFor_onInvalidPayload invalidated kept).symm.trans served)

/-- A bootstrap served after an inclusion list record on a reachable store starts a light client.

That light client trusts the block of the bootstrap.

It needs the sizes of the preset that the block and the state hold to be nonzero.

It needs the state type to be lawful. -/
theorem bootstrapFor_valid_of_recordValidatedInclusionListSatisfaction
    [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)]
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {heze : .hegota ≤ fork} {validated : Root} {satisfied : Bool} {after : Store preset fork}
    (recorded :
      store.recordValidatedInclusionListSatisfaction heze validated satisfied = .ok after)
    {root : Root} {bootstrap : LightClientBootstrap preset fork}
    -- The schedule puts the forks from Capella to Heze in order.
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
      config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
      config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
      config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
      config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    (served : bootstrapFor config after root = .ok bootstrap) :
    ∃ lightClient, initializeLightClientStore config root bootstrap = .ok lightClient :=
  bootstrapFor_valid_of_reachable reachable ordered
    ((bootstrapFor_recordValidatedInclusionListSatisfaction recorded root).symm.trans served)

end EthLib.Consensus.BeaconApi
