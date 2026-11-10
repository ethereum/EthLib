module

public import EthLib.Consensus.LightClient.FullNode
public import EthLib.Networking.Gossip.Validation

/-!
# `Consensus.Gossip.LightClient`

From Altair, gossip validation of the two light client topics: finality and optimistic updates.

An update must be newer than every update of its topic that the node forwarded before.

It must also arrive once the sync committee messages of its signature slot are due.

A full node then forwards only the update that its latest update gives.

A light client forwards only an update that its store accepts.

That update must also move the store forward, or repeat the latest forwarded finality update.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Base.Uint64 Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-- Whether strictly more than two thirds of the sync committee signed.

The ranking of updates counts exactly two thirds as enough, unlike this check.

The two agree for every committee size that is not a multiple of three. -/
def SyncAggregate.hasSupermajority (aggregate : SyncAggregate preset) : Bool :=
  aggregate.participants * 3 > preset.SYNC_COMMITTEE_SIZE.toNat * 2

/-- The light client updates that a node forwarded on each topic, the latest first. -/
structure LightClientForwarded (preset : Preset) (fork : Fork) where
  /-- The finality updates that the node forwarded. -/
  finalityUpdates : List (LightClientFinalityUpdate preset fork) := []
  /-- The optimistic updates that the node forwarded. -/
  optimisticUpdates : List (LightClientOptimisticUpdate preset fork) := []

/-- Whether a finality update is newer than one forwarded before.

It is newer if it finalizes a later slot.

At the same finalized slot, it is newer if a supermajority signed it.

A supermajority must then not have signed the earlier one. -/
def LightClientFinalityUpdate.isNewerThan (update prior : LightClientFinalityUpdate preset fork) :
    Bool :=
  prior.finalizedHeader.beacon.slot < update.finalizedHeader.beacon.slot ||
    (prior.finalizedHeader.beacon.slot == update.finalizedHeader.beacon.slot &&
      update.syncAggregate.hasSupermajority && !prior.syncAggregate.hasSupermajority)

/-- The optimistic update in a finality update: attested header, sync aggregate, signature slot. -/
def LightClientFinalityUpdate.toOptimisticUpdate (update : LightClientFinalityUpdate preset fork) :
    LightClientOptimisticUpdate preset fork where
  attestedHeader := update.attestedHeader
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- Whether the sync committee messages of a slot are due, by the clock.

They are due a fixed part of the slot after its start, by the deadline of the fork of that slot.

The clock may run behind by the maximum gossip clock disparity.

A time that leaves the 64-bit range is an error. -/
def isSyncMessageDue (config : Config) (preset : Preset) (genesisTimeMs : UInt64) (slot : Slot)
    (currentTimeMs : UInt64) : Except ArithError Bool := do
  let start ← computeTimeAtSlotMs config genesisTimeMs slot
  let due ← getSyncMessageDueMs config (config.forkAtEpoch (computeEpochAtSlot preset slot))
  let deadline ← addChecked start due
  let latest ← addChecked currentTimeMs config.MAXIMUM_GOSSIP_CLOCK_DISPARITY
  return deadline ≤ latest

namespace LightClientForwarded

variable (config : Config) (genesisTimeMs : UInt64) (forwarded : LightClientForwarded preset fork)

/-! ## Finality updates -/

/-- The checks of a finality update that every node runs.

The update must be newer than every finality update forwarded before.

It must arrive once the sync committee messages of its signature slot are due. -/
def validateFinalityUpdate (update : LightClientFinalityUpdate preset fork)
    (currentTimeMs : UInt64) : Except ArithError ValidationResult :=
  (ignoreUnless (forwarded.finalityUpdates.all update.isNewerThan)
    "finality update is not newer than a forwarded one").andThenM fun _ => do
  let due ← isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs
  return ignoreUnless due "finality update arrived before the sync messages were due"

/-- The checks of a finality update at a full node.

The update must also be the finality update that the latest update of the node gives.

The node supplies that update: the one of the highest attested slot that its fork choice selects.

A node without one ignores every update. -/
def validateFinalityUpdateAtFullNode (latest : Option (LightClientUpdate preset fork))
    (update : LightClientFinalityUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult := do
  return (← forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs).andThen
    fun _ => ignoreUnless (latest.map createLightClientFinalityUpdate = some update)
      "finality update differs from the local one"

/-- The checks of a finality update at a light client.

The store must accept the update at the slot of the clock, else the update is rejected.

The update must also make the finalized header of the store newer. -/
def validateFinalityUpdateAtLightClient (checks : SignatureChecks)
    (store : LightClientStore preset fork) (genesisValidatorsRoot : Root)
    (update : LightClientFinalityUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult :=
  (forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs) >>= fun first =>
  first.andThenM fun _ => do
  let currentSlot ← computeSlotAtTimeMs config genesisTimeMs currentTimeMs
  match processLightClientFinalityUpdate config checks store update currentSlot
      genesisValidatorsRoot with
  | .error _ => return .reject "finality update is invalid"
  | .ok next =>
    return ignoreUnless (store.finalizedHeader.beacon.slot < next.finalizedHeader.beacon.slot)
      "finality update does not advance the finalized header"

/-- The updates after a finality update is forwarded. -/
def recordFinalityUpdate (update : LightClientFinalityUpdate preset fork) :
    LightClientForwarded preset fork :=
  { forwarded with finalityUpdates := update :: forwarded.finalityUpdates }

/-! ## Optimistic updates -/

/-- The checks of an optimistic update that every node runs.

The update must attest a later slot than every optimistic update forwarded before.

It must arrive once the sync committee messages of its signature slot are due. -/
def validateOptimisticUpdate (update : LightClientOptimisticUpdate preset fork)
    (currentTimeMs : UInt64) : Except ArithError ValidationResult :=
  (ignoreUnless (forwarded.optimisticUpdates.all fun prior =>
      prior.attestedHeader.beacon.slot < update.attestedHeader.beacon.slot)
    "optimistic update is not newer than a forwarded one").andThenM fun _ => do
  let due ← isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs
  return ignoreUnless due "optimistic update arrived before the sync messages were due"

/-- The checks of an optimistic update at a full node.

The update must also be the optimistic update that the latest update of the node gives.

The node supplies that update: the one of the highest attested slot that its fork choice selects.

A node without one ignores every update. -/
def validateOptimisticUpdateAtFullNode (latest : Option (LightClientUpdate preset fork))
    (update : LightClientOptimisticUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult := do
  return (← forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs).andThen
    fun _ => ignoreUnless (latest.map createLightClientOptimisticUpdate = some update)
      "optimistic update differs from the local one"

/-- The checks of an optimistic update at a light client.

The store must accept the update at the slot of the clock, else the update is rejected.

The update must also repeat the latest forwarded finality update, or advance the store.

It advances the store when it makes the optimistic header of the store newer. -/
def validateOptimisticUpdateAtLightClient (checks : SignatureChecks)
    (store : LightClientStore preset fork) (genesisValidatorsRoot : Root)
    (update : LightClientOptimisticUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult :=
  (forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs) >>= fun first =>
  first.andThenM fun _ => do
  let currentSlot ← computeSlotAtTimeMs config genesisTimeMs currentTimeMs
  match processLightClientOptimisticUpdate config checks store update currentSlot
      genesisValidatorsRoot with
  | .error _ => return .reject "optimistic update is invalid"
  | .ok next =>
    let repeats := forwarded.finalityUpdates.head?.map (·.toOptimisticUpdate) = some update
    let advances := store.optimisticHeader.beacon.slot < next.optimisticHeader.beacon.slot
    return ignoreUnless (repeats || advances)
      "optimistic update neither repeats the finality update nor advances the optimistic header"

/-- The updates after an optimistic update is forwarded. -/
def recordOptimisticUpdate (update : LightClientOptimisticUpdate preset fork) :
    LightClientForwarded preset fork :=
  { forwarded with optimisticUpdates := update :: forwarded.optimisticUpdates }

end LightClientForwarded

end EthLib.Consensus
