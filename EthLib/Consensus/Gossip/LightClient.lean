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
  -- `3 * k > 2 * N`, for `k` participants and `N = SYNC_COMMITTEE_SIZE`.
  aggregate.participants * 3 > preset.SYNC_COMMITTEE_SIZE.toNat * 2

/-- The light client updates that a node forwarded on each topic, the latest first. -/
structure LightClientForwarded (preset : Preset) (fork : Fork) where
  /-- The finality updates that the node forwarded. -/
  finalityUpdates : List (LightClientFinalityUpdate preset fork) := []
  /-- The optimistic updates that the node forwarded. -/
  optimisticUpdates : List (LightClientOptimisticUpdate preset fork) := []

/-- Whether a finality update is newer than one forwarded before. -/
def LightClientFinalityUpdate.isNewerThan (update prior : LightClientFinalityUpdate preset fork) :
    Bool :=
  -- Let `f` and `f'` be the finalized slots of the update and of the earlier one.
  --
  -- It is newer when `f' < f`.
  prior.finalizedHeader.beacon.slot < update.finalizedHeader.beacon.slot ||
    -- It is also newer when `f' = f` and a supermajority signed it but not the earlier one.
    (prior.finalizedHeader.beacon.slot == update.finalizedHeader.beacon.slot &&
      update.syncAggregate.hasSupermajority && !prior.syncAggregate.hasSupermajority)

/-- The optimistic update in a finality update: attested header, sync aggregate, signature slot. -/
def LightClientFinalityUpdate.toOptimisticUpdate (update : LightClientFinalityUpdate preset fork) :
    LightClientOptimisticUpdate preset fork where
  attestedHeader := update.attestedHeader
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- Whether the sync committee messages of a slot are due, by the clock.

A time that leaves the 64-bit range is an error. -/
def isSyncMessageDue (config : Config) (preset : Preset) (genesisTimeMs : UInt64) (slot : Slot)
    (currentTimeMs : UInt64) : Except ArithError Bool := do
  -- Let `t_0` be the start of the slot, in milliseconds.
  let start ← computeTimeAtSlotMs config genesisTimeMs slot
  -- Let `d` be the time into a slot at which sync committee messages are due.
  --
  -- It is that of the fork of the epoch of the slot.
  --
  -- The source does not say which fork's due time applies; this reads the fork of the slot.
  let due ← getSyncMessageDueMs config (config.forkAtEpoch (computeEpochAtSlot preset slot))
  -- Let `t` be the time of the clock.
  --
  -- The messages are due when `t_0 + d ≤ t + MAXIMUM_GOSSIP_CLOCK_DISPARITY`.
  let deadline ← addChecked start due
  let latest ← addChecked currentTimeMs config.MAXIMUM_GOSSIP_CLOCK_DISPARITY
  return deadline ≤ latest

namespace LightClientForwarded

variable (config : Config) (genesisTimeMs : UInt64) (forwarded : LightClientForwarded preset fork)

/-! ## Finality updates -/

/-- The checks of a finality update that every node runs. -/
def validateFinalityUpdate (update : LightClientFinalityUpdate preset fork)
    (currentTimeMs : UInt64) : Except ArithError ValidationResult :=
  -- Ignore it unless it is newer than every finality update forwarded before.
  (ignoreUnless (forwarded.finalityUpdates.all update.isNewerThan)
    "finality update is not newer than a forwarded one").andThenM fun _ => do
  -- Ignore it unless the sync committee messages of its signature slot are due.
  let due ← isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs
  return ignoreUnless due "finality update arrived before the sync messages were due"

/-- The checks of a finality update at a full node.

The node supplies its latest update: the highest attested slot that its fork choice selects.

A tie goes to the highest signature slot.

A node without one ignores every update. -/
def validateFinalityUpdateAtFullNode (latest : Option (LightClientUpdate preset fork))
    (update : LightClientFinalityUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult := do
  -- The checks of every node come first.
  --
  -- Then ignore it unless it equals the finality update that the latest update gives.
  return (← forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs).andThen
    fun _ => ignoreUnless (latest.map createLightClientFinalityUpdate = some update)
      "finality update differs from the local one"

/-- The checks of a finality update at a light client. -/
def validateFinalityUpdateAtLightClient (checks : SignatureChecks)
    (store : LightClientStore preset fork) (genesisValidatorsRoot : Root)
    (update : LightClientFinalityUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult :=
  -- The checks of every node come first.
  (forwarded.validateFinalityUpdate config genesisTimeMs update currentTimeMs) >>= fun first =>
  first.andThenM fun _ => do
  -- Let `s` be the slot of the clock.
  let currentSlot ← computeSlotAtTimeMs config genesisTimeMs currentTimeMs
  -- Reject it unless the store accepts it at `s`.
  match processLightClientFinalityUpdate config checks store update currentSlot
      genesisValidatorsRoot with
  | .error _ => return .reject "finality update is invalid"
  | .ok next =>
    -- Ignore it unless it raises the slot of the finalized header of the store.
    return ignoreUnless (store.finalizedHeader.beacon.slot < next.finalizedHeader.beacon.slot)
      "finality update does not advance the finalized header"

/-- The updates after a finality update is forwarded. -/
def recordFinalityUpdate (update : LightClientFinalityUpdate preset fork) :
    LightClientForwarded preset fork :=
  -- The update comes first among the forwarded finality updates.
  { forwarded with finalityUpdates := update :: forwarded.finalityUpdates }

/-! ## Optimistic updates -/

/-- The checks of an optimistic update that every node runs. -/
def validateOptimisticUpdate (update : LightClientOptimisticUpdate preset fork)
    (currentTimeMs : UInt64) : Except ArithError ValidationResult :=
  -- Ignore it unless it attests a later slot than every optimistic update forwarded before.
  (ignoreUnless (forwarded.optimisticUpdates.all fun prior =>
      prior.attestedHeader.beacon.slot < update.attestedHeader.beacon.slot)
    "optimistic update is not newer than a forwarded one").andThenM fun _ => do
  -- Ignore it unless the sync committee messages of its signature slot are due.
  let due ← isSyncMessageDue config preset genesisTimeMs update.signatureSlot currentTimeMs
  return ignoreUnless due "optimistic update arrived before the sync messages were due"

/-- The checks of an optimistic update at a full node.

The node supplies its latest update: the highest attested slot that its fork choice selects.

A tie goes to the highest signature slot.

A node without one ignores every update. -/
def validateOptimisticUpdateAtFullNode (latest : Option (LightClientUpdate preset fork))
    (update : LightClientOptimisticUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult := do
  -- The checks of every node come first.
  --
  -- Then ignore it unless it equals the optimistic update that the latest update gives.
  return (← forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs).andThen
    fun _ => ignoreUnless (latest.map createLightClientOptimisticUpdate = some update)
      "optimistic update differs from the local one"

/-- The checks of an optimistic update at a light client. -/
def validateOptimisticUpdateAtLightClient (checks : SignatureChecks)
    (store : LightClientStore preset fork) (genesisValidatorsRoot : Root)
    (update : LightClientOptimisticUpdate preset fork) (currentTimeMs : UInt64) :
    Except ArithError ValidationResult :=
  -- The checks of every node come first.
  (forwarded.validateOptimisticUpdate config genesisTimeMs update currentTimeMs) >>= fun first =>
  first.andThenM fun _ => do
  -- Let `s` be the slot of the clock.
  let currentSlot ← computeSlotAtTimeMs config genesisTimeMs currentTimeMs
  -- Reject it unless the store accepts it at `s`.
  match processLightClientOptimisticUpdate config checks store update currentSlot
      genesisValidatorsRoot with
  | .error _ => return .reject "optimistic update is invalid"
  | .ok next =>
    -- It repeats the latest forwarded finality update when it equals the optimistic part of it.
    let repeats := forwarded.finalityUpdates.head?.map (·.toOptimisticUpdate) = some update
    -- It advances the store when it raises the slot of the optimistic header of the store.
    let advances := store.optimisticHeader.beacon.slot < next.optimisticHeader.beacon.slot
    -- Ignore it unless it repeats or advances.
    return ignoreUnless (repeats || advances)
      "optimistic update neither repeats the finality update nor advances the optimistic header"

/-- The updates after an optimistic update is forwarded. -/
def recordOptimisticUpdate (update : LightClientOptimisticUpdate preset fork) :
    LightClientForwarded preset fork :=
  -- The update comes first among the forwarded optimistic updates.
  { forwarded with optimisticUpdates := update :: forwarded.optimisticUpdates }

end LightClientForwarded

end EthLib.Consensus
