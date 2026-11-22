module

public import EthLib.Consensus.BeaconApi.ChainEvents
public import EthLib.Consensus.BeaconApi.Publish

/-!
# `Consensus.BeaconApi.ObjectEvents`

The events that a beacon node sends for an object that it received, from a peer or from a client.

Most of them come when the object passes the gossip rules of its topic.

The block event and the payload event come when the fork choice imports the object.

An object that gossip does not accept gives no event, so a second copy gives no gossip event.

A block that the store already holds gives no block event.

An envelope whose payload the store holds already gives no payload event.

The [event stream] gives the topics, and an example of each payload.

[event stream]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/eventstream/index.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-- A block that the fork choice imported. -/
structure BlockEvent where
  /-- The slot of the block. -/
  slot : Slot
  /-- The root of the block. -/
  block : Root
  /-- Whether the payload of the block is not yet verified. -/
  executionOptimistic : Bool
  /-- From Gloas: the builder and the block hash that the bid of the block names. -/
  bid : Option (BuilderIndex × Hash32)
  deriving DecidableEq, Repr

/-- A payload envelope: the slot, the builder and the hash of its payload, and its block. -/
structure PayloadEvent where
  /-- The slot of the payload. -/
  slot : Slot
  /-- The builder of the payload. -/
  builderIndex : BuilderIndex
  /-- The hash of the payload. -/
  blockHash : Hash32
  /-- The root of the block whose bid the payload fulfils. -/
  blockRoot : Root
  deriving DecidableEq, Repr

/-- An event for an object that the node received. -/
inductive ObjectEvent (preset : Preset) (fork : Fork) where
  /-- A block that the fork choice imported. -/
  | block (event : BlockEvent)
  /-- A block that passed gossip: its slot and its root. -/
  | blockGossip (slot : Slot) (root : Root)
  /-- Before Electra: an attestation that passed gossip. -/
  | attestation (early : fork < .pectra) (attestation : Attestation preset fork)
  /-- From Electra: a single attestation that passed gossip. -/
  | singleAttestation (electra : .pectra ≤ fork) (attestation : SingleAttestation)
  /-- A voluntary exit that passed gossip. -/
  | voluntaryExit (signed : SignedVoluntaryExit)
  /-- From Capella: a change of credentials that passed gossip. -/
  | blsToExecutionChange (capella : .shapella ≤ fork) (signed : SignedBLSToExecutionChange)
  /-- A proposer slashing that passed gossip. -/
  | proposerSlashing (slashing : ProposerSlashing)
  /-- An attester slashing that passed gossip. -/
  | attesterSlashing (slashing : AttesterSlashing preset fork)
  /-- From Altair: a sync contribution that passed gossip. -/
  | contributionAndProof (altair : .altair ≤ fork) (signed : SignedContributionAndProof preset)
  /-- From Fulu: a column sidecar that passed gossip, by the root of its block, its index and slot.
  -/
  | dataColumnSidecar (fulu : .fusaka ≤ fork) (blockRoot : Root)
    (index : DataAvailability.ColumnIndex) (slot : Slot)
  /-- From Gloas: an envelope that the fork choice imported, and whether its block is optimistic.
  -/
  | executionPayload (gloas : .glamsterdam ≤ fork) (event : PayloadEvent)
    (executionOptimistic : Bool)
  /-- From Gloas: an envelope that passed gossip. -/
  | executionPayloadGossip (gloas : .glamsterdam ≤ fork) (event : PayloadEvent)
  /-- From Gloas: a bid that passed gossip. -/
  | executionPayloadBid (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork)
  /-- From Gloas: a payload vote that passed gossip. -/
  | payloadAttestationMessage (gloas : .glamsterdam ≤ fork) (message : PayloadAttestationMessage)
  /-- From Gloas: proposer preferences that passed gossip. -/
  | proposerPreferences (gloas : .glamsterdam ≤ fork) (signed : SignedProposerPreferences)

namespace ObjectEvent

/-- The topic of an event. -/
def topic : ObjectEvent preset fork → EventTopic
  | .block _ => .block
  | .blockGossip _ _ => .blockGossip
  | .attestation _ _ => .attestation
  | .singleAttestation _ _ => .singleAttestation
  | .voluntaryExit _ => .voluntaryExit
  | .blsToExecutionChange _ _ => .blsToExecutionChange
  | .proposerSlashing _ => .proposerSlashing
  | .attesterSlashing _ => .attesterSlashing
  | .contributionAndProof _ _ => .contributionAndProof
  | .dataColumnSidecar _ _ _ _ => .dataColumnSidecar
  | .executionPayload _ _ _ => .executionPayload
  | .executionPayloadGossip _ _ => .executionPayloadGossip
  | .executionPayloadBid _ _ => .executionPayloadBid
  | .payloadAttestationMessage _ _ => .payloadAttestationMessage
  | .proposerPreferences _ _ => .proposerPreferences

/-- The fields of a payload event, as JSON. -/
def payloadFields (event : PayloadEvent) : List (String × Json) :=
  -- The two payload examples: the slot, the builder index, the block hash and the block root.
  [("slot", uintJson event.slot), ("builder_index", uintJson event.builderIndex),
    ("block_hash", ChainEvent.rootJson event.blockHash),
    ("block_root", ChainEvent.rootJson event.blockRoot)]

/-- The data of an event, as JSON.

A fork that the source does not name gives no version.

It fails only when an object cannot be written. -/
def data (fork : Fork) : ObjectEvent preset fork → Except Err Json
  -- The fields of each event are those of its example in the source.
  | .block e =>
    -- The source: from Gloas, the builder index and the block hash of the bid of the block.
    let bid := match e.bid with
      | some (builder, hash) =>
        [("builder_index", uintJson builder), ("block_hash", ChainEvent.rootJson hash)]
      | none => []
    -- The slot, the root and the optimistic flag of the block, then the fields of the bid.
    return .mkObj ([("slot", uintJson e.slot), ("block", ChainEvent.rootJson e.block),
      ("execution_optimistic", .bool e.executionOptimistic)] ++ bid)
  | .blockGossip slot root =>
    return .mkObj [("slot", uintJson slot), ("block", ChainEvent.rootJson root)]
  -- An object that the event carries is written whole, in the JSON of the API.
  | .attestation _ a => toApiJson a
  | .singleAttestation _ a => toApiJson a
  | .voluntaryExit s => toApiJson s
  | .blsToExecutionChange _ s => toApiJson s
  | .proposerSlashing s => toApiJson s
  | .attesterSlashing s => toApiJson s
  | .contributionAndProof _ s => toApiJson s
  -- The source: the root of the block of the sidecar, its index and its slot.
  | .dataColumnSidecar _ root index slot =>
    return .mkObj [("block_root", ChainEvent.rootJson root), ("index", uintJson index),
      ("slot", uintJson slot)]
  -- The imported payload also carries the optimistic flag; the gossip one does not.
  | .executionPayload _ e optimistic =>
    return .mkObj (payloadFields e ++ [("execution_optimistic", .bool optimistic)])
  | .executionPayloadGossip _ e => return .mkObj (payloadFields e)
  -- The bid, the payload vote and the preferences go under the data key, beside the version.
  | .executionPayloadBid _ s => (toApiJson s).map versioned
  | .payloadAttestationMessage _ m => (toApiJson m).map versioned
  | .proposerPreferences _ s => (toApiJson s).map versioned
where
  /-- An object under its consensus version. -/
  versioned (json : Json) : Json :=
    { version := fork.consensusVersion?, data := json : ApiEnvelope }.toJson

/-- The stream event of an object event: its topic and its data. -/
def toApiEvent (fork : Fork) (event : ObjectEvent preset fork) : Except Err ApiEvent :=
  return ⟨event.topic, ← event.data fork⟩

end ObjectEvent

/-- From Gloas: the builder and the block hash that the bid of a block names. -/
def blockBid (block : BeaconBlock preset fork) : Option (BuilderIndex × Hash32) :=
  if gloas : .glamsterdam ≤ fork then
    -- The source: the builder index and the block hash of the message of the signed bid.
    let bid := (block.body.signedExecutionPayloadBid gloas).message
    some (bid.builderIndex, bid.blockHash)
  -- Before Gloas a block has no bid.
  else none

/-- From Gloas: the payload event of an envelope. -/
def payloadEvent (gloas : .glamsterdam ≤ fork) (envelope : ExecutionPayloadEnvelope preset fork) :
    PayloadEvent :=
  -- The slot and the hash of the payload, the builder of the envelope, and the block it names.
  { slot := envelope.payload.slotNumber gloas, builderIndex := envelope.builderIndex,
    blockHash := envelope.payload.blockHash, blockRoot := envelope.beaconBlockRoot }

/-- The event of the topic of a gossip message, if its topic has one.

The topics of aggregates, sync committee messages, blob sidecars and inclusion lists have none.

It fails when the root of a block cannot be computed. -/
def objectEventOf : GossipMessage preset fork → Except Err (Option (ObjectEvent preset fork))
  -- The source: the slot and the root of a block on the beacon block topic.
  | .beaconBlock signed => do
    return some (.blockGossip signed.message.slot (← SszType.hashTreeRoot signed.message))
  | .beaconAttestation early attestation _ => return some (.attestation early attestation)
  | .singleAttestation electra attestation _ =>
    return some (.singleAttestation electra attestation)
  | .voluntaryExit signed => return some (.voluntaryExit signed)
  | .blsToExecutionChange capella signed => return some (.blsToExecutionChange capella signed)
  | .proposerSlashing slashing => return some (.proposerSlashing slashing)
  | .attesterSlashing slashing => return some (.attesterSlashing slashing)
  | .contributionAndProof altair signed => return some (.contributionAndProof altair signed)
  | .dataColumnSidecar fulu sidecar _ =>
    -- From Gloas, a sidecar names the root of its block and its slot.
    if gloas : .glamsterdam ≤ fork then
      return some (.dataColumnSidecar fulu (sidecar.beaconBlockRoot gloas) sidecar.index
        (sidecar.slot gloas))
    -- Before Gloas, the root of its signed block header is the root of its block.
    else do
      let header := (sidecar.signedBlockHeader (Nat.lt_of_not_le gloas)).message
      let root ← SszType.hashTreeRoot header
      return some (.dataColumnSidecar fulu root sidecar.index header.slot)
  | .executionPayloadEnvelope gloas signed =>
    return some (.executionPayloadGossip gloas (payloadEvent gloas signed.message))
  | .executionPayloadBid gloas signed => return some (.executionPayloadBid gloas signed)
  | .payloadAttestationMessage gloas message =>
    return some (.payloadAttestationMessage gloas message)
  | .proposerPreferences gloas signed => return some (.proposerPreferences gloas signed)
  -- The source lists no event for these four topics.
  | .aggregateAndProof _ | .syncCommitteeMessage _ _ _ | .blobSidecar _ _ _
  | .inclusionList _ _ => return none

/-- The events of a gossip message with its outcome: the event of its topic when it is accepted. -/
def eventsOfGossip (outcome : ValidationResult) (message : GossipMessage preset fork) :
    Except Err (List (ObjectEvent preset fork)) :=
  -- The source: an event only for a message that passes the validation rules of its topic.
  if outcome.isAccept then return (← objectEventOf message).toList else return []

/-- The outcome of a message that the node received, the messages seen after it, and its events. -/
def receiveGossip (context : SubmitContext preset fork) (seen : Seen)
    (message : GossipMessage preset fork) :
    Except ForkChoiceError (ValidationResult × Seen × List (ObjectEvent preset fork)) := do
  -- The source: a message comes from P2P or API.
  --
  -- EthLib's choice: a message from a client takes the same path as one from a peer.
  let (outcome, after) ← validateGossipMessage context.config context.checks context.setup seen
    context.store context.statuses context.currentTimeMs message
  return (outcome, after, ← (eventsOfGossip outcome message).mapError .ssz)

/-- The events of the messages of an item, taken in turn as the item validates them.

It fails when the root of a block cannot be computed. -/
def itemEvents (context : SubmitContext preset fork) (seen : Seen) :
    SubmitItem preset fork → Except Err (List (ObjectEvent preset fork))
  | [] => return []
  | message :: rest => do
    -- The gossip rules of the topic of the message, against the keys seen so far.
    let (reason, after) := messageFailure context seen message
    -- The source: a message that passes them gives the event of its topic.
    let event ← if reason.isNone then objectEventOf message else pure none
    -- The rest of the item, with the keys seen after this message.
    return event.toList ++ (← itemEvents context after rest)

/-- The events of a submitted list, item by item, with the keys seen that its answer threads. -/
def submittedEvents (context : SubmitContext preset fork) (seen : Seen) :
    List (SubmitItem preset fork) → Except Err (List (ObjectEvent preset fork))
  | [] => return []
  | item :: rest => do
    -- The events of the item, then those of the rest, with the keys seen after the item.
    return (← itemEvents context seen item) ++
      (← submittedEvents context (validateItem context seen item).2 rest)

/-- The block event of a block, when the store before it does not hold it.

The optimistic flag of a block tells whether its payload is not yet verified.

It fails when the root of the block cannot be computed. -/
def blockEvent? (store : Store preset fork) (optimistic : Root → Bool)
    (signed : SignedBeaconBlock preset fork) : Except Err (Option BlockEvent) := do
  let root ← SszType.hashTreeRoot signed.message
  -- EthLib's reading: a block that the store already holds gives no block event.
  if store.blocks.contains root then return none
  -- The slot, the root and the optimistic flag of the block, and from Gloas the fields of its bid.
  return some ⟨signed.message.slot, root, optimistic root, blockBid signed.message⟩

/-- The store after a block, and the block event when the block is new to the store. -/
def eventsOfBlockImport (config : Config) (checks : SignatureChecks)
    (sources : BlockSources preset fork) (store : Store preset fork) (optimistic : Root → Bool)
    (signed : SignedBeaconBlock preset fork) :
    Except ForkChoiceError (Store preset fork × List (ObjectEvent preset fork)) := do
  -- The event reads the store before the block.
  let event ← (blockEvent? store optimistic signed).mapError .ssz
  -- The source: the event comes when the fork choice imports the block; a failed import gives none.
  let after ← store.onBlock config checks sources signed
  return (after, (event.map .block).toList)

/-- From Gloas: the payload event of an envelope, when its payload is new to the store. -/
def envelopeEvent? (store : Store preset fork) (optimistic : Root → Bool)
    (gloas : .glamsterdam ≤ fork) (envelope : ExecutionPayloadEnvelope preset fork) :
    Option (ObjectEvent preset fork) :=
  let root := envelope.beaconBlockRoot
  -- EthLib's reading: a payload that the store already holds gives no payload event.
  if (store.payloads gloas).contains root then none
  else some (.executionPayload gloas (payloadEvent gloas envelope) (optimistic root))

/-- From Gloas: the store after an envelope, and the payload event when its payload is new. -/
def eventsOfEnvelopeImport (config : Config) (checks : SignatureChecks)
    (sources : BlockSources preset fork) (store : Store preset fork) (optimistic : Root → Bool)
    (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except ForkChoiceError (Store preset fork × List (ObjectEvent preset fork)) := do
  -- The source: the event comes when the fork choice imports the envelope.
  let after ← store.onExecutionPayloadEnvelope config checks sources gloas signed
  -- The event reads the store before the envelope.
  return (after, (envelopeEvent? store optimistic gloas signed.message).toList)

/-! ## Publication -/

/-- The events of a block that a client publishes, given the answer of the node. -/
def publishBlockEvents (context : SubmitContext preset fork) (seen : Seen)
    (optimistic : Root → Bool) (signed : SignedBeaconBlock preset fork)
    (outcome : PublishOutcome) : Except Err (List (ObjectEvent preset fork)) := do
  -- A block that passes gossip gives its gossip event, even when a later check refuses it.
  let gossip ← itemEvents context seen [.beaconBlock signed]
  match outcome with
  -- An integrated block also gives its block event, when the store did not hold it.
  | .integrated =>
    return gossip ++ ((← blockEvent? context.store optimistic signed).map .block).toList
  | _ => return gossip

/-- From Gloas: the events of an envelope that a client publishes, given the answer of the node. -/
def publishEnvelopeEvents (context : SubmitContext preset fork) (seen : Seen)
    (optimistic : Root → Bool) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadEnvelope preset fork) (outcome : PublishOutcome) :
    Except Err (List (ObjectEvent preset fork)) := do
  -- An envelope that passes gossip gives its gossip event, even when a later check refuses it.
  let gossip ← itemEvents context seen [.executionPayloadEnvelope gloas signed]
  match outcome with
  -- An integrated envelope also gives its payload event, when its payload is new to the store.
  | .integrated =>
    return gossip ++ (envelopeEvent? context.store optimistic gloas signed.message).toList
  | _ => return gossip

end EthLib.Consensus.BeaconApi
