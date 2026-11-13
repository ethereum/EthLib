module

public import EthLib.Consensus.BeaconApi.ObjectEvents
public import EthLib.Consensus.BeaconApi.Publish
public import EthLib.Consensus.Exports.GossipValidation

/-!
# `Exports.BeaconApiPost`

A C-ABI export that answers requests to the pool and publish endpoints of the Beacon API.

The store of a case is built as for gossip validation, from an anchor and later blocks.

Each request is a tuple of its time in milliseconds, the name of its endpoint and its items.

A request to a publish endpoint also names its level of checks, or none for the gossip level.

Each item is the SSZ bytes of one object.

The endpoints of slashings, exits, bids, blocks and envelopes take exactly one.

The requests share the keys of the messages seen, which each valid message extends.

They also share the store, which each integrated block or envelope extends.

The store is ticked to the time of a request when that time is later than its own.

An error while ticking it fails the call.

An integrated block with a payload, or an integrated envelope, gets a valid payload status.

The node holds no blobs and samples no columns, and its execution layer accepts every payload.

So a block with blobs before Fulu is broadcast but not integrated.

From Fulu the node takes the data on trust, so it integrates an object with blobs without them.

It knows no proof-of-work block, so it never integrates the block of the merge.

From Heze it finds that every payload satisfies the inclusion lists.

A block request is the signed block alone, without the blobs that the API body may carry.

Each request gives its status code, and the position and the message of each item that failed.

It also gives the events of the event stream that it causes, each as its topic and its JSON data.

A message that passes gossip gives the event of its topic, if that topic has one.

An integrated object new to the store also gives its import event.

No event is optimistic, since the execution layer accepts every payload.

An input that the export cannot read fails with code 0.

Such inputs include bytes that do not decode and an endpoint that the fork does not serve.

An error of the fork choice on one item fails that item, with its message.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz Networking.Gossip BeaconApi
open EthLib.Exports (Result PyValue FromPy fromPy pyExport)
open Cryptography.Kzg.Exports (embeddedSetup)

/-- A request to an endpoint: its time, the name of its endpoint, its items and its level. -/
structure PostInput where
  /-- The time of the request, in milliseconds since the Unix epoch. -/
  currentTimeMs : UInt64
  /-- The name of the endpoint, the last part of its path. -/
  endpoint : String
  /-- The SSZ bytes of each item. -/
  items : List ByteArray
  /-- The level of checks of a publish endpoint, or none for the gossip level. -/
  level : Option String := none

/-- A request is a tuple of its time, its endpoint, the bytes of its items and its level, if any.
-/
instance : FromPy PostInput := ⟨fun v => do
  match (← v.sequence).toList with
  | [time, endpoint, items] => return ⟨← fromPy time, ← fromPy endpoint, ← fromPy items, none⟩
  | [time, endpoint, items, level] =>
    return ⟨← fromPy time, ← fromPy endpoint, ← fromPy items, ← fromPy level⟩
  | _ => throw "a request is (time, endpoint, items, level)"⟩

/-- Decode each item of a request as a value of one SSZ type. -/
def decodePoolItems (α : Type) [SszType α] (items : List ByteArray) : Result (List α) :=
  items.mapM (decodeInput α)

/-- The request of an endpoint, from the bytes of its items.

An endpoint that the fork of the case does not serve fails with code 0. -/
def decodePoolInput {preset : Preset} {fork : Fork} (input : PostInput) :
    Result (PoolRequest preset fork) := do
  let items := input.items
  match input.endpoint with
  | "attestations" =>
    if electra : .pectra ≤ fork then
      return .singleAttestations electra (← decodePoolItems SingleAttestation items)
    else
      let attestations ← decodePoolItems (Attestation preset fork) items
      return .attestations (Nat.lt_of_not_le electra) attestations
  | "attester_slashings" =>
    let [slashing] := items | throw (0, "the attester slashing endpoint takes one slashing")
    return .attesterSlashing (← decodeInput (AttesterSlashing preset fork) slashing)
  | "proposer_slashings" =>
    let [slashing] := items | throw (0, "the proposer slashing endpoint takes one slashing")
    return .proposerSlashing (← decodeInput ProposerSlashing slashing)
  | "voluntary_exits" =>
    let [signed] := items | throw (0, "the voluntary exit endpoint takes one exit")
    return .voluntaryExit (← decodeInput SignedVoluntaryExit signed)
  | "bls_to_execution_changes" =>
    if capella : .shapella ≤ fork then
      return .blsToExecutionChanges capella (← decodePoolItems SignedBLSToExecutionChange items)
    else throw (0, "the endpoint of changes of BLS credentials serves only from Capella")
  | "sync_committees" =>
    if altair : .altair ≤ fork then
      return .syncCommitteeMessages altair (← decodePoolItems SyncCommitteeMessage items)
    else throw (0, "the sync committee endpoints serve only from Altair")
  | "payload_attestations" =>
    if gloas : .glamsterdam ≤ fork then
      return .payloadAttestations gloas (← decodePoolItems PayloadAttestationMessage items)
    else throw (0, "the payload attestation endpoint serves only from Gloas")
  | "aggregate_and_proofs" =>
    return .aggregateAndProofs (← decodePoolItems (SignedAggregateAndProof preset fork) items)
  | "contribution_and_proofs" =>
    if altair : .altair ≤ fork then
      let contributions ← decodePoolItems (SignedContributionAndProof preset) items
      return .contributionAndProofs altair contributions
    else throw (0, "the sync committee endpoints serve only from Altair")
  | "proposer_preferences" =>
    if gloas : .glamsterdam ≤ fork then
      return .proposerPreferences gloas (← decodePoolItems SignedProposerPreferences items)
    else throw (0, "the proposer preferences endpoint serves only from Gloas")
  | "execution_payload_bids" =>
    if gloas : .glamsterdam ≤ fork then
      let [bid] := items | throw (0, "the bid endpoint takes one bid")
      return .executionPayloadBid gloas (← decodeInput (SignedExecutionPayloadBid preset fork) bid)
    else throw (0, "the bid endpoint serves only from Gloas")
  | endpoint => throw (0, s!"the pool endpoint {endpoint} is not specified")

/-- A request to a publish endpoint, with its level of checks. -/
inductive PublishRequest (preset : Preset) (fork : Fork) where
  /-- A signed block. -/
  | block (signed : SignedBeaconBlock preset fork)
  /-- From Gloas: a signed envelope. -/
  | envelope (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork)

/-- The level of checks of a request, by its name in the API; none names the gossip level. -/
def broadcastValidationOf : Option String → Result BroadcastValidation
  | none | some "gossip" => return .gossip
  | some "consensus" => return .consensus
  | some "consensus_and_equivocation" => return .consensusAndEquivocation
  | some level => throw (0, s!"the broadcast validation {level} is not specified")

/-- The request of a publish endpoint, if the endpoint is one, from the bytes of its item. -/
def decodePublishInput {preset : Preset} {fork : Fork} (input : PostInput) :
    Result (Option (PublishRequest preset fork)) := do
  match input.endpoint with
  | "blocks" =>
    let [signed] := input.items | throw (0, "the block endpoint takes one block")
    return some (.block (← decodeInput (SignedBeaconBlock preset fork) signed))
  | "execution_payload_envelopes" =>
    if gloas : .glamsterdam ≤ fork then
      let [signed] := input.items | throw (0, "the envelope endpoint takes one envelope")
      let envelope ← decodeInput (SignedExecutionPayloadEnvelope preset fork) signed
      return some (.envelope gloas envelope)
    else throw (0, "the envelope endpoint serves only from Gloas")
  | _ => return none

/-- The events of a request, each as the name of its topic and its JSON data. -/
def eventRecords {preset : Preset} {fork : Fork} (events : List (ObjectEvent preset fork)) :
    Result (List (String × String)) :=
  events.mapM fun event => do
    let event ← runForkChoice ((event.toApiEvent fork).mapError .ssz)
    return (event.topic.name, event.data.compress)

/-- The status code and the failed items of the answer to a pool request. -/
def submitAnswer : SubmitOutcome → Nat × List (Nat × String)
  | .accepted => (200, [])
  | .failed failures => (400, failures)

/-- The status code of the answer to a publish request, and the reason of a refusal at position 0.
-/
def publishAnswer (outcome : PublishOutcome) : Nat × List (Nat × String) :=
  match outcome with
  | .refused reason => (outcome.status, [(0, reason)])
  | _ => (outcome.status, [])

/-- The sources of a node that holds no blobs, samples no columns and accepts every payload. -/
def emptySources {preset : Preset} {fork : Fork} (setup : Cryptography.Kzg.TrustedSetup) :
    BlockSources preset fork where
  engine := .constant true
  powBlock _ := none
  blobsAndProofs _ := some (#[], #[])
  columns _ := some #[]
  setup
  inclusionListSatisfied _ _ := true

/-- Answer the requests to pool and publish endpoints in turn.

The store starts from an anchor and later blocks.

Each answer gives its status code, the position and the message of each item that failed.

It also gives the events of the request. -/
def apiPostOf (args : String × String × ByteArray × ByteArray × List GossipBlockInput ×
    Option (UInt64 × Root) × List PostInput × Option PyValue × Bool) :
    Result (List (Nat × List (Nat × String) × List (String × String))) := do
  let (name, fork, anchorState, anchorBlock, blocks, finalized, inputs, replacements, verify) :=
    args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let (store, statuses) ← gossipCaseStore (preset := preset) (fork := fork) config checks
    anchorState anchorBlock blocks finalized
  let setup ← runForkChoice ((embeddedSetup ()).mapError .kzg)
  let sources := emptySources setup
  -- The execution layer accepts every payload, so no block is optimistic.
  let optimistic : Root → Bool := fun _ => false
  let mut store := store
  let mut statuses := statuses
  let mut seen : Seen := {}
  let mut out := #[]
  for input in inputs do
    -- The clock of the node reaches the time of each request before the node answers it.
    if store.timeMs < input.currentTimeMs then
      store ← runForkChoice (store.onTick config input.currentTimeMs)
    let context : SubmitContext preset fork :=
      { config, checks, setup, store, statuses, currentTimeMs := input.currentTimeMs }
    let publishes := input.endpoint ∈ ["blocks", "execution_payload_envelopes"]
    if !publishes && input.level.isSome then
      throw (0, "a pool endpoint takes no broadcast validation")
    let level ← broadcastValidationOf input.level
    match ← decodePublishInput input with
    | some request =>
      let (outcome, next, after) := match request with
        | .block signed => publishBlock context sources seen level signed
        | .envelope gloas signed => publishEnvelope context sources seen level gloas signed
      let events ← runForkChoice <| Except.mapError .ssz <| match request with
        | .block signed => publishBlockEvents context seen optimistic signed outcome
        | .envelope gloas signed =>
          publishEnvelopeEvents context seen optimistic gloas signed outcome
      let events ← eventRecords events
      -- The execution layer of the node accepts the payload of an integrated object.
      -- From Gloas a block holds no payload, so only its envelope gets a status.
      if outcome == PublishOutcome.integrated then
        let root ← match request with
          | .block signed =>
            if decide (Fork.bellatrix ≤ fork ∧ fork < Fork.glamsterdam) then
              some <$> runForkChoice ((SszType.hashTreeRoot signed.message).mapError .ssz)
            else pure none
          | .envelope _ signed => pure (some signed.message.beaconBlockRoot)
        if let some root := root then statuses := statuses.insert root PAYLOAD_STATUS_VALID
      store := next
      seen := after
      let (status, failures) := publishAnswer outcome
      out := out.push (status, failures, events)
    | none =>
      let request ← decodePoolInput input
      let items := request.items context
      let events ← runForkChoice ((submittedEvents context seen items).mapError .ssz)
      let (outcome, next) := submitList context seen items
      seen := next
      let (status, failures) := submitAnswer outcome
      out := out.push (status, failures, ← eventRecords events)
  return out.toList

/-- Answer the requests to pool and publish endpoints in turn.

The arguments are the names of the preset and the fork, the anchor state and the anchor block.

Then come the later blocks, the finalized checkpoint or none, and the requests.

Then come replacements of values of the configuration, and whether the signature checks run.

Each answer gives its status code, the position and the message of each item that failed.

It also gives the events of the request, each as the name of its topic and its JSON data. -/
@[export eth_consensus_api_post]
def apiPostExport (args : PyValue) : Result PyValue := pyExport apiPostOf args

/-- The event that an object gives if gossip accepts it, by the name of its gossip topic.

It runs no gossip validation, and it is none for a topic without an event. -/
def apiGossipEventOf (args : String × String × String × ByteArray) :
    Result (Option (String × String)) := do
  let (name, fork, topic, data) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let message ← decodeGossipInput (preset := preset) (fork := fork) topic ⟨0, 0, topic, data⟩
  let events ← runForkChoice ((eventsOfGossip .accept message).mapError .ssz)
  return (← eventRecords events).head?

/-- The event that an object gives if gossip accepts it, by the name of its gossip topic.

It runs no gossip validation.

The arguments are the names of the preset and the fork, the topic and the SSZ bytes of the object.

The event is its topic and its JSON data, or none for a topic without an event. -/
@[export eth_consensus_api_gossip_event]
def apiGossipEventExport (args : PyValue) : Result PyValue := pyExport apiGossipEventOf args

end EthLib.Consensus.Exports
