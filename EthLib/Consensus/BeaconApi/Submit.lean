module

public import EthLib.Consensus.Gossip.Message
public import EthLib.Consensus.HonestValidator

/-!
# `Consensus.BeaconApi.Submit`

What a beacon node answers to a list of objects that a client submits to a pool endpoint.

The node validates each object by the gossip rules of its topic, as if it came from a peer.

So it calls the same dispatch as gossip, on the subnet that the node itself picks.

The source judges each item apart, so a valid item is published even when others fail.

The answer is a success, or it lists the position and a message for each item that fails.

The [attestations endpoint] and the [sync committee endpoint] fix the subnets of an item.

The endpoints of slashings, of [voluntary exits] and of [bids] take one object.

Their answer names at most position 0, and the source sends its message in a plain error body.

SOUNDNESS.md records how this module reads the points that the source leaves open.

[attestations endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/pool/attestations.v2.yaml
[sync committee endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/pool/sync_committees.yaml
[voluntary exits]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/pool/voluntary_exits.yaml
[bids]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/execution_payload/bid.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Networking.Gossip Cryptography.Kzg

variable {preset : Preset} {fork : Fork}

/-- The answer to a submitted list: every item passed, or the items that failed.

Each failure gives the position of its item in the list, and a message. -/
inductive SubmitOutcome where
  /-- Every item passed. -/
  | accepted
  /-- Some items failed, each with its position and a message. -/
  | failed (failures : List (Nat × String))
  deriving DecidableEq, Repr

/-- The position and the message of each item that failed, none for a success. -/
def SubmitOutcome.failures : SubmitOutcome → List (Nat × String)
  | .accepted => []
  | .failed failures => failures

/-- An item of a submission: the gossip messages that publish it, one for each of its subnets.

An empty item publishes nothing and passes, and no endpoint builds one. -/
abbrev SubmitItem (preset : Preset) (fork : Fork) := List (GossipMessage preset fork)

/-- What a node reads to validate an item: the configuration, the checks and the store.

It also reads the KZG setup, the statuses of payloads and the time of the request. -/
structure SubmitContext (preset : Preset) (fork : Fork) where
  /-- The configuration of the chain. -/
  config : Config
  /-- The signature checks. -/
  checks : SignatureChecks
  /-- The KZG setup, for the proofs of a sidecar. -/
  setup : TrustedSetup
  /-- The fork choice store of the node. -/
  store : Store preset fork
  /-- The statuses of the payloads that the execution layer judged. -/
  statuses : PayloadStatuses
  /-- The time of the request, in milliseconds since the Unix epoch. -/
  currentTimeMs : UInt64

/-- The reason of an outcome that ignores or rejects, none for a valid message. -/
def failureReason : ValidationResult → Option String
  | .accept => none
  -- An ignored message fails too, since it is not published.
  | .ignore reason | .reject reason => some reason

/-- The reason that a message fails, if it does, and the messages seen after it. -/
def messageFailure (context : SubmitContext preset fork) (seen : Seen)
    (message : GossipMessage preset fork) : Option String × Seen :=
  -- The gossip validation of the topic of the message, as for a message from a peer.
  match validateGossipMessage context.config context.checks context.setup seen context.store
      context.statuses context.currentTimeMs message with
  | .ok (outcome, after) => (failureReason outcome, after)
  -- An error of the fork choice fails the message, with the keys seen before it.
  --
  -- So it fails only the item of that message, not the others.
  | .error _ => (some "fork choice: the store cannot check it", seen)

/-- The messages of an item in turn: the reason of the first one that fails, if any. -/
def validateItem (context : SubmitContext preset fork) (seen : Seen) :
    SubmitItem preset fork → Option String × Seen
  | [] => (none, seen)
  | message :: rest =>
    -- Every message is validated, and a valid one adds its keys before the next one.
    let (reason, seen) := messageFailure context seen message
    let (later, seen) := validateItem context seen rest
    (reason.or later, seen)

/-- The failures of the items from a position on, in order, and the messages seen after them. -/
def submitFrom (context : SubmitContext preset fork) (position : Nat) (seen : Seen) :
    List (SubmitItem preset fork) → List (Nat × String) × Seen
  | [] => ([], seen)
  | item :: rest =>
    -- The source: each item is processed individually.
    --
    -- EthLib's choice: the items run in order.
    --
    -- The keys of each valid message apply to the later items.
    let (failure, seen) := validateItem context seen item
    let (failures, seen) := submitFrom context (position + 1) seen rest
    -- The source: a failed item gives its index in the request list, and a message.
    ((failure.map (position, ·)).toList ++ failures, seen)

/-- The answer to a submitted list, and the messages seen after it. -/
def submitList (context : SubmitContext preset fork) (seen : Seen)
    (items : List (SubmitItem preset fork)) : SubmitOutcome × Seen :=
  -- The index of an item counts from 0, the first item of the list.
  let (failures, seen) := submitFrom context 0 seen items
  -- The source: code 200 when every item passed, else code 400 with the failed items.
  (if failures.isEmpty then .accepted else .failed failures, seen)

/-! ## Subnets

The node picks the subnet of an item from its head state.

When it finds none, gossip validation fails at or before its check of the subnet.

The node then validates the item on subnet 0. -/

/-- The subnet of the committee of an index, at the slot and the target epoch of a vote. -/
def voteSubnet (context : SubmitContext preset fork) (data : AttestationData)
    (index : CommitteeIndex) : UInt64 :=
  match context.store.headState context.config with
  -- Subnet 0 when the head state cannot be computed.
  | .error _ => 0
  | .ok state =>
    -- The head state gives the number of committees per slot of the target epoch.
    let committees := getCommitteeCountPerSlot state data.target.epoch
    -- The source: the appropriate subnet, that of the committee of the index at the slot.
    --
    -- Subnet 0 when it cannot be computed.
    (computeSubnetForAttestation preset context.config committees data.slot index).toOption.getD 0

/-- From Altair: the subnets of the seats of the validator of a message, once each, in order. -/
def syncSubnets (context : SubmitContext preset fork) (altair : .altair ≤ fork)
    (message : SyncCommitteeMessage) : List UInt64 :=
  match context.store.headState context.config with
  -- Subnet 0 alone when the head state cannot be computed.
  | .error _ => [0]
  | .ok state =>
    -- The source: all applicable subnets, those that hold a seat of the validator, once each.
    match computeSubnetsForSyncCommittee state altair message.validatorIndex with
    | .ok (subnet :: subnets) => subnet :: subnets
    -- Subnet 0 alone when the validator has no seat, or when the subnets cannot be computed.
    | _ => [0]

/-! ## Endpoints -/

/-- A request to a pool endpoint, with the fork from which the endpoint takes it.

Most endpoints take a list, and the endpoints of slashings, exits and bids take one object. -/
inductive PoolRequest (preset : Preset) (fork : Fork) where
  /-- Before Electra: attestations. -/
  | attestations (early : fork < .pectra) (items : List (Attestation preset fork))
  /-- From Electra: single attestations. -/
  | singleAttestations (electra : .pectra ≤ fork) (items : List SingleAttestation)
  /-- One attester slashing. -/
  | attesterSlashing (slashing : AttesterSlashing preset fork)
  /-- One proposer slashing. -/
  | proposerSlashing (slashing : ProposerSlashing)
  /-- One voluntary exit. -/
  | voluntaryExit (signed : SignedVoluntaryExit)
  /-- From Capella: changes of withdrawal credentials. -/
  | blsToExecutionChanges (capella : .shapella ≤ fork) (items : List SignedBLSToExecutionChange)
  /-- From Altair: sync committee messages. -/
  | syncCommitteeMessages (altair : .altair ≤ fork) (items : List SyncCommitteeMessage)
  /-- From Gloas: payload votes. -/
  | payloadAttestations (gloas : .glamsterdam ≤ fork) (items : List PayloadAttestationMessage)
  /-- Aggregates. -/
  | aggregateAndProofs (items : List (SignedAggregateAndProof preset fork))
  /-- From Altair: contributions. -/
  | contributionAndProofs (altair : .altair ≤ fork)
    (items : List (SignedContributionAndProof preset))
  /-- From Gloas: preferences of proposers. -/
  | proposerPreferences (gloas : .glamsterdam ≤ fork) (items : List SignedProposerPreferences)
  /-- From Gloas: one bid of a builder. -/
  | executionPayloadBid (gloas : .glamsterdam ≤ fork) (bid : SignedExecutionPayloadBid preset fork)

/-- The items of a request, each with the messages that publish it. -/
def PoolRequest.items (context : SubmitContext preset fork) :
    PoolRequest preset fork → List (SubmitItem preset fork)
  -- Before Electra: each attestation on the subnet of the committee that its data names.
  | .attestations early items => items.map fun item =>
    [.beaconAttestation early item (voteSubnet context item.data item.data.index)]
  -- From Electra: each single attestation on the subnet of the committee that it names.
  | .singleAttestations electra items => items.map fun item =>
    [.singleAttestation electra item (voteSubnet context item.data item.committeeIndex)]
  -- The endpoints of slashings and of exits take one object: a list of one item.
  | .attesterSlashing slashing => [[.attesterSlashing slashing]]
  | .proposerSlashing slashing => [[.proposerSlashing slashing]]
  | .voluntaryExit signed => [[.voluntaryExit signed]]
  -- Each change of withdrawal credentials is one message, on its topic.
  | .blsToExecutionChanges capella items =>
    items.map fun item => [.blsToExecutionChange capella item]
  -- Each sync committee message on each subnet of the seats of its validator.
  | .syncCommitteeMessages altair items => items.map fun item =>
    (syncSubnets context altair item).map (.syncCommitteeMessage altair item)
  -- Each item of the endpoints below is one message, on the one topic of its kind.
  | .payloadAttestations gloas items =>
    items.map fun item => [.payloadAttestationMessage gloas item]
  | .aggregateAndProofs items => items.map fun item => [.aggregateAndProof item]
  | .contributionAndProofs altair items => items.map fun item => [.contributionAndProof altair item]
  | .proposerPreferences gloas items => items.map fun item => [.proposerPreferences gloas item]
  -- The source lets a node skip the gossip checks of a bid from a locally configured builder.
  --
  -- EthLib knows no such builder, so it always runs them.
  | .executionPayloadBid gloas bid => [[.executionPayloadBid gloas bid]]

/-- The answer of a node to a request to a pool endpoint, and the messages seen after it. -/
def submitPool (context : SubmitContext preset fork) (seen : Seen)
    (request : PoolRequest preset fork) : SubmitOutcome × Seen :=
  -- Each item is validated by the gossip rules of its topic, then the failures are listed.
  submitList context seen (request.items context)

end EthLib.Consensus.BeaconApi
