module

public import EthLib.Consensus.BeaconApi.Submit
public import EthLib.Consensus.Exports.GossipValidation

/-!
# `Exports.BeaconApiPool`

A C-ABI export that answers lists submitted to the pool endpoints of the Beacon API.

The store of a case is built as for gossip validation, from an anchor and later blocks.

Each request is a tuple of its time in milliseconds, the name of its endpoint and its items.

Each item is the SSZ bytes of one object.

The endpoints of slashings, exits and bids take exactly one.

The requests share the keys of the messages seen, which each valid message extends.

Each request gives the position and the message of each item that failed, or nothing.

An input that the export cannot read fails with code 0.

Such inputs include bytes that do not decode and an endpoint that the fork does not serve.

An error of the fork choice on one item fails that item, with its message.

A request that the export cannot read fails the whole call.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz Networking.Gossip BeaconApi
open EthLib.Exports (Result PyValue FromPy fromPy pyExport)
open Cryptography.Kzg.Exports (embeddedSetup)

/-- A request to a pool endpoint: its time, the name of its endpoint and its items. -/
structure PoolInput where
  /-- The time of the request, in milliseconds since the Unix epoch. -/
  currentTimeMs : UInt64
  /-- The name of the endpoint, the last part of its path. -/
  endpoint : String
  /-- The SSZ bytes of each item. -/
  items : List ByteArray

/-- A request is a tuple of its time, the name of its endpoint and the bytes of its items. -/
instance : FromPy PoolInput := ⟨fun v => do
  match (← v.sequence).toList with
  | [time, endpoint, items] => return ⟨← fromPy time, ← fromPy endpoint, ← fromPy items⟩
  | _ => throw "a request is (time, endpoint, items)"⟩

/-- Decode each item of a request as a value of one SSZ type. -/
def decodePoolItems (α : Type) [SszType α] (items : List ByteArray) : Result (List α) :=
  items.mapM (decodeInput α)

/-- The request of an endpoint, from the bytes of its items.

An endpoint that the fork of the case does not serve fails with code 0. -/
def decodePoolInput {preset : Preset} {fork : Fork} (input : PoolInput) :
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
  | "execution_payload_bid" =>
    if gloas : .glamsterdam ≤ fork then
      let [bid] := items | throw (0, "the bid endpoint takes one bid")
      return .executionPayloadBid gloas (← decodeInput (SignedExecutionPayloadBid preset fork) bid)
    else throw (0, "the bid endpoint serves only from Gloas")
  | endpoint => throw (0, s!"the pool endpoint {endpoint} is not specified")

/-- Answer the requests to pool endpoints in turn, against the store of an anchor and later blocks.

Each answer lists the position and the message of each item that failed. -/
def apiPoolOf (args : String × String × ByteArray × ByteArray × List GossipBlockInput ×
    Option (UInt64 × Root) × List PoolInput × Option PyValue × Bool) :
    Result (List (List (Nat × String))) := do
  let (name, fork, anchorState, anchorBlock, blocks, finalized, inputs, replacements, verify) :=
    args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let (store, statuses) ← gossipCaseStore (preset := preset) (fork := fork) config checks
    anchorState anchorBlock blocks finalized
  let setup ← runForkChoice (embeddedSetup.mapError .kzg)
  let mut seen : Seen := {}
  let mut out := #[]
  for input in inputs do
    let request ← decodePoolInput input
    let context := { config, checks, setup, store, statuses, currentTimeMs := input.currentTimeMs }
    let (outcome, next) := submitPool context seen request
    seen := next
    out := out.push outcome.failures
  return out.toList

/-- Answer the requests to pool endpoints in turn, against the store of an anchor and later blocks.

The arguments are the names of the preset and the fork, the anchor state and the anchor block.

Then come the later blocks, the finalized checkpoint or none, and the requests.

Then come replacements of values of the configuration, and whether the signature checks run.

Each answer lists the position and the message of each item that failed. -/
@[export eth_consensus_api_pool]
def apiPoolExport (args : PyValue) : Result PyValue := pyExport apiPoolOf args

end EthLib.Consensus.Exports
