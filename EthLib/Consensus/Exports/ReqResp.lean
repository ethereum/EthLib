module

public import EthLib.Base.Exports
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.ReqResp.Messages
public import EthLib.Consensus.ReqResp.ResponseBounds

/-!
# `Exports.ReqResp`

C-ABI exports of the request and response protocols of the consensus layer.

The protocol IDs, the parsed ID, the messages and the bounds take and return typed values.

A message comes back as the pair of its root and its bytes encoded again.

An unknown name, a fork with no rules yet, or an ID that names no protocol has code 0.

A protocol that the fork does not define, or one without a request, has the code of its error.

A preset and a configuration are named together, by `mainnet` or `minimal`.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport forkUpTo)
open Serialization.Ssz.Exports (runSsz)

/-- The protocol IDs of a fork. -/
def reqRespProtocolIdsOf (fork : String) : Result (List String) := do
  let fork ← forkUpTo .hegota fork.toUTF8
  return (protocolIds fork).map ProtocolId.toString

/-- The protocol IDs of a fork, as a list of strings.

The argument is the name of the fork. -/
@[export eth_consensus_reqresp_protocol_ids]
def reqRespProtocolIdsExport (args : PyValue) : Result PyValue :=
  pyExport reqRespProtocolIdsOf args

/-- The protocol name and the version that an ID names. -/
def reqRespParseProtocolIdOf (text : String) : Result (String × Nat) := do
  let some id := ProtocolId.parse? text | throw (0, s!"{text} names no protocol")
  return (id.protocol.name, id.version)

/-- The protocol name and the version that an ID names, as a pair.

The argument is the protocol ID. -/
@[export eth_consensus_reqresp_parse_protocol_id]
def reqRespParseProtocolIdExport (args : PyValue) : Result PyValue :=
  pyExport reqRespParseProtocolIdOf args

/-- The request and response message of a name at a preset, a configuration and a fork.

A request of a protocol that the fork does not define has no message. -/
def reqRespMessageOf (preset : Preset) (config : Config) (fork : Fork) :
    String → Option Container
  | "Status" => some ⟨Status fork⟩
  | "Goodbye" | "Ping" => some ⟨UInt64⟩
  | "MetaData" => some ⟨MetaData config fork⟩
  | "BeaconBlocksByRangeRequest" => some ⟨BeaconBlocksByRangeRequest⟩
  | "BeaconBlocksByRootRequest" => some ⟨BeaconBlocksByRootRequest config fork⟩
  | "ErrorMessage" => some ⟨ErrorMessage⟩
  | "LightClientUpdatesByRangeRequest" =>
    if .altair ≤ fork then some ⟨LightClientUpdatesByRangeRequest⟩ else none
  | "BlobSidecarsByRangeRequest" =>
    if .dencun ≤ fork then some ⟨BlobSidecarsByRangeRequest⟩ else none
  | "BlobSidecarsByRootRequest" =>
    if .dencun ≤ fork then some ⟨BlobSidecarsByRootRequest config fork⟩ else none
  | "DataColumnSidecarsByRangeRequest" =>
    if .fusaka ≤ fork then some ⟨DataColumnSidecarsByRangeRequest preset⟩ else none
  | "DataColumnSidecarsByRootRequest" =>
    if .fusaka ≤ fork then some ⟨DataColumnSidecarsByRootRequest preset config⟩ else none
  | "BeaconBlocksByHeadRequest" =>
    if .fusaka ≤ fork then some ⟨BeaconBlocksByHeadRequest⟩ else none
  | "ExecutionPayloadEnvelopesByRangeRequest" =>
    if .glamsterdam ≤ fork then some ⟨ExecutionPayloadEnvelopesByRangeRequest⟩ else none
  | "ExecutionPayloadEnvelopesByRootRequest" =>
    if .glamsterdam ≤ fork then some ⟨ExecutionPayloadEnvelopesByRootRequest config⟩ else none
  | "InclusionListsByIndicesRequest" =>
    if .hegota ≤ fork then some ⟨InclusionListsByIndicesRequest preset⟩ else none
  | "SignedInclusionLists" => if .hegota ≤ fork then some ⟨SignedInclusionLists config⟩ else none
  | _ => none

/-- The root of the message that the bytes encode, and the bytes of that message. -/
def reqRespMessageOfBytes (args : String × String × String × ByteArray) :
    Result (Root × ByteArray) := do
  let (name, fork, type, data) := args
  let preset ← presetOf name
  let config ← configOf name
  let fork ← forkUpTo .hegota fork.toUTF8
  let some message := reqRespMessageOf preset config fork type
    | throw (0, s!"no message {type} at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize message.type data)
  let root ← runSsz "root rejected" (SszType.hashTreeRoot value)
  let bytes ← runSsz "value rejected" (SszType.serialize value)
  return (root, bytes)

/-- The root of the message that the bytes encode, and the bytes of that message, as a pair.

The arguments are the name of the preset and the configuration, the fork, the message and its bytes.
-/
@[export eth_consensus_reqresp_message]
def reqRespMessageExport (args : PyValue) : Result PyValue := pyExport reqRespMessageOfBytes args

/-- The fewest epochs back from the current one over which a node must serve blocks, at a fork. -/
def minEpochsForBlockRequestsOf (args : String × String) : Result Nat := do
  let (name, fork) := args
  let config ← configOf name
  let fork ← forkUpTo .hegota fork.toUTF8
  return (config.computeMinEpochsForBlockRequests fork).toNat

/-- The fewest epochs back from the current one over which a node must serve blocks, at a fork.

The arguments are the name of the configuration and the name of the fork. -/
@[export eth_consensus_compute_min_epochs_for_block_requests]
def computeMinEpochsForBlockRequestsExport (args : PyValue) : Result PyValue :=
  pyExport minEpochsForBlockRequestsOf args

/-- A protocol ID that the fork defines, or the code of the error that says it does not. -/
def protocolAtFork (fork : Fork) (text : String) : Result ProtocolId := do
  let some id := ProtocolId.parse? text | throw (0, s!"{text} names no protocol")
  unless (protocolIds fork).contains id do
    throw (BoundsError.notAtFork.code, s!"{text} is not a protocol of {fork.name}")
  return id

/-- The smallest and the largest length of a request payload. -/
def reqRespRequestBoundsOf (args : String × String × String) : Result (Nat × Nat) := do
  let (name, fork, protocol) := args
  let preset ← presetOf name
  let config ← configOf name
  let fork ← forkUpTo .hegota fork.toUTF8
  let id ← protocolAtFork fork protocol
  let some (low, high) := requestBounds preset config fork id
    | throw (BoundsError.noRequest.code, s!"{id.toString} carries no request")
  return (low.toNat, high.toNat)

/-- The smallest and the largest length of a request payload, as a pair.

The arguments are the name of the preset and the configuration, the fork and the protocol ID. -/
@[export eth_consensus_reqresp_request_bounds]
def reqRespRequestBoundsExport (args : PyValue) : Result PyValue :=
  pyExport reqRespRequestBoundsOf args

/-- The smallest and the largest length of the payload of a successful response chunk.

The fork is the one that the context bytes of the chunk name, and it must define the protocol. -/
def reqRespResponseBoundsOf (args : String × String × String) : Result (Nat × Nat) := do
  let (name, chunkFork, protocol) := args
  let preset ← presetOf name
  let config ← configOf name
  let fork ← forkUpTo .hegota chunkFork.toUTF8
  let id ← protocolAtFork fork protocol
  -- Every version that a fork defines has a response type.
  let some (low, high) := responseBounds preset config fork id
    | throw (BoundsError.notAtFork.code, s!"{id.toString} has no response at {fork.name}")
  return (low.toNat, high.toNat)

/-- The smallest and the largest length of the payload of a successful response chunk, as a pair.

The arguments are the name of the preset and the configuration, the fork of the chunk and the ID.

That fork is the one that the context bytes of the chunk name, and it must define the protocol. -/
@[export eth_consensus_reqresp_response_bounds]
def reqRespResponseBoundsExport (args : PyValue) : Result PyValue :=
  pyExport reqRespResponseBoundsOf args

end EthLib.Consensus.Exports
