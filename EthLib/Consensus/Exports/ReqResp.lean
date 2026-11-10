module

public import EthLib.Base.Exports
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.ReqResp.Messages
public import EthLib.Consensus.ReqResp.ResponseBounds
public import EthLib.Consensus.ReqResp.Validity

/-!
# `Exports.ReqResp`

C-ABI exports of the request and response protocols of the consensus layer.

The protocol IDs, the parsed ID, the messages and the bounds take and return typed values.

A message comes back as the pair of its root and its bytes encoded again.

An unknown name, a fork with no rules yet, or an ID that names no protocol has code 0.

A protocol that the fork does not define, or one without a request, has the code of its error.

A preset and a configuration are named together, by `mainnet` or `minimal`.

A response check takes the request as SSZ bytes, and each item as the tuple of what the check reads.
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

/-- Decode the SSZ bytes of a request, or fail with code 0. -/
def decodeRequest (α : Type) [SszType α] (data : ByteArray) : Result α :=
  runSsz "request rejected" (SszType.deserialize α data)

/-- Decode each item of a response from its tuple, or fail with code 0. -/
def decodeItems {β : Type} (α : Type) [EthLib.Exports.FromPy α] (make : α → β)
    (items : List PyValue) : Result (List β) :=
  items.mapM fun item => do
    return make (← (EthLib.Exports.FromPy.fromPy item).mapError fun error => (0, error))

/-- Whether a response is valid for its request, under the protocol that an ID names.

The fork is the one in effect when the request is served, and it must define the protocol.

Each item is the tuple of what the check reads, in the order of the fields of its form.

A block is its slot, parent root and root; a sidecar its slot, block root and index.

An envelope is its slot, block root, parent hash and block hash.

An inclusion list is its slot, validator index and dependent root.

The committee is read only for inclusion lists, and must then have one validator per seat.

A protocol without a check of its response, such as status, has code 0. -/
def reqRespResponseValidOf
    (args : String × String × String × ByteArray × List PyValue × List UInt64) :
    Result Bool := do
  let (name, fork, protocol, request, items, committee) := args
  let preset ← presetOf name
  let config ← configOf name
  let fork ← forkUpTo .hegota fork.toUTF8
  let id ← protocolAtFork fork protocol
  let block := decodeItems (Slot × Root × Root) fun (slot, parentRoot, root) =>
    ResponseBlock.mk slot parentRoot root
  let sidecar := decodeItems (Slot × Root × UInt64) fun (slot, blockRoot, index) =>
    ResponseSidecar.mk slot blockRoot index
  let envelope := decodeItems (Slot × Root × Hash32 × Hash32)
    fun (slot, beaconBlockRoot, parentHash, blockHash) =>
      ResponseEnvelope.mk slot beaconBlockRoot parentHash blockHash
  match id.protocol with
  | .beaconBlocksByRange =>
    return isValidBlocksByRangeResponse config fork
      (← decodeRequest BeaconBlocksByRangeRequest request) (← block items)
  | .beaconBlocksByRoot =>
    return isValidBlocksByRootResponse
      (← decodeRequest (BeaconBlocksByRootRequest config fork) request) (← block items)
  | .blobSidecarsByRange =>
    return isValidBlobSidecarsByRangeResponse config fork
      (← decodeRequest BlobSidecarsByRangeRequest request) (← sidecar items)
  | .blobSidecarsByRoot =>
    return isValidBlobSidecarsByRootResponse
      (← decodeRequest (BlobSidecarsByRootRequest config fork) request) (← sidecar items)
  | .dataColumnSidecarsByRange =>
    return isValidDataColumnSidecarsByRangeResponse preset config
      (← decodeRequest (DataColumnSidecarsByRangeRequest preset) request) (← sidecar items)
  | .dataColumnSidecarsByRoot =>
    return isValidDataColumnSidecarsByRootResponse
      (← decodeRequest (DataColumnSidecarsByRootRequest preset config) request)
      (← sidecar items)
  | .executionPayloadEnvelopesByRange =>
    return isValidExecutionPayloadEnvelopesByRangeResponse config fork
      (← decodeRequest ExecutionPayloadEnvelopesByRangeRequest request) (← envelope items)
  | .executionPayloadEnvelopesByRoot =>
    return isValidExecutionPayloadEnvelopesByRootResponse
      (← decodeRequest (ExecutionPayloadEnvelopesByRootRequest config) request)
      (← envelope items)
  | .inclusionListsByIndices =>
    let request ← decodeRequest (InclusionListsByIndicesRequest preset) request
    let seats := preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat
    let committee ← if h : committee.length = seats then
        pure (committee.toArray.toVector.cast (by simpa using h))
      else throw (0, s!"the committee has {committee.length} seats, not {seats}")
    let lists ← decodeItems (Slot × ValidatorIndex × Root)
      (fun (slot, validatorIndex, dependentRoot) =>
        InclusionList.mk slot validatorIndex dependentRoot ⟨#[]⟩) items
    return isValidInclusionListsByIndicesResponse config request committee lists
  | _ => throw (0, s!"{id.toString} has no response check")

/-- Whether a response is valid for its request, as a Boolean.

The arguments are the name of the preset and the configuration, the fork and the protocol ID.

They go on with the request as SSZ bytes, the items of the response and the committee. -/
@[export eth_consensus_reqresp_response_valid]
def reqRespResponseValidExport (args : PyValue) : Result PyValue :=
  pyExport reqRespResponseValidOf args

end EthLib.Consensus.Exports
