module

public import EthLib.Base.Exports
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.ReqResp.Messages

/-!
# `Exports.ReqResp`

C-ABI exports of the request and response protocols of the consensus layer.

A list comes back as JSON, and a message as its root and its bytes encoded again.

An unknown name, a fork with no rules yet, or an ID that names no protocol has code 0.

A preset and a configuration are named together, by `mainnet` or `minimal`.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result forkUpTo)
open Serialization.Ssz.Exports (runSsz)

/-- The protocol IDs of a fork, as a JSON list of strings. -/
@[export eth_consensus_reqresp_protocol_ids]
def reqRespProtocolIdsExport (fork : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .bpo5 fork
  let some ids := protocolIds fork | throw (0, s!"fork {fork.name} not yet specified")
  return jsonBytes (toJson (ids.map ProtocolId.toString))

/-- The protocol name and the version that an ID names, as a JSON pair. -/
@[export eth_consensus_reqresp_parse_protocol_id]
def reqRespParseProtocolIdExport (text : ByteArray) : Result ByteArray := do
  let text ← nameOf text
  let some id := ProtocolId.parse? text | throw (0, s!"{text} names no protocol")
  return jsonBytes (toJson (id.protocol.name, id.version))

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
  | _ => none

/-- The root of the message that the bytes encode, then the bytes of that message. -/
@[export eth_consensus_reqresp_message]
def reqRespMessageExport (name fork type data : ByteArray) : Result ByteArray := do
  let name ← nameOf name
  let preset ← presetOf name
  let config ← configOf name
  let fork ← forkUpTo .bpo5 fork
  let type ← nameOf type
  let some message := reqRespMessageOf preset config fork type
    | throw (0, s!"no message {type} at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize message.type data)
  let root ← runSsz "root rejected" (SszType.hashTreeRoot value)
  let bytes ← runSsz "value rejected" (SszType.serialize value)
  return ⟨root.toArray⟩ ++ bytes

/-- The fewest epochs back from the current one over which a node must serve blocks. -/
@[export eth_consensus_compute_min_epochs_for_block_requests]
def computeMinEpochsForBlockRequestsExport (name : ByteArray) : Result UInt64 := do
  return (← configOf (← nameOf name)).computeMinEpochsForBlockRequests

end EthLib.Consensus.Exports
