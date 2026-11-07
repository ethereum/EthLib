module

public import EthLib.Consensus.Exports.HonestProposer
public import EthLib.Consensus.HonestBuilder

/-!
# `Exports.HonestBuilder`

From Gloas: C-ABI exports of the bid and the envelope of an honest builder.

A state, a payload, its requests, the commitments of its blobs and a block come as SSZ bytes.

So do a fee recipient and, from Heze, the bits of the inclusion lists.

The slot, the builder index and the value are 64-bit integers.

The result is the SSZ bytes of the bid, of the signed self-built bid or of the envelope.

The preset and the fork are named in UTF-8, at Gloas or Heze.

An input that does not decode, an unknown name or a fork before Gloas has code 0.

So do bits of inclusion lists before Heze, which must then be empty.

A root that cannot be computed has the code of its SSZ error.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)
open Serialization.Ssz.Exports (runSsz)

/-- From Heze, the bits of the inclusion lists of a bid, from their SSZ bytes.

Before Heze the bytes must be empty. -/
def inclusionListBitsOf {preset : Preset} {fork : Fork} (bits : ByteArray) :
    Result (Since .hegota fork (InclusionListBits preset)) :=
  if heze : .hegota ≤ fork then do
    let bits ← decodeInput (InclusionListBits preset) bits
    return fun _ => bits
  else if bits.isEmpty then return fun later => absurd later heze
  else throw (0, s!"no inclusion list bits at {fork.name}")

/-- From Gloas: the bid of a builder for a payload that it built on a state, as SSZ bytes. -/
@[export eth_consensus_get_execution_payload_bid]
def getExecutionPayloadBidExport
    (name fork state payload requests commitments feeRecipient bits : ByteArray)
    (slot builderIndex value : UInt64) : Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨_⟩ ← holds (.glamsterdam ≤ fork) s!"no execution payload bid at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let payload ← decodeInput (ExecutionPayload preset fork) payload
  let requests ← decodeInput (ExecutionRequests preset fork) requests
  let commitments ← decodeInput (BlobKZGCommitments preset fork) commitments
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let bits ← inclusionListBitsOf bits
  let bid ← runSsz "bid rejected" (getExecutionPayloadBid state payload requests commitments slot
    feeRecipient builderIndex value bits)
  runSsz "bid rejected" (SszType.serialize bid)

/-- From Gloas: the signed bid of a proposer that builds its own payload, as SSZ bytes. -/
@[export eth_consensus_get_self_built_execution_payload_bid]
def getSelfBuiltExecutionPayloadBidExport
    (name fork state payload requests commitments feeRecipient bits : ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨_⟩ ← holds (.glamsterdam ≤ fork) s!"no execution payload bid at {fork.name}"
  let state ← decodeInput (BeaconState preset fork) state
  let payload ← decodeInput (ExecutionPayload preset fork) payload
  let requests ← decodeInput (ExecutionRequests preset fork) requests
  let commitments ← decodeInput (BlobKZGCommitments preset fork) commitments
  let feeRecipient ← decodeInput ExecutionAddress feeRecipient
  let bits ← inclusionListBitsOf bits
  let signed ← runSsz "bid rejected" (getSelfBuiltExecutionPayloadBid state payload requests
    commitments feeRecipient bits)
  runSsz "bid rejected" (SszType.serialize signed)

/-- From Gloas: the envelope that reveals a payload after the block of its bid, as SSZ bytes. -/
@[export eth_consensus_get_execution_payload_envelope]
def getExecutionPayloadEnvelopeExport (name fork block payload requests : ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← transitionPresetAndFork name fork
  let ⟨gloas⟩ ← holds (.glamsterdam ≤ fork) s!"no execution payload envelope at {fork.name}"
  let block ← decodeInput (BeaconBlock preset fork) block
  let payload ← decodeInput (ExecutionPayload preset fork) payload
  let requests ← decodeInput (ExecutionRequests preset fork) requests
  let envelope ← runSsz "envelope rejected"
    (getExecutionPayloadEnvelope block gloas payload requests)
  runSsz "envelope rejected" (SszType.serialize envelope)

end EthLib.Consensus.Exports
