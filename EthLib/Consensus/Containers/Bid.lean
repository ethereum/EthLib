module

public import EthLib.Consensus.Containers.InclusionList
public import EthLib.Consensus.Containers.Requests
public import EthLib.Cryptography.Kzg.Core
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.Containers.Bid`

From Gloas: the bid of a builder, and the envelope that reveals its execution payload.

A proposer puts the bid of one builder in its block, in place of a payload.

The bid commits to the hash of the payload, to its blobs and to its requests.

The builder later reveals the payload and its requests in a signed envelope.

[EIP-7732] adds these containers; on 2026-11-03 the EIP was in Last Call.

From Heze the bid also says which inclusion lists the builder saw, as [EIP-7805] asks.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#new-containers
[EIP-7805]: https://eips.ethereum.org/EIPS/eip-7805#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Cryptography.Kzg Serialization.Ssz

/-- From Deneb: the commitments to the blobs of a block.

From Gloas the list has no limit in its type, as EIP-7688 specifies. -/
abbrev BlobKZGCommitments (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork KZGCommitment preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat

/-- The offer of a builder to give the payload of a slot for a value.

Heze adds the inclusion lists that the builder saw, as its last field. -/
structure ExecutionPayloadBid (preset : Preset) (fork : Fork) where
  /-- The hash of the parent execution block. -/
  parentBlockHash : Hash32
  /-- The root of the parent beacon block. -/
  parentBlockRoot : Root
  /-- The hash of the execution block that the builder will reveal. -/
  blockHash : Hash32
  /-- The RANDAO mix that the execution block reads. -/
  prevRandao : Bytes32
  /-- The address that receives the priority fees. -/
  feeRecipient : ExecutionAddress
  /-- The gas limit of the execution block. -/
  gasLimit : UInt64
  /-- The builder. -/
  builderIndex : BuilderIndex
  /-- The slot of the bid. -/
  slot : Slot
  /-- The value that the builder pays the proposer on the beacon chain. -/
  value : Gwei
  /-- The value that the builder pays the proposer on the execution layer. -/
  executionPayment : Gwei
  /-- The commitments to the blobs of the payload. -/
  blobKzgCommitments : BlobKZGCommitments preset fork
  /-- The root of the requests of the payload. -/
  executionRequestsRoot : Root
  /-- From Heze: whether the builder saw the list of each member of the inclusion list committee. -/
  inclusionListBits : Since .hegota fork (InclusionListBits preset)

namespace ExecutionPayloadBid

/-- The names of the fields of a bid at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["parent_block_hash", "parent_block_root", "block_hash", "prev_randao", "fee_recipient",
    "gas_limit", "builder_index", "slot", "value", "execution_payment", "blob_kzg_commitments",
    "execution_requests_root"] ++
  sinceNames .hegota fork ["inclusion_list_bits"]

/-- The layout of a bid at a fork: twelve fields, and thirteen from Heze. -/
def activeFields (fork : Fork) : List Bool :=
  List.replicate (if .hegota ≤ fork then 13 else 12) true

instance {preset : Preset} {fork : Fork} : SszType (ExecutionPayloadBid preset fork) :=
  .progressiveContainer (activeFields fork) (names fork)
    (fun b => (b.parentBlockHash, b.parentBlockRoot, b.blockHash, b.prevRandao, b.feeRecipient,
      b.gasLimit, b.builderIndex, b.slot, b.value, b.executionPayment, b.blobKzgCommitments,
      b.executionRequestsRoot, b.inclusionListBits))
    (fun (parentBlockHash, parentBlockRoot, blockHash, prevRandao, feeRecipient, gasLimit,
        builderIndex, slot, value, executionPayment, blobKzgCommitments,
        executionRequestsRoot, inclusionListBits) =>
      ⟨parentBlockHash, parentBlockRoot, blockHash, prevRandao, feeRecipient, gasLimit,
        builderIndex, slot, value, executionPayment, blobKzgCommitments, executionRequestsRoot,
        inclusionListBits⟩)

end ExecutionPayloadBid

/-- A bid with the signature of its builder. -/
structure SignedExecutionPayloadBid (preset : Preset) (fork : Fork) where
  /-- The bid. -/
  message : ExecutionPayloadBid preset fork
  /-- The signature of the bid by the builder. -/
  signature : BLSSignature

instance {preset : Preset} {fork : Fork} : SszType (SignedExecutionPayloadBid preset fork) :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

/-- The payload of a beacon block, with its requests, as its builder reveals them. -/
structure ExecutionPayloadEnvelope (preset : Preset) (fork : Fork) where
  /-- The payload. -/
  payload : ExecutionPayload preset fork
  /-- The requests of the payload. -/
  executionRequests : ExecutionRequests preset fork
  /-- The builder. -/
  builderIndex : BuilderIndex
  /-- The root of the beacon block whose bid the payload fulfils. -/
  beaconBlockRoot : Root
  /-- The root of the parent of that beacon block. -/
  parentBeaconBlockRoot : Root

namespace ExecutionPayloadEnvelope

/-- The names of the fields of an envelope, in their order. -/
def names : List String :=
  ["payload", "execution_requests", "builder_index", "beacon_block_root",
    "parent_beacon_block_root"]

/-- The layout of an envelope, its five fields in their order. -/
def activeFields : List Bool := [true, true, true, true, true]

instance {preset : Preset} {fork : Fork} : SszType (ExecutionPayloadEnvelope preset fork) :=
  .progressiveContainer activeFields names
    (fun e => (e.payload, e.executionRequests, e.builderIndex, e.beaconBlockRoot,
      e.parentBeaconBlockRoot))
    (fun (payload, executionRequests, builderIndex, beaconBlockRoot, parentBeaconBlockRoot) =>
      ⟨payload, executionRequests, builderIndex, beaconBlockRoot, parentBeaconBlockRoot⟩)

end ExecutionPayloadEnvelope

/-- An envelope with the signature of its builder. -/
structure SignedExecutionPayloadEnvelope (preset : Preset) (fork : Fork) where
  /-- The envelope. -/
  message : ExecutionPayloadEnvelope preset fork
  /-- The signature of the envelope by the builder. -/
  signature : BLSSignature

instance {preset : Preset} {fork : Fork} :
    SszType (SignedExecutionPayloadEnvelope preset fork) :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

end EthLib.Consensus
