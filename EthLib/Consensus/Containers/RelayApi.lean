module

public import EthLib.Consensus.ConsensusVersion
public import EthLib.Consensus.Containers.BuilderApi

/-!
# `Consensus.Containers.RelayApi`

The containers of the Relay API with which a builder submits a block, from Bellatrix to Fulu.

A bid trace sums up a submission: its slot, hashes, keys, fee recipient, gas and value.

A submission carries the bid trace, the payload and, from Deneb, the blobs bundle of the payload.

From Electra it also carries the requests of the payload.

The relay specification defines them for [Bellatrix], [Capella], [Deneb], [Electra] and [Fulu].

It restates the payload, the withdrawals, the blobs bundle and the requests; EthLib uses its own.

[Bellatrix]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/specs/bellatrix/builder.md#containers
[Capella]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/specs/capella/builder.md#containers
[Deneb]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/specs/deneb/builder.md#containers
[Electra]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/specs/electra/builder.md#containers
[Fulu]: https://github.com/flashbots/relay-specs/blob/a4e0a50d9d46bfe881fd74cc7e0db366371f4eed/specs/fulu/builder.md#containers
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The public summary of a block that a builder submits to a relay.

It is the same at every fork. -/
structure BidTrace where
  /-- The slot of the block. -/
  slot : Slot
  /-- The hash of the parent of the payload. -/
  parentHash : Hash32
  /-- The hash of the payload. -/
  blockHash : Hash32
  /-- The key of the builder. -/
  builderPubkey : BLSPubkey
  /-- The key of the proposer of the slot. -/
  proposerPubkey : BLSPubkey
  /-- The address of the proposer that receives the payment. -/
  proposerFeeRecipient : ExecutionAddress
  /-- The gas limit of the payload. -/
  gasLimit : UInt64
  /-- The gas that the payload uses. -/
  gasUsed : UInt64
  /-- The value of the payload to the proposer. -/
  value : U256
  deriving DecidableEq

namespace BidTrace

/-- The names of the fields of a bid trace, in their order. -/
def names : List String :=
  ["slot", "parent_hash", "block_hash", "builder_pubkey", "proposer_pubkey",
    "proposer_fee_recipient", "gas_limit", "gas_used", "value"]

instance : SszType BidTrace :=
  .container names
    (fun t => (t.slot, t.parentHash, t.blockHash, t.builderPubkey, t.proposerPubkey,
      t.proposerFeeRecipient, t.gasLimit, t.gasUsed, t.value))
    (fun (slot, parentHash, blockHash, builderPubkey, proposerPubkey, proposerFeeRecipient,
        gasLimit, gasUsed, value) =>
      ⟨slot, parentHash, blockHash, builderPubkey, proposerPubkey, proposerFeeRecipient,
        gasLimit, gasUsed, value⟩)

end BidTrace

/-- A block that a builder submits to a relay, with the builder's signature of its bid trace.

The type exists at every fork, but only Bellatrix to Fulu have submissions. -/
structure SubmitBlockRequest (preset : Preset) (fork : Fork) where
  /-- The bid trace, which the builder signs. -/
  message : BidTrace
  /-- The payload. -/
  executionPayload : ExecutionPayload preset fork
  /-- From Deneb to Fulu: the blobs of the payload, with their commitments and proofs. -/
  blobsBundle : During .dencun .glamsterdam fork (BuilderBlobsBundle preset fork)
  /-- From Electra to Fulu: the requests of the payload. -/
  executionRequests : During .pectra .glamsterdam fork (ExecutionRequests preset fork)
  /-- The signature of the bid trace by the builder. -/
  signature : BLSSignature

namespace SubmitBlockRequest

/-- The names of the fields of a submission at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["message", "execution_payload"] ++ duringNames .dencun .glamsterdam fork ["blobs_bundle"] ++
    duringNames .pectra .glamsterdam fork ["execution_requests"] ++ ["signature"]

instance : SszType (SubmitBlockRequest preset fork) :=
  .container (names fork)
    (fun r => (r.message, r.executionPayload, r.blobsBundle, r.executionRequests, r.signature))
    (fun (message, executionPayload, blobsBundle, executionRequests, signature) =>
      ⟨message, executionPayload, blobsBundle, executionRequests, signature⟩)

end SubmitBlockRequest

/-- A submission inside a container of one field, which the source names after the fork.

The field takes the consensus version of the fork, and the name of the fork where it has none.

The source defines this container but does not say where it is used. -/
structure BuilderSubmitNewBlockRequest (preset : Preset) (fork : Fork) where
  /-- The submission. -/
  request : SubmitBlockRequest preset fork

namespace BuilderSubmitNewBlockRequest

/-- The name of the one field at a fork. -/
def names (fork : Fork) : List String :=
  [(fork.consensusVersion?.map ConsensusVersion.name).getD fork.name]

instance : SszType (BuilderSubmitNewBlockRequest preset fork) :=
  .container (names fork) (fun r => r.request) (fun request => ⟨request⟩)

end BuilderSubmitNewBlockRequest

end EthLib.Consensus
