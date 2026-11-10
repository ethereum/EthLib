module

public import EthLib.Consensus.Containers.Block

/-!
# `Consensus.Containers.BuilderApi`

From Bellatrix to Fulu: the containers of the Builder API.

A validator registers its fee recipient and its gas limit with builders.

A builder bids on a payload by its header, under its own key.

A blinded block holds that header in place of the payload.

The [builder specification] defines them at Bellatrix.

Its documents for [Capella], [Deneb] and [Electra] extend the bid and the blinded body.

The [Fulu] document changes only the blobs bundle, so Fulu keeps the bid and body of Electra.

[builder specification]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/bellatrix/builder.md#containers
[Capella]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/capella/builder.md#containers
[Deneb]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/deneb/builder.md#containers
[Electra]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/electra/builder.md#containers
[Fulu]: https://github.com/ethereum/builder-specs/blob/fce64468a81a87892d7cb9b4858272bb3d010e50/specs/fulu/builder.md#containers
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Whether a fork has the Builder API of this module: from Bellatrix to Fulu. -/
abbrev HasBuilderApi (fork : Fork) : Prop := .bellatrix ≤ fork ∧ fork < .glamsterdam

/-- The fee recipient and the gas limit that a validator registers with builders. -/
structure ValidatorRegistrationV1 where
  /-- The address that receives the fees of the payload. -/
  feeRecipient : ExecutionAddress
  /-- The gas limit that the payload should have. -/
  gasLimit : UInt64
  /-- The time of the registration, in seconds. -/
  timestamp : UInt64
  /-- The key of the validator. -/
  pubkey : BLSPubkey
  deriving DecidableEq

instance : SszType ValidatorRegistrationV1 :=
  .container ["fee_recipient", "gas_limit", "timestamp", "pubkey"]
    (fun r => (r.feeRecipient, r.gasLimit, r.timestamp, r.pubkey))
    (fun (feeRecipient, gasLimit, timestamp, pubkey) => ⟨feeRecipient, gasLimit, timestamp, pubkey⟩)

/-- A registration with the signature of its validator. -/
structure SignedValidatorRegistrationV1 where
  /-- The registration. -/
  message : ValidatorRegistrationV1
  /-- The signature of the registration by the validator. -/
  signature : BLSSignature
  deriving DecidableEq

instance : SszType SignedValidatorRegistrationV1 :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

/-- The offer of a builder: the header of a payload, its value to the proposer, and its key.

From Deneb it also carries the commitments to the blobs of the payload.

From Electra it also carries the requests of the payload. -/
structure BuilderBid (preset : Preset) (fork : Fork) where
  /-- The header of the payload. -/
  header : ExecutionPayloadHeader preset fork
  /-- From Deneb: the commitments to the blobs of the payload. -/
  blobKzgCommitments : Since .dencun fork (BlobKZGCommitments preset fork)
  /-- From Electra: the requests of the payload. -/
  executionRequests : Since .pectra fork (ExecutionRequests preset fork)
  /-- The value of the payload to the proposer, in wei. -/
  value : U256
  /-- The key of the builder. -/
  pubkey : BLSPubkey

namespace BuilderBid

/-- The names of the fields of a bid at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["header"] ++ sinceNames .dencun fork ["blob_kzg_commitments"] ++
    sinceNames .pectra fork ["execution_requests"] ++ ["value", "pubkey"]

instance : SszType (BuilderBid preset fork) :=
  .container (names fork)
    (fun b => (b.header, b.blobKzgCommitments, b.executionRequests, b.value, b.pubkey))
    (fun (header, blobKzgCommitments, executionRequests, value, pubkey) =>
      ⟨header, blobKzgCommitments, executionRequests, value, pubkey⟩)

end BuilderBid

/-- A bid with the signature of its builder. -/
structure SignedBuilderBid (preset : Preset) (fork : Fork) where
  /-- The bid. -/
  message : BuilderBid preset fork
  /-- The signature of the bid by the builder. -/
  signature : BLSSignature

instance : SszType (SignedBuilderBid preset fork) :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

/-- A beacon block body with the header of its payload in place of the payload.

From Bellatrix to Fulu every other field is that of the body of the same fork.

The type exists at every fork, but only that range has a blinded body.

Its fields follow those of the body, so that blinding copies each field as it is. -/
structure BlindedBeaconBlockBody (preset : Preset) (fork : Fork) where
  /-- The proposer's signature of the epoch, which feeds the RANDAO mix. -/
  randaoReveal : BLSSignature
  /-- Before Heze: the proposer's vote on the deposit contract of the execution layer. -/
  eth1Data : Until .hegota fork Eth1Data
  /-- Free bytes that the proposer chooses. -/
  graffiti : Bytes32
  /-- The proposer slashings. -/
  proposerSlashings : ProposerSlashings preset fork
  /-- The attester slashings. -/
  attesterSlashings : AttesterSlashings preset fork
  /-- The attestations. -/
  attestations : Attestations preset fork
  /-- Before Heze: the deposits. -/
  deposits : Until .hegota fork (Deposits preset fork)
  /-- The voluntary exits. -/
  voluntaryExits : VoluntaryExits preset fork
  /-- From Altair: the signature of the sync committee on the parent block. -/
  syncAggregate : Since .altair fork (SyncAggregate preset)
  /-- From Bellatrix to Fulu: the header of the execution payload. -/
  executionPayloadHeader : During .bellatrix .glamsterdam fork (ExecutionPayloadHeader preset fork)
  /-- From Capella: the changes of withdrawal credentials. -/
  blsToExecutionChanges : Since .shapella fork (BLSToExecutionChanges preset fork)
  /-- From Deneb to Fulu: the commitments to the blobs of the block. -/
  blobKzgCommitments : During .dencun .glamsterdam fork (BlobKZGCommitments preset fork)
  /-- From Electra to Fulu: the requests of the execution payload. -/
  executionRequests : During .pectra .glamsterdam fork (ExecutionRequests preset fork)

namespace BlindedBeaconBlockBody

/-- The names of the fields of a blinded body at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["randao_reveal"] ++ untilNames .hegota fork ["eth1_data"] ++
  ["graffiti", "proposer_slashings", "attester_slashings", "attestations"] ++
  untilNames .hegota fork ["deposits"] ++ ["voluntary_exits"] ++
  sinceNames .altair fork ["sync_aggregate"] ++
  duringNames .bellatrix .glamsterdam fork ["execution_payload_header"] ++
  sinceNames .shapella fork ["bls_to_execution_changes"] ++
  duringNames .dencun .glamsterdam fork ["blob_kzg_commitments"] ++
  duringNames .pectra .glamsterdam fork ["execution_requests"]

instance : SszType (BlindedBeaconBlockBody preset fork) :=
  .container (names fork)
    (fun b => (b.randaoReveal, b.eth1Data, b.graffiti, b.proposerSlashings, b.attesterSlashings,
      b.attestations, b.deposits, b.voluntaryExits, b.syncAggregate, b.executionPayloadHeader,
      b.blsToExecutionChanges, b.blobKzgCommitments, b.executionRequests))
    (fun (randaoReveal, eth1Data, graffiti, proposerSlashings, attesterSlashings, attestations,
        deposits, voluntaryExits, syncAggregate, executionPayloadHeader, blsToExecutionChanges,
        blobKzgCommitments, executionRequests) =>
      ⟨randaoReveal, eth1Data, graffiti, proposerSlashings, attesterSlashings, attestations,
        deposits, voluntaryExits, syncAggregate, executionPayloadHeader, blsToExecutionChanges,
        blobKzgCommitments, executionRequests⟩)

end BlindedBeaconBlockBody

/-- A blinded beacon block: a beacon block whose body holds the header of its payload. -/
structure BlindedBeaconBlock (preset : Preset) (fork : Fork) where
  /-- The slot of the block. -/
  slot : Slot
  /-- The validator that proposed the block. -/
  proposerIndex : ValidatorIndex
  /-- The root of the parent block. -/
  parentRoot : Root
  /-- The root of the state after the block. -/
  stateRoot : Root
  /-- The blinded body of the block. -/
  body : BlindedBeaconBlockBody preset fork

instance : SszType (BlindedBeaconBlock preset fork) :=
  .container ["slot", "proposer_index", "parent_root", "state_root", "body"]
    (fun b => (b.slot, b.proposerIndex, b.parentRoot, b.stateRoot, b.body))
    (fun (slot, proposerIndex, parentRoot, stateRoot, body) =>
      ⟨slot, proposerIndex, parentRoot, stateRoot, body⟩)

/-- A blinded beacon block with the signature of its proposer. -/
structure SignedBlindedBeaconBlock (preset : Preset) (fork : Fork) where
  /-- The blinded block. -/
  message : BlindedBeaconBlock preset fork
  /-- The signature of the block by its proposer. -/
  signature : BLSSignature

instance : SszType (SignedBlindedBeaconBlock preset fork) :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

end EthLib.Consensus
