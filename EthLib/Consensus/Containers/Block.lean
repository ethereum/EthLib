module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Containers.Execution
public import EthLib.Consensus.Containers.Operations
public import EthLib.Consensus.Containers.Requests
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Cryptography.Kzg.Core

/-!
# `Consensus.Containers.Block`

The beacon block, its body and its signed form, at every fork.

The body is one type for every fork, and each fork adds its fields after those of the forks before.

A field that a later fork adds holds nothing at the forks before it, and its codec skips it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Cryptography.Kzg Serialization.Ssz

/-- The body of a beacon block: the operations and data that the proposer includes.

Altair adds the sync aggregate, and Bellatrix the execution payload.

Capella adds the changes of withdrawal credentials.

Deneb adds the commitments to the blobs of [EIP-4844], and Electra the requests of [EIP-7685].

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#consensus-layer-validation
[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#consensus-layer
-/
structure BeaconBlockBody (preset : Preset) (fork : Fork) where
  /-- The proposer's signature of the epoch, which feeds the RANDAO mix. -/
  randaoReveal : BLSSignature
  /-- The proposer's vote on the deposit contract of the execution layer. -/
  eth1Data : Eth1Data
  /-- Free bytes that the proposer chooses. -/
  graffiti : Bytes32
  /-- The proposer slashings. -/
  proposerSlashings : SszList ProposerSlashing preset.MAX_PROPOSER_SLASHINGS.toNat
  /-- The attester slashings. -/
  attesterSlashings :
    SszList (AttesterSlashing preset fork) (parameters preset fork).MAX_ATTESTER_SLASHINGS.toNat
  /-- The attestations. -/
  attestations : SszList (Attestation preset fork) (parameters preset fork).MAX_ATTESTATIONS.toNat
  /-- The deposits. -/
  deposits : SszList Deposit preset.MAX_DEPOSITS.toNat
  /-- The voluntary exits. -/
  voluntaryExits : SszList SignedVoluntaryExit preset.MAX_VOLUNTARY_EXITS.toNat
  /-- From Altair: the signature of the sync committee on the parent block. -/
  syncAggregate : Since .altair fork (SyncAggregate preset)
  /-- From Bellatrix: the execution payload. -/
  executionPayload : Since .bellatrix fork (ExecutionPayload preset fork)
  /-- From Capella: the changes of withdrawal credentials. -/
  blsToExecutionChanges :
    Since .shapella fork
      (SszList SignedBLSToExecutionChange preset.MAX_BLS_TO_EXECUTION_CHANGES.toNat)
  /-- From Deneb: the commitments to the blobs of the block. -/
  blobKzgCommitments :
    Since .dencun fork (SszList KZGCommitment preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat)
  /-- From Electra: the requests of the execution payload. -/
  executionRequests : Since .pectra fork (ExecutionRequests preset)

namespace BeaconBlockBody

/-- The names of the fields of a body at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["randao_reveal", "eth1_data", "graffiti", "proposer_slashings", "attester_slashings",
    "attestations", "deposits", "voluntary_exits"] ++
  sinceNames .altair fork ["sync_aggregate"] ++
  sinceNames .bellatrix fork ["execution_payload"] ++
  sinceNames .shapella fork ["bls_to_execution_changes"] ++
  sinceNames .dencun fork ["blob_kzg_commitments"] ++
  sinceNames .pectra fork ["execution_requests"]

instance {preset : Preset} {fork : Fork} : SszType (BeaconBlockBody preset fork) :=
  .container (names fork)
    (fun b => (b.randaoReveal, b.eth1Data, b.graffiti, b.proposerSlashings, b.attesterSlashings,
      b.attestations, b.deposits, b.voluntaryExits, b.syncAggregate, b.executionPayload,
      b.blsToExecutionChanges, b.blobKzgCommitments, b.executionRequests))
    (fun (randaoReveal, eth1Data, graffiti, proposerSlashings, attesterSlashings, attestations,
        deposits, voluntaryExits, syncAggregate, executionPayload, blsToExecutionChanges,
        blobKzgCommitments, executionRequests) =>
      ⟨randaoReveal, eth1Data, graffiti, proposerSlashings, attesterSlashings, attestations,
        deposits, voluntaryExits, syncAggregate, executionPayload, blsToExecutionChanges,
        blobKzgCommitments, executionRequests⟩)

end BeaconBlockBody

/-- A beacon block: its slot, its proposer, the roots it links to, and its body. -/
structure BeaconBlock (preset : Preset) (fork : Fork) where
  /-- The slot of the block. -/
  slot : Slot
  /-- The validator that proposed the block. -/
  proposerIndex : ValidatorIndex
  /-- The root of the parent block. -/
  parentRoot : Root
  /-- The root of the state after the block. -/
  stateRoot : Root
  /-- The body of the block. -/
  body : BeaconBlockBody preset fork

instance {preset : Preset} {fork : Fork} : SszType (BeaconBlock preset fork) :=
  .container ["slot", "proposer_index", "parent_root", "state_root", "body"]
    (fun b => (b.slot, b.proposerIndex, b.parentRoot, b.stateRoot, b.body))
    (fun (slot, proposerIndex, parentRoot, stateRoot, body) =>
      ⟨slot, proposerIndex, parentRoot, stateRoot, body⟩)

/-- A beacon block with the signature of its proposer. -/
structure SignedBeaconBlock (preset : Preset) (fork : Fork) where
  /-- The block. -/
  message : BeaconBlock preset fork
  /-- The signature of the block by its proposer. -/
  signature : BLSSignature

instance {preset : Preset} {fork : Fork} : SszType (SignedBeaconBlock preset fork) :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

end EthLib.Consensus
