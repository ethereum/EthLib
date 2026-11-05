module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Containers.Execution
public import EthLib.Consensus.Containers.Operations
public import EthLib.Consensus.Containers.PayloadAttestation
public import EthLib.Consensus.Containers.Requests
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Cryptography.Kzg.Core

/-!
# `Consensus.Containers.Block`

The beacon block, its body and its signed form, at every fork.

The body is one type for every fork, and each fork adds its fields after those of the forks before.

A field that a later fork adds holds nothing at the forks before it, and its codec skips it.

So does a field that a later fork removes, from that fork on.

From Gloas the body is a progressive container, and its lists have no limit in their type.

[EIP-7688] makes that change.

A progressive container keeps a gap where a later fork removes a field.

So the fields that remain keep their places in the tree, and their proofs stay valid.

[EIP-7688]: https://eips.ethereum.org/EIPS/eip-7688#converted-types
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Cryptography.Kzg Serialization.Ssz

/-- The proposer slashings of a block. -/
abbrev ProposerSlashings (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork ProposerSlashing preset.MAX_PROPOSER_SLASHINGS.toNat

/-- The attester slashings of a block. -/
abbrev AttesterSlashings (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork (AttesterSlashing preset fork)
    (parameters preset fork).MAX_ATTESTER_SLASHINGS.toNat

/-- The attestations of a block. -/
abbrev Attestations (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork (Attestation preset fork)
    (parameters preset fork).MAX_ATTESTATIONS.toNat

/-- The deposits of a block. -/
abbrev Deposits (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork Deposit preset.MAX_DEPOSITS.toNat

/-- The voluntary exits of a block. -/
abbrev VoluntaryExits (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork SignedVoluntaryExit preset.MAX_VOLUNTARY_EXITS.toNat

/-- From Capella: the changes of withdrawal credentials of a block. -/
abbrev BLSToExecutionChanges (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork SignedBLSToExecutionChange
    preset.MAX_BLS_TO_EXECUTION_CHANGES.toNat

/-- The body of a beacon block: the operations and data that the proposer includes.

Altair adds the sync aggregate, and Bellatrix the execution payload.

Capella adds the changes of withdrawal credentials.

Deneb adds the commitments to the blobs of [EIP-4844], and Electra the requests of [EIP-7685].

Gloas moves the payload, the commitments and the requests to the envelope of the builder.

In their place it adds the bid of the builder, the payload votes and the parent's requests.

[EIP-7732] specifies these changes.

Heze removes the vote on the deposit contract and the deposits, as [EIP-8015] asks.

On 2026-11-03 EIP-8015 was a Draft that EIP-8081 only considers for Hegotá.

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#consensus-layer-validation
[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#consensus-layer
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#modified-containers
[EIP-8015]: https://eips.ethereum.org/EIPS/eip-8015#beaconblockbody-modifications
-/
structure BeaconBlockBody (preset : Preset) (fork : Fork) where
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
  /-- From Bellatrix to Fulu: the execution payload. -/
  executionPayload : During .bellatrix .glamsterdam fork (ExecutionPayload preset fork)
  /-- From Capella: the changes of withdrawal credentials. -/
  blsToExecutionChanges : Since .shapella fork (BLSToExecutionChanges preset fork)
  /-- From Deneb to Fulu: the commitments to the blobs of the block. -/
  blobKzgCommitments : During .dencun .glamsterdam fork (BlobKZGCommitments preset fork)
  /-- From Electra to Fulu: the requests of the execution payload. -/
  executionRequests : During .pectra .glamsterdam fork (ExecutionRequests preset fork)
  /-- From Gloas: the bid of the builder whose payload the block takes. -/
  signedExecutionPayloadBid : Since .glamsterdam fork (SignedExecutionPayloadBid preset fork)
  /-- From Gloas: the payload votes on the parent block. -/
  payloadAttestations : Since .glamsterdam fork (PayloadAttestations preset)
  /-- From Gloas: the requests of the payload of the parent block. -/
  parentExecutionRequests : Since .glamsterdam fork (ExecutionRequests preset fork)

namespace BeaconBlockBody

/-- The names of the fields of a body at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["randao_reveal"] ++ untilNames .hegota fork ["eth1_data"] ++
  ["graffiti", "proposer_slashings", "attester_slashings", "attestations"] ++
  untilNames .hegota fork ["deposits"] ++ ["voluntary_exits"] ++
  sinceNames .altair fork ["sync_aggregate"] ++
  duringNames .bellatrix .glamsterdam fork ["execution_payload"] ++
  sinceNames .shapella fork ["bls_to_execution_changes"] ++
  duringNames .dencun .glamsterdam fork ["blob_kzg_commitments"] ++
  duringNames .pectra .glamsterdam fork ["execution_requests"] ++
  sinceNames .glamsterdam fork
    ["signed_execution_payload_bid", "payload_attestations", "parent_execution_requests"]

/-- From Gloas: the layout of a body, thirteen places in their order.

From Heze the places of the vote on the deposit contract and of the deposits stay empty. -/
def activeFields (fork : Fork) : List Bool :=
  if .hegota ≤ fork then
    [true, false, true, true, true, true, false, true, true, true, true, true, true]
  else List.replicate 13 true

instance {preset : Preset} {fork : Fork} : SszType (BeaconBlockBody preset fork) :=
  .forkContainer .glamsterdam fork (activeFields fork) (names fork)
    (fun b => (b.randaoReveal, b.eth1Data, b.graffiti, b.proposerSlashings, b.attesterSlashings,
      b.attestations, b.deposits, b.voluntaryExits, b.syncAggregate, b.executionPayload,
      b.blsToExecutionChanges, b.blobKzgCommitments, b.executionRequests,
      b.signedExecutionPayloadBid, b.payloadAttestations, b.parentExecutionRequests))
    (fun (randaoReveal, eth1Data, graffiti, proposerSlashings, attesterSlashings, attestations,
        deposits, voluntaryExits, syncAggregate, executionPayload, blsToExecutionChanges,
        blobKzgCommitments, executionRequests, signedExecutionPayloadBid, payloadAttestations,
        parentExecutionRequests) =>
      ⟨randaoReveal, eth1Data, graffiti, proposerSlashings, attesterSlashings, attestations,
        deposits, voluntaryExits, syncAggregate, executionPayload, blsToExecutionChanges,
        blobKzgCommitments, executionRequests, signedExecutionPayloadBid, payloadAttestations,
        parentExecutionRequests⟩)

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
