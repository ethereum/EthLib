module

public import EthLib.Consensus.Containers.Execution
public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Serialization.Ssz.Typed.Gindex

/-!
# `Consensus.LightClient.Containers`

From Altair, a light client follows the chain through the signatures of the sync committee.

It keeps a few block headers and the committees that sign, not the state.

A full node sends it a bootstrap, then updates.

Each message proves what it carries against a state root by a Merkle branch.

The bootstrap proves the current committee.

An update proves the next committee and a finalized header.

From Capella, a header also carries the execution payload header, with a branch to the body root.

Electra adds fields to the state, so its tree is one level deeper.

So from Electra the branches into the state are one node longer.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The generalized index of a field of a beacon state at a fork, then of the path below it. -/
def stateGindex (preset : Preset) (fork : Fork) (field : String) (below : List PathStep) :
    Except Err Nat :=
  SszType.getGeneralizedIndex (BeaconState preset fork)
    (.position ((BeaconState.names fork).idxOf field) :: below)

/-- The generalized index of the root of the finalized checkpoint, in the tree of a state. -/
def finalizedRootGindex (fork : Fork) : Nat := if .pectra ≤ fork then 169 else 105

/-- The generalized index of the current sync committee, in the tree of a state. -/
def currentSyncCommitteeGindex (fork : Fork) : Nat := if .pectra ≤ fork then 86 else 54

/-- The generalized index of the next sync committee, in the tree of a state. -/
def nextSyncCommitteeGindex (fork : Fork) : Nat := if .pectra ≤ fork then 87 else 55

/-- From Capella: the generalized index of the execution payload, in the tree of a block body. -/
def EXECUTION_PAYLOAD_GINDEX : Nat := 25

/-- A block header, as a light client sees it.

From Capella it also holds the execution payload header and its branch to the body root. -/
structure LightClientHeader (preset : Preset) (fork : Fork) where
  /-- The header of the beacon block. -/
  beacon : BeaconBlockHeader
  /-- From Capella: the header of the execution payload of the block. -/
  execution : Since .shapella fork (ExecutionPayloadHeader preset fork)
  /-- From Capella: the branch from the execution payload up to the body root. -/
  executionBranch : Since .shapella fork (Vector Bytes32 (Nat.log2 EXECUTION_PAYLOAD_GINDEX))

namespace LightClientHeader

/-- The names of the fields of a header at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["beacon"] ++ sinceNames .shapella fork ["execution", "execution_branch"]

instance {preset : Preset} {fork : Fork} : SszType (LightClientHeader preset fork) :=
  .container (names fork) (fun h => (h.beacon, h.execution, h.executionBranch))
    (fun (beacon, execution, executionBranch) => ⟨beacon, execution, executionBranch⟩)

end LightClientHeader

/-- What a light client needs to start: a trusted header and the committee of its period. -/
structure LightClientBootstrap (preset : Preset) (fork : Fork) where
  /-- The header that the client trusts. -/
  header : LightClientHeader preset fork
  /-- The sync committee of the period of the header. -/
  currentSyncCommittee : SyncCommittee preset
  /-- The branch from the committee up to the state root of the header. -/
  currentSyncCommitteeBranch : Vector Bytes32 (Nat.log2 (currentSyncCommitteeGindex fork))

instance {preset : Preset} {fork : Fork} : SszType (LightClientBootstrap preset fork) :=
  .container ["header", "current_sync_committee", "current_sync_committee_branch"]
    (fun b => (b.header, b.currentSyncCommittee, b.currentSyncCommitteeBranch))
    (fun (header, currentSyncCommittee, currentSyncCommitteeBranch) =>
      ⟨header, currentSyncCommittee, currentSyncCommitteeBranch⟩)

/-- A header signed by the sync committee, with what its state proves.

The state of the attested header proves the next committee and a finalized header.

Either proof may be absent: its fields then hold zeros. -/
structure LightClientUpdate (preset : Preset) (fork : Fork) where
  /-- The header that the sync committee signed. -/
  attestedHeader : LightClientHeader preset fork
  /-- The next sync committee, in the state of the attested header. -/
  nextSyncCommittee : SyncCommittee preset
  /-- The branch from the next committee up to the state root of the attested header. -/
  nextSyncCommitteeBranch : Vector Bytes32 (Nat.log2 (nextSyncCommitteeGindex fork))
  /-- The finalized header, whose root is the finalized root in that state. -/
  finalizedHeader : LightClientHeader preset fork
  /-- The branch from the finalized root up to the state root of the attested header. -/
  finalityBranch : Vector Bytes32 (Nat.log2 (finalizedRootGindex fork))
  /-- The signature of the sync committee on the attested header. -/
  syncAggregate : SyncAggregate preset
  /-- The slot at which the committee signed. -/
  signatureSlot : Slot

instance {preset : Preset} {fork : Fork} : SszType (LightClientUpdate preset fork) :=
  .container ["attested_header", "next_sync_committee", "next_sync_committee_branch",
      "finalized_header", "finality_branch", "sync_aggregate", "signature_slot"]
    (fun u => (u.attestedHeader, u.nextSyncCommittee, u.nextSyncCommitteeBranch,
      u.finalizedHeader, u.finalityBranch, u.syncAggregate, u.signatureSlot))
    (fun (attestedHeader, nextSyncCommittee, nextSyncCommitteeBranch, finalizedHeader,
        finalityBranch, syncAggregate, signatureSlot) =>
      ⟨attestedHeader, nextSyncCommittee, nextSyncCommitteeBranch, finalizedHeader,
        finalityBranch, syncAggregate, signatureSlot⟩)

/-- An update that carries only the finality proof. -/
structure LightClientFinalityUpdate (preset : Preset) (fork : Fork) where
  /-- The header that the sync committee signed. -/
  attestedHeader : LightClientHeader preset fork
  /-- The finalized header, whose root is the finalized root in that state. -/
  finalizedHeader : LightClientHeader preset fork
  /-- The branch from the finalized root up to the state root of the attested header. -/
  finalityBranch : Vector Bytes32 (Nat.log2 (finalizedRootGindex fork))
  /-- The signature of the sync committee on the attested header. -/
  syncAggregate : SyncAggregate preset
  /-- The slot at which the committee signed. -/
  signatureSlot : Slot

instance {preset : Preset} {fork : Fork} : SszType (LightClientFinalityUpdate preset fork) :=
  .container ["attested_header", "finalized_header", "finality_branch", "sync_aggregate",
      "signature_slot"]
    (fun u => (u.attestedHeader, u.finalizedHeader, u.finalityBranch, u.syncAggregate,
      u.signatureSlot))
    (fun (attestedHeader, finalizedHeader, finalityBranch, syncAggregate, signatureSlot) =>
      ⟨attestedHeader, finalizedHeader, finalityBranch, syncAggregate, signatureSlot⟩)

/-- An update that carries only the signed header. -/
structure LightClientOptimisticUpdate (preset : Preset) (fork : Fork) where
  /-- The header that the sync committee signed. -/
  attestedHeader : LightClientHeader preset fork
  /-- The signature of the sync committee on the attested header. -/
  syncAggregate : SyncAggregate preset
  /-- The slot at which the committee signed. -/
  signatureSlot : Slot

instance {preset : Preset} {fork : Fork} : SszType (LightClientOptimisticUpdate preset fork) :=
  .container ["attested_header", "sync_aggregate", "signature_slot"]
    (fun u => (u.attestedHeader, u.syncAggregate, u.signatureSlot))
    (fun (attestedHeader, syncAggregate, signatureSlot) =>
      ⟨attestedHeader, syncAggregate, signatureSlot⟩)

/-- What a light client keeps between updates. -/
structure LightClientStore (preset : Preset) (fork : Fork) where
  /-- The latest header that the client knows to be finalized. -/
  finalizedHeader : LightClientHeader preset fork
  /-- The sync committee of the period of the finalized header. -/
  currentSyncCommittee : SyncCommittee preset
  /-- The sync committee of the next period, or zeros while it is unknown. -/
  nextSyncCommittee : SyncCommittee preset
  /-- The best update seen so far that has not been applied, kept for a forced update. -/
  bestValidUpdate : Option (LightClientUpdate preset fork)
  /-- The latest header that enough of the committee signed. -/
  optimisticHeader : LightClientHeader preset fork
  /-- The most participants in a committee signature in the previous period. -/
  previousMaxActiveParticipants : UInt64
  /-- The most participants in a committee signature in the current period. -/
  currentMaxActiveParticipants : UInt64

end EthLib.Consensus
