module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Containers.Execution
public import EthLib.Consensus.Containers.Operations
public import EthLib.Consensus.Containers.Signing
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.Ssz`

A C-ABI export that reads the bytes of a beacon container, for the static SSZ test vectors.

The container is named as the source names it, at a preset and a fork.

The export decodes the bytes, then returns the root of the value and its bytes encoded again.

A name with no container at the fork comes back as code 0, since no error type covers it.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result)
open Serialization.Ssz.Exports (runSsz)

/-- A container type of the beacon chain, with its SSZ codec. -/
structure Container where
  /-- The Lean type of the container. -/
  type : Type
  /-- Its SSZ codec. -/
  [codec : SszType type]

attribute [instance] Container.codec

/-- The container of a name at a preset and a fork, if the fork has one.

Altair replaces the pending attestations of a state by participation flags.

Capella stops adding historical batches, and adds historical summaries instead. -/
def containerOf (preset : Preset) (fork : Fork) : String → Option Container
  | "Fork" => some ⟨ForkVersions⟩
  | "ForkData" => some ⟨ForkData⟩
  | "SigningData" => some ⟨SigningData⟩
  | "Checkpoint" => some ⟨Checkpoint⟩
  | "Validator" => some ⟨Validator⟩
  | "AttestationData" => some ⟨AttestationData⟩
  | "PendingAttestation" => if fork < .altair then some ⟨PendingAttestation preset⟩ else none
  | "Eth1Data" => some ⟨Eth1Data⟩
  | "HistoricalBatch" => if fork < .shapella then some ⟨HistoricalBatch preset⟩ else none
  | "DepositMessage" => some ⟨DepositMessage⟩
  | "DepositData" => some ⟨DepositData⟩
  | "BeaconBlockHeader" => some ⟨BeaconBlockHeader⟩
  | "SignedBeaconBlockHeader" => some ⟨SignedBeaconBlockHeader⟩
  | "Eth1Block" => some ⟨Eth1Block⟩
  | "ProposerSlashing" => some ⟨ProposerSlashing⟩
  | "Deposit" => some ⟨Deposit⟩
  | "VoluntaryExit" => some ⟨VoluntaryExit⟩
  | "SignedVoluntaryExit" => some ⟨SignedVoluntaryExit⟩
  | "Attestation" => some ⟨Attestation preset fork⟩
  | "IndexedAttestation" => some ⟨IndexedAttestation preset fork⟩
  | "AttesterSlashing" => some ⟨AttesterSlashing preset fork⟩
  | "AggregateAndProof" => some ⟨AggregateAndProof preset fork⟩
  | "SignedAggregateAndProof" => some ⟨SignedAggregateAndProof preset fork⟩
  | "SingleAttestation" => if .pectra ≤ fork then some ⟨SingleAttestation⟩ else none
  | "SyncCommittee" => if .altair ≤ fork then some ⟨SyncCommittee preset⟩ else none
  | "SyncAggregate" => if .altair ≤ fork then some ⟨SyncAggregate preset⟩ else none
  | "SyncCommitteeMessage" => if .altair ≤ fork then some ⟨SyncCommitteeMessage⟩ else none
  | "SyncCommitteeContribution" =>
    if .altair ≤ fork then some ⟨SyncCommitteeContribution preset⟩ else none
  | "ContributionAndProof" =>
    if .altair ≤ fork then some ⟨ContributionAndProof preset⟩ else none
  | "SignedContributionAndProof" =>
    if .altair ≤ fork then some ⟨SignedContributionAndProof preset⟩ else none
  | "SyncAggregatorSelectionData" =>
    if .altair ≤ fork then some ⟨SyncAggregatorSelectionData⟩ else none
  | "HistoricalSummary" => if .shapella ≤ fork then some ⟨HistoricalSummary⟩ else none
  | "BLSToExecutionChange" => if .shapella ≤ fork then some ⟨BLSToExecutionChange⟩ else none
  | "SignedBLSToExecutionChange" =>
    if .shapella ≤ fork then some ⟨SignedBLSToExecutionChange⟩ else none
  | "Withdrawal" => if .shapella ≤ fork then some ⟨Withdrawal⟩ else none
  | "ExecutionPayload" =>
    if .bellatrix ≤ fork then some ⟨ExecutionPayload preset fork⟩ else none
  | _ => none

/-- The root of the value that the bytes encode, then the bytes of that value.

The preset, the fork and the container are named in UTF-8. -/
@[export eth_consensus_ssz_static]
def sszStaticExport (name fork type data : ByteArray) : Result ByteArray := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  let type ← nameOf type
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  let root ← runSsz "root rejected" (SszType.hashTreeRoot value)
  let bytes ← runSsz "value rejected" (SszType.serialize value)
  return ⟨root.toArray⟩ ++ bytes

end EthLib.Consensus.Exports
