module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Containers.BuilderApi
public import EthLib.Consensus.Containers.Builder
public import EthLib.Consensus.Containers.Execution
public import EthLib.Consensus.Containers.InclusionList
public import EthLib.Consensus.Containers.Operations
public import EthLib.Consensus.Containers.PayloadAttestation
public import EthLib.Consensus.Containers.PowBlock
public import EthLib.Consensus.Containers.ProposerPreferences
public import EthLib.Consensus.Containers.Requests
public import EthLib.Consensus.Containers.Signing
public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.LightClient.Containers
public import EthLib.Serialization.Exports.Ssz

/-!
# `Exports.Ssz`

C-ABI exports that read the bytes of a beacon container, for the static SSZ test vectors.

The container is named as the source names it, at a preset and a fork.

The export decodes the bytes, then returns the pair of the root and the bytes encoded again.

The static SSZ and Merkle proof exports take and return typed Python values.

A name with no container at the fork comes back as code 0, since no error type covers it.

From Glamsterdam on, a container whose form EthLib does not hold yet fails with code 0 too.

Another export upgrades an attestation, indexed attestation or attester slashing of Fulu to Gloas.

From Bellatrix to Fulu the names also cover the containers of the Builder API.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- A container type of the beacon chain, with its SSZ codec. -/
structure Container where
  /-- The Lean type of the container. -/
  type : Type
  /-- Its SSZ codec. -/
  [codec : SszType type]

attribute [instance] Container.codec

/-- Whether EthLib holds the light client containers at a fork: from Altair. -/
def lightClientAt (fork : Fork) : Bool := .altair ≤ fork

/-- The container of a name at a preset and a fork, if the fork has one.

Altair replaces the pending attestations of a state by participation flags.

Capella stops adding historical batches, and adds historical summaries instead.

Fulu carries blobs in data column sidecars instead of blob sidecars.

The light client containers start at Altair; EthLib does not yet hold their Gloas form. -/
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
  | "PendingDeposit" => if .pectra ≤ fork then some ⟨PendingDeposit⟩ else none
  | "PendingPartialWithdrawal" => if .pectra ≤ fork then some ⟨PendingPartialWithdrawal⟩ else none
  | "PendingConsolidation" => if .pectra ≤ fork then some ⟨PendingConsolidation⟩ else none
  | "DepositRequest" => if .pectra ≤ fork then some ⟨DepositRequest⟩ else none
  | "WithdrawalRequest" => if .pectra ≤ fork then some ⟨WithdrawalRequest⟩ else none
  | "ConsolidationRequest" => if .pectra ≤ fork then some ⟨ConsolidationRequest⟩ else none
  | "ExecutionRequests" => if .pectra ≤ fork then some ⟨ExecutionRequests preset fork⟩ else none
  | "BeaconBlockBody" => some ⟨BeaconBlockBody preset fork⟩
  | "BeaconBlock" => some ⟨BeaconBlock preset fork⟩
  | "SignedBeaconBlock" => some ⟨SignedBeaconBlock preset fork⟩
  | "BeaconState" => some ⟨BeaconState preset fork⟩
  | "LightClientHeader" =>
    if lightClientAt fork then some ⟨LightClientHeader preset fork⟩ else none
  | "LightClientBootstrap" =>
    if lightClientAt fork then some ⟨LightClientBootstrap preset fork⟩ else none
  | "LightClientUpdate" =>
    if lightClientAt fork then some ⟨LightClientUpdate preset fork⟩ else none
  | "LightClientFinalityUpdate" =>
    if lightClientAt fork then some ⟨LightClientFinalityUpdate preset fork⟩ else none
  | "LightClientOptimisticUpdate" =>
    if lightClientAt fork then some ⟨LightClientOptimisticUpdate preset fork⟩ else none
  | "BlobSidecar" => if .dencun ≤ fork ∧ fork < .fusaka then some ⟨BlobSidecar preset⟩ else none
  | "BlobIdentifier" => if .dencun ≤ fork ∧ fork < .fusaka then some ⟨BlobIdentifier⟩ else none
  | "DataColumnSidecar" =>
    if .fusaka ≤ fork then some ⟨DataColumnSidecar preset fork⟩ else none
  | "DataColumnsByRootIdentifier" =>
    if .fusaka ≤ fork then some ⟨DataColumnsByRootIdentifier preset⟩ else none
  | "MatrixEntry" => if .fusaka ≤ fork then some ⟨MatrixEntry⟩ else none
  | "PartialDataColumnSidecar" =>
    if .fusaka ≤ fork then some ⟨PartialDataColumnSidecar preset fork⟩ else none
  | "PartialDataColumnPartsMetadata" =>
    if .fusaka ≤ fork then some ⟨PartialDataColumnPartsMetadata preset fork⟩ else none
  | "PartialDataColumnHeader" =>
    if .fusaka ≤ fork ∧ fork < .glamsterdam then some ⟨PartialDataColumnHeader preset fork⟩
    else none
  | "PartialDataColumnGroupID" =>
    if .fusaka ≤ fork then some ⟨PartialDataColumnGroupID fork⟩ else none
  | "Withdrawal" => if .shapella ≤ fork then some ⟨Withdrawal⟩ else none
  | "PowBlock" => if .bellatrix ≤ fork then some ⟨PowBlock⟩ else none
  | "ExecutionPayload" =>
    if .bellatrix ≤ fork then some ⟨ExecutionPayload preset fork⟩ else none
  | "ExecutionPayloadHeader" =>
    if .bellatrix ≤ fork ∧ fork < .glamsterdam then some ⟨ExecutionPayloadHeader preset fork⟩
    else none
  | "Builder" => if .glamsterdam ≤ fork then some ⟨Builder⟩ else none
  | "BuilderPendingPayment" => if .glamsterdam ≤ fork then some ⟨BuilderPendingPayment⟩ else none
  | "BuilderPendingWithdrawal" =>
    if .glamsterdam ≤ fork then some ⟨BuilderPendingWithdrawal⟩ else none
  | "BuilderDepositRequest" => if .glamsterdam ≤ fork then some ⟨BuilderDepositRequest⟩ else none
  | "BuilderExitRequest" => if .glamsterdam ≤ fork then some ⟨BuilderExitRequest⟩ else none
  | "PayloadAttestationData" =>
    if .glamsterdam ≤ fork then some ⟨PayloadAttestationData⟩ else none
  | "PayloadAttestationMessage" =>
    if .glamsterdam ≤ fork then some ⟨PayloadAttestationMessage⟩ else none
  | "PayloadAttestation" => if .glamsterdam ≤ fork then some ⟨PayloadAttestation preset⟩ else none
  | "IndexedPayloadAttestation" =>
    if .glamsterdam ≤ fork then some ⟨IndexedPayloadAttestation preset⟩ else none
  | "NewPayloadRequest" =>
    if .bellatrix ≤ fork then some ⟨NewPayloadRequest preset fork⟩ else none
  | "ExecutionPayloadBid" =>
    if .glamsterdam ≤ fork then some ⟨ExecutionPayloadBid preset fork⟩ else none
  | "SignedExecutionPayloadBid" =>
    if .glamsterdam ≤ fork then some ⟨SignedExecutionPayloadBid preset fork⟩ else none
  | "ExecutionPayloadEnvelope" =>
    if .glamsterdam ≤ fork then some ⟨ExecutionPayloadEnvelope preset fork⟩ else none
  | "SignedExecutionPayloadEnvelope" =>
    if .glamsterdam ≤ fork then some ⟨SignedExecutionPayloadEnvelope preset fork⟩ else none
  | "ProposerPreferences" => if .glamsterdam ≤ fork then some ⟨ProposerPreferences⟩ else none
  | "SignedProposerPreferences" =>
    if .glamsterdam ≤ fork then some ⟨SignedProposerPreferences⟩ else none
  | "InclusionList" => if .hegota ≤ fork then some ⟨InclusionList⟩ else none
  | "SignedInclusionList" => if .hegota ≤ fork then some ⟨SignedInclusionList⟩ else none
  | "ValidatorRegistrationV1" =>
    if HasBuilderApi fork then some ⟨ValidatorRegistrationV1⟩ else none
  | "SignedValidatorRegistrationV1" =>
    if HasBuilderApi fork then some ⟨SignedValidatorRegistrationV1⟩ else none
  | "BuilderBid" =>
    if HasBuilderApi fork then some ⟨BuilderBid preset fork⟩ else none
  | "SignedBuilderBid" =>
    if HasBuilderApi fork then some ⟨SignedBuilderBid preset fork⟩ else none
  | "BlindedBeaconBlockBody" =>
    if HasBuilderApi fork then some ⟨BlindedBeaconBlockBody preset fork⟩ else none
  | "BlindedBeaconBlock" =>
    if HasBuilderApi fork then some ⟨BlindedBeaconBlock preset fork⟩ else none
  | "SignedBlindedBeaconBlock" =>
    if HasBuilderApi fork then some ⟨SignedBlindedBeaconBlock preset fork⟩ else none
  | "BuilderRequestAuth" => if .glamsterdam ≤ fork then some ⟨BuilderRequestAuth⟩ else none
  | "SignedBuilderRequestAuth" =>
    if .glamsterdam ≤ fork then some ⟨SignedBuilderRequestAuth⟩ else none
  | "BuilderPreferences" => if .glamsterdam ≤ fork then some ⟨BuilderPreferences⟩ else none
  | "BuilderPreferencesRequest" =>
    if .glamsterdam ≤ fork then some ⟨BuilderPreferencesRequest⟩ else none
  | _ => none

/-- The containers whose form EthLib holds from Glamsterdam on.

Gloas and Heze change some containers, and EthLib holds those forms only as specified. -/
def specifiedFromGlamsterdam : List String := [
  "BuilderRequestAuth", "SignedBuilderRequestAuth", "BuilderPreferences",
  "BuilderPreferencesRequest",
  "Fork", "ForkData", "SigningData", "Checkpoint", "Validator", "AttestationData", "Eth1Data",
  "DepositMessage", "DepositData", "BeaconBlockHeader", "SignedBeaconBlockHeader", "Eth1Block",
  "ProposerSlashing", "Deposit", "VoluntaryExit", "SignedVoluntaryExit", "SingleAttestation",
  "SyncCommittee", "SyncAggregate", "SyncCommitteeMessage", "SyncCommitteeContribution",
  "ContributionAndProof", "SignedContributionAndProof", "SyncAggregatorSelectionData",
  "HistoricalSummary", "BLSToExecutionChange", "SignedBLSToExecutionChange", "PendingDeposit",
  "PendingPartialWithdrawal", "PendingConsolidation", "DepositRequest", "WithdrawalRequest",
  "ConsolidationRequest", "Withdrawal", "PowBlock", "Builder", "BuilderPendingPayment",
  "BuilderPendingWithdrawal", "BuilderDepositRequest", "BuilderExitRequest",
  "PayloadAttestationData", "PayloadAttestationMessage", "ProposerPreferences",
  "SignedProposerPreferences", "InclusionList", "SignedInclusionList",
  "Attestation", "IndexedAttestation", "AttesterSlashing", "AggregateAndProof",
  "SignedAggregateAndProof", "ExecutionPayload", "ExecutionRequests", "NewPayloadRequest",
  "ExecutionPayloadEnvelope", "SignedExecutionPayloadEnvelope", "PayloadAttestation",
  "IndexedPayloadAttestation", "DataColumnSidecar", "DataColumnsByRootIdentifier",
  "MatrixEntry", "PartialDataColumnSidecar", "PartialDataColumnPartsMetadata",
  "PartialDataColumnGroupID", "ExecutionPayloadBid", "SignedExecutionPayloadBid", "BeaconBlockBody",
  "BeaconBlock", "SignedBeaconBlock", "BeaconState", "LightClientHeader", "LightClientBootstrap",
  "LightClientUpdate", "LightClientFinalityUpdate", "LightClientOptimisticUpdate"]

/-- Whether EthLib holds the form of a container at a fork. -/
def specifiedAt (fork : Fork) (type : String) : Bool :=
  fork < .glamsterdam || type ∈ specifiedFromGlamsterdam

/-- The preset and the fork that UTF-8 names name, at a fork up to Fulu. -/
def presetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  if .glamsterdam ≤ fork then throw (0, s!"fork {fork.name} not yet specified")
  return (preset, fork)

/-- The root of the value that the bytes encode, and the bytes of that value. -/
def sszStaticOf (args : String × String × String × ByteArray) : Result (Root × ByteArray) := do
  let (name, fork, type, data) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  if !specifiedAt fork type then
    throw (0, s!"{type} not yet specified at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  let root ← runSsz "root rejected" (SszType.hashTreeRoot value)
  let bytes ← runSsz "value rejected" (SszType.serialize value)
  return (root, bytes)

/-- The root of the value that the bytes encode, and the bytes of that value, as a pair.

The arguments are the name of the preset, the fork, the container and the bytes. -/
@[export eth_consensus_ssz_static]
def sszStaticExport (args : PyValue) : Result PyValue := pyExport sszStaticOf args

/-- The node at a generalized index of the value that the bytes encode, and its branch.

The branch lists the sibling of each node on the path, from the node up to the root. -/
def merkleProofOf (args : String × String × String × ByteArray × UInt64) :
    Result (ByteArray × List ByteArray) := do
  let (name, fork, type, data, gindex) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  if !specifiedAt fork type then
    throw (0, s!"{type} not yet specified at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  let shape := SszType.desc container.type
  let node ← runSsz "node rejected" (nodeRoot shape (SszType.toValue value) gindex.toNat)
  let branch ← runSsz "branch rejected" (buildProof shape (SszType.toValue value) gindex.toNat)
  return (⟨node⟩, branch.map fun sibling => ⟨sibling⟩)

/-- The node at a generalized index of the value that the bytes encode, and its branch, as a pair.

The arguments are the name of the preset, the fork, the container, the bytes and the index.

The branch lists the sibling of each node on the path, from the node up to the root. -/
@[export eth_consensus_merkle_proof]
def merkleProofExport (args : PyValue) : Result PyValue := pyExport merkleProofOf args

/-- The root and the bytes of the upgrade of the value that bytes encode. -/
def upgradeToGloasOf {α β : Type} [SszType α] [SszType β] (upgrade : α → β) (data : ByteArray) :
    Result (Root × ByteArray) := do
  let post := upgrade (← runSsz "input rejected" (SszType.deserialize α data))
  let root ← runSsz "root rejected" (SszType.hashTreeRoot post)
  let bytes ← runSsz "value rejected" (SszType.serialize post)
  return (root, bytes)

/-- The Gloas form of an attestation, indexed attestation or attester slashing of Fulu. -/
def upgradeOperationOf (args : String × String × ByteArray) : Result (Root × ByteArray) := do
  let (name, type, data) := args
  let preset ← presetOf name
  match type with
  | "Attestation" => upgradeToGloasOf (Attestation.upgradeToGloas (preset := preset)) data
  | "IndexedAttestation" =>
    upgradeToGloasOf (IndexedAttestation.upgradeToGloas (preset := preset)) data
  | "AttesterSlashing" =>
    upgradeToGloasOf (AttesterSlashing.upgradeToGloas (preset := preset)) data
  | _ => throw (0, s!"no upgrade of {type} to Gloas")

/-- The root and the bytes of the Gloas form of a container of Fulu, as a pair.

The container is an attestation, an indexed attestation or an attester slashing.

The arguments are the name of the preset, the container and its bytes at Fulu.

The upgrade keeps every field and every element of a list.

From Gloas the lists are progressive, and so are an attestation and its indexed form. -/
@[export eth_consensus_upgrade_operation]
def upgradeOperationExport (args : PyValue) : Result PyValue := pyExport upgradeOperationOf args

/-- Whether the branch of a blob sidecar, given as bytes, climbs to the body root of its header. -/
@[export eth_consensus_verify_blob_sidecar_inclusion_proof]
def verifyBlobSidecarInclusionProofExport (name fork data : ByteArray) : Result Bool := do
  let (preset, fork) ← presetAndFork name fork
  if ¬(.dencun ≤ fork ∧ fork < .fusaka) then throw (0, s!"no container BlobSidecar at {fork.name}")
  let sidecar ← runSsz "input rejected" (SszType.deserialize (BlobSidecar preset) data)
  return verifyBlobSidecarInclusionProof preset fork sidecar

end EthLib.Consensus.Exports
