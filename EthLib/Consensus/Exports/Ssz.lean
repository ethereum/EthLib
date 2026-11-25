module

public import EthLib.Consensus.BeaconApi.Spelling
public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Containers.BuilderApi
public import EthLib.Consensus.Containers.BuilderConfig
public import EthLib.Consensus.Containers.Builder
public import EthLib.Consensus.Containers.Execution
public import EthLib.Consensus.Containers.InclusionList
public import EthLib.Consensus.Containers.Operations
public import EthLib.Consensus.Containers.PayloadAttestation
public import EthLib.Consensus.Containers.PowBlock
public import EthLib.Consensus.Containers.ProposerPreferences
public import EthLib.Consensus.Containers.RelayApi
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

The static SSZ and Merkle proof exports take and return typed Python values.

Another export upgrades an attestation, indexed attestation or attester slashing of Fulu to Gloas.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport rejectArgument toResult)

/-- A container type of the beacon chain, with its SSZ codec. -/
structure Container where
  /-- The Lean type of the container. -/
  type : Type
  /-- Its SSZ codec. -/
  [codec : SszType type]

attribute [instance] Container.codec

/-- A container of the beacon chain, with its SSZ codec and its spelling in the Beacon API.

Each container must declare its spelling, so none falls back to a default. -/
structure BeaconContainer where
  /-- The Lean type of the container. -/
  type : Type
  /-- Its SSZ codec. -/
  [codec : SszType type]
  /-- How the Beacon API writes it in JSON. -/
  [spelling : BeaconApi.ApiSpelling type]

attribute [instance] BeaconContainer.codec BeaconContainer.spelling

/-- Whether EthLib holds the light client containers at a fork: from Altair. -/
def lightClientAt (fork : Fork) : Bool := .altair ≤ fork

/-- The container of a name at a preset and a fork, if the fork has one. -/
def containerOf (preset : Preset) (fork : Fork) (name : String) : Option BeaconContainer :=
  -- The compiler lifts out of a match each instance built only from the function's arguments.
  --
  -- Each arm binds the preset and the fork it reads, so a lookup builds only what it returns.
  match name, preset, fork with
  | "Fork", _, _ => some ⟨ForkVersions⟩
  | "ForkData", _, _ => some ⟨ForkData⟩
  | "SigningData", _, _ => some ⟨SigningData⟩
  | "Checkpoint", _, _ => some ⟨Checkpoint⟩
  | "Validator", _, _ => some ⟨Validator⟩
  | "AttestationData", _, _ => some ⟨AttestationData⟩
  -- Altair replaces the pending attestations of a state by participation flags.
  | "PendingAttestation", preset, fork =>
    if fork < .altair then some ⟨PendingAttestation preset⟩ else none
  | "Eth1Data", _, _ => some ⟨Eth1Data⟩
  -- Capella stops adding historical batches, and adds historical summaries instead.
  | "HistoricalBatch", preset, fork =>
    if fork < .shapella then some ⟨HistoricalBatch preset⟩ else none
  | "DepositMessage", _, _ => some ⟨DepositMessage⟩
  | "DepositData", _, _ => some ⟨DepositData⟩
  | "BeaconBlockHeader", _, _ => some ⟨BeaconBlockHeader⟩
  | "SignedBeaconBlockHeader", _, _ => some ⟨SignedBeaconBlockHeader⟩
  | "Eth1Block", _, _ => some ⟨Eth1Block⟩
  | "ProposerSlashing", _, _ => some ⟨ProposerSlashing⟩
  | "Deposit", _, _ => some ⟨Deposit⟩
  | "VoluntaryExit", _, _ => some ⟨VoluntaryExit⟩
  | "SignedVoluntaryExit", _, _ => some ⟨SignedVoluntaryExit⟩
  | "Attestation", preset, fork => some ⟨Attestation preset fork⟩
  | "IndexedAttestation", preset, fork => some ⟨IndexedAttestation preset fork⟩
  | "AttesterSlashing", preset, fork => some ⟨AttesterSlashing preset fork⟩
  | "AggregateAndProof", preset, fork => some ⟨AggregateAndProof preset fork⟩
  | "SignedAggregateAndProof", preset, fork => some ⟨SignedAggregateAndProof preset fork⟩
  | "SingleAttestation", _, fork => if .pectra ≤ fork then some ⟨SingleAttestation⟩ else none
  | "SyncCommittee", preset, fork => if .altair ≤ fork then some ⟨SyncCommittee preset⟩ else none
  | "SyncAggregate", preset, fork => if .altair ≤ fork then some ⟨SyncAggregate preset⟩ else none
  | "SyncCommitteeMessage", _, fork => if .altair ≤ fork then some ⟨SyncCommitteeMessage⟩ else none
  | "SyncCommitteeContribution", preset, fork =>
    if .altair ≤ fork then some ⟨SyncCommitteeContribution preset⟩ else none
  | "ContributionAndProof", preset, fork =>
    if .altair ≤ fork then some ⟨ContributionAndProof preset⟩ else none
  | "SignedContributionAndProof", preset, fork =>
    if .altair ≤ fork then some ⟨SignedContributionAndProof preset⟩ else none
  | "SyncAggregatorSelectionData", _, fork =>
    if .altair ≤ fork then some ⟨SyncAggregatorSelectionData⟩ else none
  | "HistoricalSummary", _, fork => if .shapella ≤ fork then some ⟨HistoricalSummary⟩ else none
  | "BLSToExecutionChange", _, fork =>
    if .shapella ≤ fork then some ⟨BLSToExecutionChange⟩ else none
  | "SignedBLSToExecutionChange", _, fork =>
    if .shapella ≤ fork then some ⟨SignedBLSToExecutionChange⟩ else none
  | "PendingDeposit", _, fork => if .pectra ≤ fork then some ⟨PendingDeposit⟩ else none
  | "PendingPartialWithdrawal", _, fork =>
    if .pectra ≤ fork then some ⟨PendingPartialWithdrawal⟩ else none
  | "PendingConsolidation", _, fork => if .pectra ≤ fork then some ⟨PendingConsolidation⟩ else none
  | "DepositRequest", _, fork => if .pectra ≤ fork then some ⟨DepositRequest⟩ else none
  | "WithdrawalRequest", _, fork => if .pectra ≤ fork then some ⟨WithdrawalRequest⟩ else none
  | "ConsolidationRequest", _, fork => if .pectra ≤ fork then some ⟨ConsolidationRequest⟩ else none
  | "ExecutionRequests", preset, fork =>
    if .pectra ≤ fork then some ⟨ExecutionRequests preset fork⟩ else none
  | "BeaconBlockBody", preset, fork => some ⟨BeaconBlockBody preset fork⟩
  | "BeaconBlock", preset, fork => some ⟨BeaconBlock preset fork⟩
  | "SignedBeaconBlock", preset, fork => some ⟨SignedBeaconBlock preset fork⟩
  | "BeaconState", preset, fork => some ⟨BeaconState preset fork⟩
  -- The light client containers start at Altair.
  --
  -- EthLib does not yet hold their Gloas form.
  | "LightClientHeader", preset, fork =>
    if lightClientAt fork then some ⟨LightClientHeader preset fork⟩ else none
  | "LightClientBootstrap", preset, fork =>
    if lightClientAt fork then some ⟨LightClientBootstrap preset fork⟩ else none
  | "LightClientUpdate", preset, fork =>
    if lightClientAt fork then some ⟨LightClientUpdate preset fork⟩ else none
  | "LightClientFinalityUpdate", preset, fork =>
    if lightClientAt fork then some ⟨LightClientFinalityUpdate preset fork⟩ else none
  | "LightClientOptimisticUpdate", preset, fork =>
    if lightClientAt fork then some ⟨LightClientOptimisticUpdate preset fork⟩ else none
  -- Fulu carries blobs in data column sidecars instead of blob sidecars.
  | "BlobSidecar", preset, fork =>
    if .dencun ≤ fork ∧ fork < .fusaka then some ⟨BlobSidecar preset⟩ else none
  | "BlobIdentifier", _, fork =>
    if .dencun ≤ fork ∧ fork < .fusaka then some ⟨BlobIdentifier⟩ else none
  | "DataColumnSidecar", preset, fork =>
    if .fusaka ≤ fork then some ⟨DataColumnSidecar preset fork⟩ else none
  | "DataColumnsByRootIdentifier", preset, fork =>
    if .fusaka ≤ fork then some ⟨DataColumnsByRootIdentifier preset⟩ else none
  | "MatrixEntry", _, fork => if .fusaka ≤ fork then some ⟨MatrixEntry⟩ else none
  | "PartialDataColumnSidecar", preset, fork =>
    if .fusaka ≤ fork then some ⟨PartialDataColumnSidecar preset fork⟩ else none
  | "PartialDataColumnPartsMetadata", preset, fork =>
    if .fusaka ≤ fork then some ⟨PartialDataColumnPartsMetadata preset fork⟩ else none
  | "PartialDataColumnHeader", preset, fork =>
    if .fusaka ≤ fork ∧ fork < .glamsterdam then some ⟨PartialDataColumnHeader preset fork⟩
    else none
  | "PartialDataColumnGroupID", _, fork =>
    if .fusaka ≤ fork then some ⟨PartialDataColumnGroupID fork⟩ else none
  | "Withdrawal", _, fork => if .shapella ≤ fork then some ⟨Withdrawal⟩ else none
  | "PowBlock", _, fork => if .bellatrix ≤ fork then some ⟨PowBlock⟩ else none
  | "ExecutionPayload", preset, fork =>
    if .bellatrix ≤ fork then some ⟨ExecutionPayload preset fork⟩ else none
  | "ExecutionPayloadHeader", preset, fork =>
    if .bellatrix ≤ fork ∧ fork < .glamsterdam then some ⟨ExecutionPayloadHeader preset fork⟩
    else none
  | "Builder", _, fork => if .glamsterdam ≤ fork then some ⟨Builder⟩ else none
  | "BuilderPendingPayment", _, fork =>
    if .glamsterdam ≤ fork then some ⟨BuilderPendingPayment⟩ else none
  | "BuilderPendingWithdrawal", _, fork =>
    if .glamsterdam ≤ fork then some ⟨BuilderPendingWithdrawal⟩ else none
  | "BuilderDepositRequest", _, fork =>
    if .glamsterdam ≤ fork then some ⟨BuilderDepositRequest⟩ else none
  | "BuilderExitRequest", _, fork => if .glamsterdam ≤ fork then some ⟨BuilderExitRequest⟩ else none
  | "PayloadAttestationData", _, fork =>
    if .glamsterdam ≤ fork then some ⟨PayloadAttestationData⟩ else none
  | "PayloadAttestationMessage", _, fork =>
    if .glamsterdam ≤ fork then some ⟨PayloadAttestationMessage⟩ else none
  | "PayloadAttestation", preset, fork =>
    if .glamsterdam ≤ fork then some ⟨PayloadAttestation preset⟩ else none
  | "IndexedPayloadAttestation", preset, fork =>
    if .glamsterdam ≤ fork then some ⟨IndexedPayloadAttestation preset⟩ else none
  | "NewPayloadRequest", preset, fork =>
    if .bellatrix ≤ fork then some ⟨NewPayloadRequest preset fork⟩ else none
  | "ExecutionPayloadBid", preset, fork =>
    if .glamsterdam ≤ fork then some ⟨ExecutionPayloadBid preset fork⟩ else none
  | "SignedExecutionPayloadBid", preset, fork =>
    if .glamsterdam ≤ fork then some ⟨SignedExecutionPayloadBid preset fork⟩ else none
  | "ExecutionPayloadEnvelope", preset, fork =>
    if .glamsterdam ≤ fork then some ⟨ExecutionPayloadEnvelope preset fork⟩ else none
  | "SignedExecutionPayloadEnvelope", preset, fork =>
    if .glamsterdam ≤ fork then some ⟨SignedExecutionPayloadEnvelope preset fork⟩ else none
  | "ProposerPreferences", _, fork =>
    if .glamsterdam ≤ fork then some ⟨ProposerPreferences⟩ else none
  | "SignedProposerPreferences", _, fork =>
    if .glamsterdam ≤ fork then some ⟨SignedProposerPreferences⟩ else none
  | "InclusionList", _, fork => if .hegota ≤ fork then some ⟨InclusionList⟩ else none
  | "SignedInclusionList", _, fork => if .hegota ≤ fork then some ⟨SignedInclusionList⟩ else none
  -- From Bellatrix to Fulu the names also cover the containers of the Builder and Relay APIs.
  | "ValidatorRegistrationV1", _, fork =>
    if HasBuilderApi fork then some ⟨ValidatorRegistrationV1⟩ else none
  | "SignedValidatorRegistrationV1", _, fork =>
    if HasBuilderApi fork then some ⟨SignedValidatorRegistrationV1⟩ else none
  | "BuilderBid", preset, fork =>
    if HasBuilderApi fork then some ⟨BuilderBid preset fork⟩ else none
  | "SignedBuilderBid", preset, fork =>
    if HasBuilderApi fork then some ⟨SignedBuilderBid preset fork⟩ else none
  | "BlindedBeaconBlockBody", preset, fork =>
    if HasBuilderApi fork then some ⟨BlindedBeaconBlockBody preset fork⟩ else none
  | "BlindedBeaconBlock", preset, fork =>
    if HasBuilderApi fork then some ⟨BlindedBeaconBlock preset fork⟩ else none
  | "SignedBlindedBeaconBlock", preset, fork =>
    if HasBuilderApi fork then some ⟨SignedBlindedBeaconBlock preset fork⟩ else none
  | "BlobsBundle", preset, fork =>
    if .dencun ≤ fork ∧ fork < .glamsterdam then some ⟨BuilderBlobsBundle preset fork⟩ else none
  | "ExecutionPayloadAndBlobsBundle", preset, fork =>
    if .dencun ≤ fork ∧ fork < .glamsterdam then some ⟨ExecutionPayloadAndBlobsBundle preset fork⟩
    else none
  | "BuilderRequestAuth", _, fork => if .glamsterdam ≤ fork then some ⟨BuilderRequestAuth⟩ else none
  | "SignedBuilderRequestAuth", _, fork =>
    if .glamsterdam ≤ fork then some ⟨SignedBuilderRequestAuth⟩ else none
  | "BuilderPreferences", _, fork => if .glamsterdam ≤ fork then some ⟨BuilderPreferences⟩ else none
  | "BuilderPreferencesRequest", _, fork =>
    if .glamsterdam ≤ fork then some ⟨BuilderPreferencesRequest⟩ else none
  | "BuilderEntry", _, fork => if .glamsterdam ≤ fork then some ⟨BuilderEntry⟩ else none
  | "BuilderConfig", _, fork => if .glamsterdam ≤ fork then some ⟨BuilderConfig⟩ else none
  | "BidTrace", _, fork => if HasBuilderApi fork then some ⟨BidTrace⟩ else none
  | "SubmitBlockRequest", preset, fork =>
    if HasBuilderApi fork then some ⟨SubmitBlockRequest preset fork⟩ else none
  | "BuilderSubmitNewBlockRequest", preset, fork =>
    if HasBuilderApi fork then some ⟨BuilderSubmitNewBlockRequest preset fork⟩ else none
  | _, _, _ => none

/-- The containers whose form EthLib holds from Glamsterdam on.

Gloas and Heze change some containers, and EthLib holds those forms only as specified. -/
def specifiedFromGlamsterdam : List String := [
  "BuilderRequestAuth", "SignedBuilderRequestAuth", "BuilderPreferences",
  "BuilderPreferencesRequest", "BuilderEntry", "BuilderConfig",
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
  if .glamsterdam ≤ fork then rejectArgument none s!"fork {fork.name} not yet specified"
  return (preset, fork)

/-- The root of the value that the bytes encode, and the bytes of that value. -/
def sszStaticOf (args : String × String × String × ByteArray) : Result (Root × ByteArray) := do
  let (name, fork, type, data) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  -- A name with no container at the fork comes back as code 0, since no error type covers it.
  let some container := containerOf preset fork type
    | rejectArgument none s!"no container {type} at {fork.name}"
  -- From Glamsterdam on, a container whose form EthLib does not hold yet fails with code 0 too.
  if !specifiedAt fork type then
    rejectArgument none s!"{type} not yet specified at {fork.name}"
  -- Decode the bytes, then return the pair of the root and the bytes encoded again.
  let value ← toResult "input rejected" (SszType.deserialize container.type data)
  let root ← toResult "root rejected" (SszType.hashTreeRoot value)
  let bytes ← toResult "value rejected" (SszType.serialize value)
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
  -- A name with no container at the fork comes back as code 0, since no error type covers it.
  let some container := containerOf preset fork type
    | rejectArgument none s!"no container {type} at {fork.name}"
  -- From Glamsterdam on, a container whose form EthLib does not hold yet fails with code 0 too.
  if !specifiedAt fork type then
    rejectArgument none s!"{type} not yet specified at {fork.name}"
  let value ← toResult "input rejected" (SszType.deserialize container.type data)
  let shape := SszType.desc container.type
  let node ← toResult "node rejected" (nodeRoot shape (SszType.toValue value) gindex.toNat)
  let branch ← toResult "branch rejected" (buildProof shape (SszType.toValue value) gindex.toNat)
  return (⟨node⟩, branch.map fun sibling => ⟨sibling⟩)

/-- The node at a generalized index of the value that the bytes encode, and its branch, as a pair.

The arguments are the name of the preset, the fork, the container, the bytes and the index.

The branch lists the sibling of each node on the path, from the node up to the root. -/
@[export eth_consensus_merkle_proof]
def merkleProofExport (args : PyValue) : Result PyValue := pyExport merkleProofOf args

/-- The root and the bytes of the upgrade of the value that bytes encode. -/
def upgradeToGloasOf {α β : Type} [SszType α] [SszType β] (upgrade : α → β) (data : ByteArray) :
    Result (Root × ByteArray) := do
  let post := upgrade (← toResult "input rejected" (SszType.deserialize α data))
  let root ← toResult "root rejected" (SszType.hashTreeRoot post)
  let bytes ← toResult "value rejected" (SszType.serialize post)
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
  | _ => rejectArgument none s!"no upgrade of {type} to Gloas"

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
  if ¬(.dencun ≤ fork ∧ fork < .fusaka) then
    rejectArgument none s!"no container BlobSidecar at {fork.name}"
  let sidecar ← toResult "input rejected" (SszType.deserialize (BlobSidecar preset) data)
  return verifyBlobSidecarInclusionProof preset fork sidecar

end EthLib.Consensus.Exports
