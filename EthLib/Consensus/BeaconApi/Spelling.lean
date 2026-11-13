module

public import EthLib.Consensus.BeaconApi.Encoding
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
public import EthLib.Consensus.Containers.RelayApi
public import EthLib.Consensus.Containers.Requests
public import EthLib.Consensus.Containers.Signing
public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.LightClient.Containers

/-!
# `Consensus.BeaconApi.Spelling`

The spelling of each container of the consensus layer in the JSON of the Beacon API.

SSZ gives a byte and a one-byte integer the same type, and so a byte list and a list of them.

The JSON mapping does not.

A container marks each field where the two differ, and every other container marks nothing.

- Before Gloas, participation flags are a byte list, written as one decimal string per byte.
- From Gloas, a transaction and a block access list are lists of one-byte integers, written as hex.
- A container that holds one of these takes the spelling of the field that holds it.

The [`types` files] of the API fix these forms.

Examples are `Transaction` in `primitive.yaml` and `altair/epoch_participation.yaml`.

[`types` files]: https://github.com/ethereum/beacon-APIs/tree/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Serialization.Ssz

/-- The spelling of a container: each named field has its own, and the other fields have none.

A type that is not a container has none. -/
def fieldSpelling (shape : Desc) (marks : List (String × Spelling)) : Spelling :=
  match shape with
  | .container names _ | .progressiveContainer _ names _ =>
    .plain (names.map fun name => (marks.lookup name).getD .opaque)
  | _ => .opaque

namespace ApiSpelling

/-- The spelling that marks nothing: bytes as hex, and integers as decimal strings. -/
@[instance_reducible]
def unmarked {α : Type} : ApiSpelling α := ⟨.opaque⟩

/-- The spelling of a container, from the spelling of each named field. -/
@[instance_reducible]
def ofFields (α : Type) [SszType α] (marks : List (String × Spelling)) : ApiSpelling α :=
  ⟨fieldSpelling (SszType.desc α) marks⟩

end ApiSpelling

/-- A list of transactions: each transaction is written as hex. -/
def transactionsSpelling : Spelling := .plain [.plain [.byte]]

variable {preset : Preset} {fork : Base.Fork}

/-- The participation flags of a state are decimal strings. -/
instance : ApiSpelling (BeaconState preset fork) :=
  .ofFields (BeaconState preset fork)
    [("previous_epoch_participation", .digits), ("current_epoch_participation", .digits)]

/-- The transactions and the block access list of a payload are hex. -/
instance : ApiSpelling (ExecutionPayload preset fork) :=
  .ofFields (ExecutionPayload preset fork)
    [("transactions", transactionsSpelling), ("block_access_list", .plain [.byte])]

/-- Before Gloas, a block body holds a payload. -/
instance : ApiSpelling (BeaconBlockBody preset fork) :=
  .ofFields (BeaconBlockBody preset fork)
    [("execution_payload", ApiSpelling.spelling (ExecutionPayload preset fork))]

/-- A block holds a body. -/
instance : ApiSpelling (BeaconBlock preset fork) :=
  .ofFields (BeaconBlock preset fork) [("body", ApiSpelling.spelling (BeaconBlockBody preset fork))]

/-- A signed block holds a block. -/
instance : ApiSpelling (SignedBeaconBlock preset fork) :=
  .ofFields (SignedBeaconBlock preset fork)
    [("message", ApiSpelling.spelling (BeaconBlock preset fork))]

/-- A request to the execution layer holds a payload. -/
instance : ApiSpelling (NewPayloadRequest preset fork) :=
  .ofFields (NewPayloadRequest preset fork)
    [("execution_payload", ApiSpelling.spelling (ExecutionPayload preset fork))]

/-- From Gloas, an envelope holds a payload. -/
instance : ApiSpelling (ExecutionPayloadEnvelope preset fork) :=
  .ofFields (ExecutionPayloadEnvelope preset fork)
    [("payload", ApiSpelling.spelling (ExecutionPayload preset fork))]

/-- A signed envelope holds an envelope. -/
instance : ApiSpelling (SignedExecutionPayloadEnvelope preset fork) :=
  .ofFields (SignedExecutionPayloadEnvelope preset fork)
    [("message", ApiSpelling.spelling (ExecutionPayloadEnvelope preset fork))]

/-- A payload with its blobs bundle, as the Builder API returns it, holds a payload. -/
instance : ApiSpelling (ExecutionPayloadAndBlobsBundle preset fork) :=
  .ofFields (ExecutionPayloadAndBlobsBundle preset fork)
    [("execution_payload", ApiSpelling.spelling (ExecutionPayload preset fork))]

/-- A submission to a relay holds a payload. -/
instance : ApiSpelling (SubmitBlockRequest preset fork) :=
  .ofFields (SubmitBlockRequest preset fork)
    [("execution_payload", ApiSpelling.spelling (ExecutionPayload preset fork))]

/-- The one field of a wrapped submission holds a submission. -/
instance : ApiSpelling (BuilderSubmitNewBlockRequest preset fork) :=
  .ofFields (BuilderSubmitNewBlockRequest preset fork)
    ((BuilderSubmitNewBlockRequest.names fork).map
      (·, ApiSpelling.spelling (SubmitBlockRequest preset fork)))

/-- From Heze, the transactions of an inclusion list are hex.

The API defines no inclusion list yet, so this follows its form of a transaction. -/
instance : ApiSpelling InclusionList :=
  .ofFields InclusionList [("transactions", transactionsSpelling)]

/-- A signed inclusion list holds a list. -/
instance : ApiSpelling SignedInclusionList :=
  .ofFields SignedInclusionList [("message", ApiSpelling.spelling InclusionList)]

-- No other container holds a field where a byte and a one-byte integer are written differently.
instance : ApiSpelling ForkVersions := .unmarked
instance : ApiSpelling ForkData := .unmarked
instance : ApiSpelling SigningData := .unmarked
instance : ApiSpelling Checkpoint := .unmarked
instance : ApiSpelling Validator := .unmarked
instance : ApiSpelling AttestationData := .unmarked
instance : ApiSpelling (PendingAttestation preset) := .unmarked
instance : ApiSpelling Eth1Data := .unmarked
instance : ApiSpelling (HistoricalBatch preset) := .unmarked
instance : ApiSpelling DepositMessage := .unmarked
instance : ApiSpelling DepositData := .unmarked
instance : ApiSpelling BeaconBlockHeader := .unmarked
instance : ApiSpelling SignedBeaconBlockHeader := .unmarked
instance : ApiSpelling Eth1Block := .unmarked
instance : ApiSpelling ProposerSlashing := .unmarked
instance : ApiSpelling Deposit := .unmarked
instance : ApiSpelling VoluntaryExit := .unmarked
instance : ApiSpelling SignedVoluntaryExit := .unmarked
instance : ApiSpelling (Attestation preset fork) := .unmarked
instance : ApiSpelling (IndexedAttestation preset fork) := .unmarked
instance : ApiSpelling (AttesterSlashing preset fork) := .unmarked
instance : ApiSpelling (AggregateAndProof preset fork) := .unmarked
instance : ApiSpelling (SignedAggregateAndProof preset fork) := .unmarked
instance : ApiSpelling SingleAttestation := .unmarked
instance : ApiSpelling (SyncCommittee preset) := .unmarked
instance : ApiSpelling (SyncAggregate preset) := .unmarked
instance : ApiSpelling SyncCommitteeMessage := .unmarked
instance : ApiSpelling (SyncCommitteeContribution preset) := .unmarked
instance : ApiSpelling (ContributionAndProof preset) := .unmarked
instance : ApiSpelling (SignedContributionAndProof preset) := .unmarked
instance : ApiSpelling SyncAggregatorSelectionData := .unmarked
instance : ApiSpelling HistoricalSummary := .unmarked
instance : ApiSpelling BLSToExecutionChange := .unmarked
instance : ApiSpelling SignedBLSToExecutionChange := .unmarked
instance : ApiSpelling PendingDeposit := .unmarked
instance : ApiSpelling PendingPartialWithdrawal := .unmarked
instance : ApiSpelling PendingConsolidation := .unmarked
instance : ApiSpelling DepositRequest := .unmarked
instance : ApiSpelling WithdrawalRequest := .unmarked
instance : ApiSpelling ConsolidationRequest := .unmarked
instance : ApiSpelling (ExecutionRequests preset fork) := .unmarked
instance : ApiSpelling (LightClientHeader preset fork) := .unmarked
instance : ApiSpelling (LightClientBootstrap preset fork) := .unmarked
instance : ApiSpelling (LightClientUpdate preset fork) := .unmarked
instance : ApiSpelling (LightClientFinalityUpdate preset fork) := .unmarked
instance : ApiSpelling (LightClientOptimisticUpdate preset fork) := .unmarked
instance : ApiSpelling (BlobSidecar preset) := .unmarked
instance : ApiSpelling BlobIdentifier := .unmarked
instance : ApiSpelling (DataColumnSidecar preset fork) := .unmarked
instance : ApiSpelling (DataColumnsByRootIdentifier preset) := .unmarked
instance : ApiSpelling MatrixEntry := .unmarked
instance : ApiSpelling (PartialDataColumnSidecar preset fork) := .unmarked
instance : ApiSpelling (PartialDataColumnPartsMetadata preset fork) := .unmarked
instance : ApiSpelling (PartialDataColumnHeader preset fork) := .unmarked
instance : ApiSpelling (PartialDataColumnGroupID fork) := .unmarked
instance : ApiSpelling Withdrawal := .unmarked
instance : ApiSpelling PowBlock := .unmarked
instance : ApiSpelling (ExecutionPayloadHeader preset fork) := .unmarked
instance : ApiSpelling Builder := .unmarked
instance : ApiSpelling BuilderPendingPayment := .unmarked
instance : ApiSpelling BuilderPendingWithdrawal := .unmarked
instance : ApiSpelling BuilderDepositRequest := .unmarked
instance : ApiSpelling BuilderExitRequest := .unmarked
instance : ApiSpelling PayloadAttestationData := .unmarked
instance : ApiSpelling PayloadAttestationMessage := .unmarked
instance : ApiSpelling (PayloadAttestation preset) := .unmarked
instance : ApiSpelling (IndexedPayloadAttestation preset) := .unmarked
instance : ApiSpelling (ExecutionPayloadBid preset fork) := .unmarked
instance : ApiSpelling (SignedExecutionPayloadBid preset fork) := .unmarked
instance : ApiSpelling ProposerPreferences := .unmarked
instance : ApiSpelling SignedProposerPreferences := .unmarked
instance : ApiSpelling ValidatorRegistrationV1 := .unmarked
instance : ApiSpelling SignedValidatorRegistrationV1 := .unmarked
instance : ApiSpelling (BuilderBid preset fork) := .unmarked
instance : ApiSpelling (SignedBuilderBid preset fork) := .unmarked
instance : ApiSpelling (BlindedBeaconBlockBody preset fork) := .unmarked
instance : ApiSpelling (BlindedBeaconBlock preset fork) := .unmarked
instance : ApiSpelling (SignedBlindedBeaconBlock preset fork) := .unmarked
instance : ApiSpelling (BuilderBlobsBundle preset fork) := .unmarked
instance : ApiSpelling BuilderRequestAuth := .unmarked
instance : ApiSpelling SignedBuilderRequestAuth := .unmarked
instance : ApiSpelling BuilderPreferences := .unmarked
instance : ApiSpelling BuilderPreferencesRequest := .unmarked
instance : ApiSpelling BidTrace := .unmarked

end EthLib.Consensus.BeaconApi
