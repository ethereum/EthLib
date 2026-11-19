module

public import EthLib.Consensus.BeaconApi.ValidatorData
public import EthLib.Consensus.Exports.BeaconApiIdentifiers
public import EthLib.Consensus.Exports.BeaconApiStateQueries

/-!
# `Exports.BeaconApiValidatorData`

C-ABI exports of the answers of the Beacon API that hand a validator the data it signs.

The answers that read the fork choice take the store after the steps of a fork choice case.

The roots of the blocks whose payload is not yet verified are given as a list.

An error response of the API has its own code: 400, 404, 500 or 503.

An unknown name or fork, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- An optimistic store that knows only which roots are not yet verified. -/
def optimisticOf {preset : Preset} {fork : Fork} (roots : List Root) :
    OptimisticStore preset fork :=
  { optimisticRoots := roots, head := default, blocks := ∅ }

/-- The JSON response of the attestation data endpoint. -/
def apiAttestationDataOf (args : StoreCaseArgs (List Root × UInt64 × UInt64)) :
    Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, roots, slot, committeeIndex) := args
  let ⟨_, _, config, store⟩ ← storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  let envelope ← apiError (BeaconApi.attestationDataResponse config store (optimisticOf roots)
    slot committeeIndex)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the attestation data endpoint, as a `dict`.

The first arguments build the store as a fork choice case does.

Then come the roots not yet verified, the slot and the committee index. -/
@[export eth_consensus_api_attestation_data]
def apiAttestationDataExport (args : PyValue) : Result PyValue :=
  pyExport apiAttestationDataOf args

/-- The JSON response of the payload attestation data endpoint, or none for code 204. -/
def apiPayloadAttestationDataOf (args : StoreCaseArgs (UInt64 × Bool × Bool)) :
    Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, slot, present, available) := args
  let ⟨_, _, config, store⟩ ← storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  match ← apiError (BeaconApi.payloadAttestationDataResponse config store slot present available)
  with
  | none => return .none
  | some envelope => return PyValue.ofJson envelope.toJson

/-- The JSON response of the payload attestation data endpoint, as a `dict`, or None for 204.

The first arguments build the store as a fork choice case does.

Then come the slot, and whether the payload and its blob data were seen. -/
@[export eth_consensus_api_payload_attestation_data]
def apiPayloadAttestationDataExport (args : PyValue) : Result PyValue :=
  pyExport apiPayloadAttestationDataOf args

/-- The JSON response of the aggregate endpoint. -/
def apiAggregateAttestationOf (args : String × String × ByteArray × List ByteArray ×
    List ByteArray × List Root × Root × UInt64 × UInt64) : Result PyValue := do
  let (name, fork, state, attestations, singles, roots, dataRoot, slot, committeeIndex) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let attestations ← attestations.mapM (decodeInput (Attestation preset fork))
  let singles ← singles.mapM (decodeInput SingleAttestation)
  let envelope ← apiError (BeaconApi.aggregateAttestationResponse state (optimisticOf roots)
    attestations singles dataRoot slot committeeIndex)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the aggregate endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state and of the collected messages.

The attestations count before Electra, and the single attestations from Electra.

Then come the roots not yet verified, the data root, the slot and the committee index. -/
@[export eth_consensus_api_aggregate_attestation]
def apiAggregateAttestationExport (args : PyValue) : Result PyValue :=
  pyExport apiAggregateAttestationOf args

/-- The JSON response of the contribution endpoint. -/
def apiSyncCommitteeContributionOf (args : String × String × ByteArray × List ByteArray ×
    List Root × UInt64 × UInt64 × Root) : Result PyValue := do
  let (name, fork, state, messages, roots, slot, subcommitteeIndex, root) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let messages ← messages.mapM (decodeInput SyncCommitteeMessage)
  let envelope ← apiError (BeaconApi.syncCommitteeContributionResponse state (optimisticOf roots)
    messages slot subcommitteeIndex root)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the contribution endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state and of the collected messages.

Then come the roots not yet verified, the slot, the subcommittee index and the block root. -/
@[export eth_consensus_api_sync_committee_contribution]
def apiSyncCommitteeContributionExport (args : PyValue) : Result PyValue :=
  pyExport apiSyncCommitteeContributionOf args

end EthLib.Consensus.Exports
