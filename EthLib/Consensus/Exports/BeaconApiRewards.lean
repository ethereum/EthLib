module

public import EthLib.Consensus.BeaconApi.Rewards
public import EthLib.Consensus.Exports.BeaconApiStateQueries

/-!
# `Exports.BeaconApiRewards`

C-ABI exports of the answers of the Beacon API that split the rewards of validators.

The identifiers are texts as the API writes them, and an empty list names every validator.

The JSON answer is the response without the two flags that come from the store.

An error response of the API has its own code: 400, 404 or 500.

An unknown name or fork, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- The JSON response of the attestation rewards endpoint. -/
def apiAttestationRewardsOf (args : String × String × ByteArray × Option PyValue × UInt64 ×
    List String) : Result PyValue := do
  let (name, fork, state, replacements, epoch, ids) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let ids ← apiError (BeaconApi.readValidatorIds false ids)
  let envelope ← apiError (BeaconApi.attestationRewardsResponse config state epoch ids)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the attestation rewards endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state and replacements or None.

Then come the epoch and the identifiers of the validators. -/
@[export eth_consensus_api_attestation_rewards]
def apiAttestationRewardsExport (args : PyValue) : Result PyValue :=
  pyExport apiAttestationRewardsOf args

/-- The JSON response of the sync committee rewards endpoint. -/
def apiSyncCommitteeRewardsOf (args : String × String × ByteArray × ByteArray × List String) :
    Result PyValue := do
  let (name, fork, state, aggregate, ids) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let aggregate ← decodeInput (SyncAggregate preset) aggregate
  let ids ← apiError (BeaconApi.readValidatorIds false ids)
  let envelope ← apiError (BeaconApi.syncCommitteeRewardsResponse state aggregate ids)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the sync committee rewards endpoint, as a `dict`.

The arguments are the name, the fork, and the SSZ bytes of the state and of the sync aggregate.

The state is the one that the sync aggregate step of the block reads.

Then come the identifiers of the validators. -/
@[export eth_consensus_api_sync_committee_rewards]
def apiSyncCommitteeRewardsExport (args : PyValue) : Result PyValue :=
  pyExport apiSyncCommitteeRewardsOf args

/-- The JSON response of the block rewards endpoint. -/
def apiBlockRewardsOf (args : String × String × ByteArray × ByteArray × Option PyValue) :
    Result PyValue := do
  let (name, fork, state, block, replacements) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let signed ← decodeInput (SignedBeaconBlock preset fork) block
  let envelope ← apiError (BeaconApi.blockRewardsResponse config SignatureChecks.acceptAll
    (.constant true) state signed.message)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the block rewards endpoint, as a `dict`.

The arguments are the name, the fork, and the SSZ bytes of the state and of the signed block.

The state is the one at the slot of the block, before the block.

Then come the replacements of the configuration, or None.

The block was imported, so no signature is checked, and the execution layer accepts its payload. -/
@[export eth_consensus_api_block_rewards]
def apiBlockRewardsExport (args : PyValue) : Result PyValue :=
  pyExport apiBlockRewardsOf args

end EthLib.Consensus.Exports
