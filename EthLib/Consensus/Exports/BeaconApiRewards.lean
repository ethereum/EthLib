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

end EthLib.Consensus.Exports
