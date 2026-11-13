module

public import EthLib.Consensus.BeaconApi.Registries
public import EthLib.Consensus.Exports.BeaconApiStateQueries

/-!
# `Exports.BeaconApiRegistries`

C-ABI exports of the answers of the Beacon API that read the registries of a state.

A query is named as the last segment of the path of its endpoint, such as `validator_balances`.

The query `validator` is the endpoint for one validator, and takes exactly one identifier.

The identifiers and the statuses are texts as the API writes them, and a missing list is empty.

Only the validators and builders queries take statuses.

Only the validators and balances queries take their identifiers in a query string.

The JSON answer is the response without the two flags that come from the store.

An error response of the API has its own code: 400, 404, 414 or 500.

An unknown name, query or fork, or an input that does not decode, has code 0.

So has an argument that the query does not take, or a wrong count of identifiers for one validator.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- The error of an argument that a query does not take, with code 0. -/
def refuseArgument {α : Type} (query argument : String) : Result α :=
  throw (0, s!"the query {query} takes no {argument}")

/-- The response to a query on the registries of a state, from the texts of the request. -/
def registryQuery {preset : Preset} {fork : Fork} (state : BeaconState preset fork)
    (query : String) (ids statuses : List String) (inQuery : Bool) :
    Result BeaconApi.ApiEnvelope := do
  match query with
  | "validators" =>
    let ids ← apiError (BeaconApi.readValidatorIds inQuery ids)
    let filter ← apiError (BeaconApi.readStatusFilter statuses)
    apiError (BeaconApi.validatorsResponse state ids filter)
  | "validator" =>
    if !statuses.isEmpty then refuseArgument query "statuses"
    else if inQuery then refuseArgument query "query string"
    else
      let [text] := ids | throw (0, "the query validator takes exactly one identifier")
      let id ← apiError (BeaconApi.parseValidatorId text)
      let entry ← apiError (BeaconApi.stateValidator state id)
      let data ← apiError (entry.toJson.mapError fun fault =>
        BeaconApi.internalError (reprStr fault))
      return { data }
  | "validator_balances" =>
    if !statuses.isEmpty then refuseArgument query "statuses"
    else
      let ids ← apiError (BeaconApi.readValidatorIds inQuery ids)
      apiError (BeaconApi.balancesResponse state ids)
  | "validator_identities" =>
    if !statuses.isEmpty then refuseArgument query "statuses"
    else if inQuery then refuseArgument query "query string"
    else
      let ids ← apiError (BeaconApi.readValidatorIds false ids)
      apiError (BeaconApi.identitiesResponse state ids)
  | "builders" =>
    if inQuery then refuseArgument query "query string"
    -- A state before Gloas gets its error before the identifiers and statuses are read.
    else if .glamsterdam ≤ fork then
      let ids ← apiError (BeaconApi.readBuilderIds ids)
      let filter ← apiError (statuses.mapM BeaconApi.BuilderStatus.parse)
      apiError (BeaconApi.buildersResponse state ids filter)
    else apiError (BeaconApi.buildersResponse state [] [])
  | _ => throw (0, s!"no registry query is named {query}")

/-- The JSON response to a query on the registries of a state. -/
def apiRegistryQueryOf
    (args : String × String × ByteArray × String × Option (List String) ×
      Option (List String) × Bool) : Result PyValue := do
  let (name, fork, state, query, ids, statuses, inQuery) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let envelope ← registryQuery state query (ids.getD []) (statuses.getD []) inQuery
  return PyValue.ofJson envelope.toJson

/-- The JSON response to a query on the registries of a state, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state and the query.

Then come the identifiers, the statuses, and whether the identifiers come in a query string.

The queries are the validators, one validator, the balances, the identities and the builders. -/
@[export eth_consensus_api_registry_query]
def apiRegistryQueryExport (args : PyValue) : Result PyValue := pyExport apiRegistryQueryOf args

/-- The SSZ body of the balances answer. -/
def apiValidatorBalancesSszOf
    (args : String × String × ByteArray × Option (List String) × Bool) : Result ByteArray := do
  let (name, fork, state, ids, inQuery) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let ids ← apiError (BeaconApi.readValidatorIds inQuery (ids.getD []))
  apiError (BeaconApi.balancesSsz state ids)

/-- The SSZ body of the balances answer, as `bytes`.

The arguments are the name, the fork, the SSZ bytes of the state and the identifiers.

The last argument says whether the identifiers come in a query string. -/
@[export eth_consensus_api_validator_balances_ssz]
def apiValidatorBalancesSszExport (args : PyValue) : Result PyValue :=
  pyExport apiValidatorBalancesSszOf args

end EthLib.Consensus.Exports
