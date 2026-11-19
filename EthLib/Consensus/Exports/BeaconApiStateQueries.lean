module

public import EthLib.Consensus.BeaconApi.StateQueries
public import EthLib.Consensus.Exports.Transition

/-!
# `Exports.BeaconApiStateQueries`

C-ABI exports of the answers of the Beacon API that read one field of a state.

A query is named as the last segment of the path of its endpoint, such as `finality_checkpoints`.

The JSON answer is the response without the two flags that come from the store.

An error response of the API has its own code, 400 or 500.

An unknown name, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- The query that the last segment of the path of an endpoint names, with an optional epoch.

Only the RANDAO mix takes an epoch. -/
def stateQueryOf (name : String) (epoch : Option UInt64) : Result BeaconApi.StateQuery :=
  match name, epoch with
  | "root", none => pure .root
  | "fork", none => pure .fork
  | "finality_checkpoints", none => pure .finalityCheckpoints
  | "randao", epoch => pure (.randao epoch)
  | "pending_deposits", none => pure .pendingDeposits
  | "pending_partial_withdrawals", none => pure .pendingPartialWithdrawals
  | "pending_consolidations", none => pure .pendingConsolidations
  | "proposer_lookahead", none => pure .proposerLookahead
  | "builder_pending_payments", none => pure .builderPendingPayments
  | "builder_pending_withdrawals", none => pure .builderPendingWithdrawals
  | "root", some _ | "fork", some _ | "finality_checkpoints", some _ | "pending_deposits", some _
  | "pending_partial_withdrawals", some _ | "pending_consolidations", some _
  | "proposer_lookahead", some _ | "builder_pending_payments", some _
  | "builder_pending_withdrawals", some _ => throw (0, s!"the query {name} takes no epoch")
  | _, _ => throw (0, s!"no state query is named {name}")

/-- The error of the API as the error of an export, with its code. -/
def apiError {α : Type} : Except BeaconApi.ErrorMessage α → Result α
  | .ok x => .ok x
  | .error e => .error (e.code.toUInt32, e.message)

/-- The JSON response to a query on a state. -/
def apiStateQueryOf (args : String × String × ByteArray × String × Option UInt64) :
    Result PyValue := do
  let (name, fork, state, query, epoch) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let envelope ← apiError (BeaconApi.stateQuery state (← stateQueryOf query epoch))
  return PyValue.ofJson envelope.toJson

/-- The JSON response to a query on a state, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state, the query, and an epoch or None.

The response has the data, and the version where the endpoint gives one.

A query on a state before the fork that adds its field has code 400. -/
@[export eth_consensus_api_state_query]
def apiStateQueryExport (args : PyValue) : Result PyValue := pyExport apiStateQueryOf args

/-- The SSZ body of the response to a query on a state. -/
def apiStateQuerySszOf (args : String × String × ByteArray × String) : Result ByteArray := do
  let (name, fork, state, query) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let some body := BeaconApi.stateQuerySsz state (← stateQueryOf query none)
    | throw (0, s!"the query {query} has no SSZ body")
  apiError body

/-- The SSZ body of the response to a query on a state, as `bytes`.

The arguments are the name, the fork, the SSZ bytes of the state and the query.

Only the queues, the lookahead and the builder fields have one.

A query on a state before the fork that adds its field has code 400. -/
@[export eth_consensus_api_state_query_ssz]
def apiStateQuerySszExport (args : PyValue) : Result PyValue := pyExport apiStateQuerySszOf args

end EthLib.Consensus.Exports
