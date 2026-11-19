module

public import EthLib.Consensus.BeaconApi.Debug
public import EthLib.Consensus.Exports.BeaconApiValidatorData

/-!
# `Exports.BeaconApiDebug`

C-ABI exports of the answers of the Beacon API that show the tree of the fork choice.

Each takes the store after the steps of a fork choice case.

The roots of the blocks whose payload is not yet verified are given as a list.

The configuration of the preset may take replacements, as a case with its own configuration does.

A store whose tree cannot be read gives the error with code 500.

An unknown name or fork, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base
open EthLib.Exports (Result PyValue pyExport)

/-- An optimistic store with the blocks of a store and the roots not yet verified. -/
def optimisticWithBlocks {preset : Preset} {fork : Fork} (store : Store preset fork)
    (roots : List Root) : OptimisticStore preset fork :=
  { (optimisticOf roots : OptimisticStore preset fork) with blocks := store.blocks }

/-- The JSON response of the fork choice endpoint. -/
def apiForkChoiceOf (args : StoreCaseArgs (List Root × Option PyValue)) : Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, roots, replacements) := args
  let ⟨_, _, config, store⟩ ←
    storeOfCaseWith (name, fork, anchorState, anchorBlock, steps, verify) replacements
  let envelope ← apiError
    (BeaconApi.forkChoiceResponse config store (optimisticWithBlocks store roots))
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the fork choice endpoint, as a `dict`.

The first arguments build the store as a fork choice case does.

Then come the roots not yet verified, and replacements of the configuration or None. -/
@[export eth_consensus_api_fork_choice]
def apiForkChoiceExport (args : PyValue) : Result PyValue := pyExport apiForkChoiceOf args

/-- The JSON response of the heads endpoint. -/
def apiChainHeadsOf (args : StoreCaseArgs (List Root × Option PyValue)) : Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, roots, replacements) := args
  let ⟨_, _, _, store⟩ ←
    storeOfCaseWith (name, fork, anchorState, anchorBlock, steps, verify) replacements
  let envelope ← apiError
    (BeaconApi.chainHeadsResponse store (optimisticWithBlocks store roots))
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the heads endpoint, as a `dict`.

The first arguments build the store as a fork choice case does.

Then come the roots not yet verified, and replacements of the configuration or None. -/
@[export eth_consensus_api_chain_heads]
def apiChainHeadsExport (args : PyValue) : Result PyValue := pyExport apiChainHeadsOf args

end EthLib.Consensus.Exports
