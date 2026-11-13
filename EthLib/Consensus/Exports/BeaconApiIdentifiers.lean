module

public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.Exports.ForkChoice

/-!
# `Exports.BeaconApiIdentifiers`

A C-ABI export that resolves identifiers of the Beacon API against a store of the fork choice.

The store is built as a fork choice case builds it: an anchor state, an anchor block and steps.

A query gives a state or a block identifier as the text of a path.

A validator query gives a validator identifier with the state identifier it is read in.

A text that is no identifier gives its error body as the answer, with code 400.

An answer is tagged, so an error body never reads as a found value.

An identifier that names nothing in the store gives none.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport ToPy FromPy LawfulPy toPy fromPy)

/-- A query of an identifier, as the text of a path. -/
inductive ApiQuery where
  /-- A state identifier. -/
  | state (text : String)
  /-- A block identifier. -/
  | block (text : String)
  /-- A validator identifier in the state that a state identifier names. -/
  | validator (state validator : String)

derive_py ApiQuery
derive_py_laws ApiQuery

/-- What an identifier names in the store.

A state is given by the block that it follows. -/
structure ApiRead where
  /-- The root of the block, or of the block that the state follows. -/
  root : Root
  /-- The slot of the block, or of the state. -/
  slot : UInt64
  /-- Whether the block is the finalized block or one of its ancestors. -/
  finalized : Bool
  /-- The index of the validator, for a validator query. -/
  index : Option UInt64

derive_py ApiRead
derive_py_laws ApiRead

/-- The answer to a query. -/
inductive ApiAnswer where
  /-- What the query names, or none when the store holds nothing that it names. -/
  | found (read : Option ApiRead)
  /-- The error body of a text that names nothing: its code and its message. -/
  | refused (code : UInt32) (message : String)

derive_py ApiAnswer
derive_py_laws ApiAnswer

/-- The answer that a parse gives, or the error body of a text that names nothing. -/
def withParsed {α : Type} (parsed : Except BeaconApi.ErrorMessage α)
    (answer : α → Option ApiRead) : ApiAnswer :=
  match parsed with
  | .ok id => .found (answer id)
  | .error error => .refused error.code.toUInt32 error.message

/-- What a state identifier names, as a read with no validator. -/
def stateRead {preset : Preset} {fork : Fork} (config : Config) (store : Store preset fork)
    (id : BeaconApi.StateId) : Option (ApiRead × BeaconState preset fork) :=
  (BeaconApi.resolveStateId config store id).map fun (root, state) =>
    (⟨root, state.slot, BeaconApi.isFinalizedRoot store root, none⟩, state)

/-- The answer to a query against a store. -/
def answerQuery {preset : Preset} {fork : Fork} (config : Config) (store : Store preset fork) :
    ApiQuery → ApiAnswer
  | .state text => withParsed (BeaconApi.parseStateId text) fun id =>
    (stateRead config store id).map (·.1)
  | .block text => withParsed (BeaconApi.parseBlockId text) fun id =>
    (BeaconApi.resolveBlockId config store id).bind fun root =>
      store.blocks[root]?.map fun block =>
        ⟨root, block.slot, BeaconApi.isFinalizedRoot store root, none⟩
  | .validator stateText validatorText =>
    let ids := do
      return (← BeaconApi.parseStateId stateText, ← BeaconApi.parseValidatorId validatorText)
    withParsed ids fun (stateId, validatorId) =>
      (stateRead config store stateId).bind fun (read, state) =>
        (BeaconApi.resolveValidatorId state validatorId).map fun index =>
          { read with index := some index }

/-- The answer to each query, against the store after the steps of a fork choice case. -/
def apiResolve (args : String × String × ByteArray × ByteArray × List ForkChoiceStep × Bool ×
    List ApiQuery) : Result (List ApiAnswer) := do
  let (name, fork, anchorState, anchorBlock, steps, verify, queries) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let config ← configWithValue name none
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let anchorState ← decodeInput (BeaconState preset fork) anchorState
  let anchorBlock ← decodeInput (BeaconBlock preset fork) anchorBlock
  let (store, _) ← replayForkChoice config checks anchorState anchorBlock steps
  return queries.map (answerQuery config store)

/-- The answer to each query, against the store after the steps of a fork choice case.

The arguments are the preset, the fork, the anchor state and the anchor block in SSZ, and the steps.

Then come whether the signature checks run, and the queries. -/
@[export eth_consensus_api_resolve]
def apiResolveExport (args : PyValue) : Result PyValue := pyExport apiResolve args

end EthLib.Consensus.Exports
