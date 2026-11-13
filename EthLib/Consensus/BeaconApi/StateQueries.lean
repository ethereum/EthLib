module

public import EthLib.Consensus.Accessors
public import EthLib.Consensus.BeaconApi.Spelling

/-!
# `Consensus.BeaconApi.StateQueries`

The answers of the Beacon API that read one field of a state.

The [states endpoints] fix each answer, one file per endpoint.

A field that a fork adds gives an error with code 400 for a state before that fork.

The flags `execution_optimistic` and `finalized` come from the store, not from the state.

SOUNDNESS.md records the points that the source leaves open.

[states endpoints]: https://github.com/ethereum/beacon-APIs/tree/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/states
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The three checkpoints of a state that finality depends on. -/
structure FinalityCheckpoints where
  /-- The justified checkpoint of the previous epoch. -/
  previousJustified : Checkpoint
  /-- The justified checkpoint of the current epoch. -/
  currentJustified : Checkpoint
  /-- The finalized checkpoint. -/
  finalized : Checkpoint
  deriving DecidableEq, Repr

instance : SszType FinalityCheckpoints :=
  .container ["previous_justified", "current_justified", "finalized"]
    (fun c => (c.previousJustified, c.currentJustified, c.finalized))
    (fun (previousJustified, currentJustified, finalized) =>
      ⟨previousJustified, currentJustified, finalized⟩)

instance : ApiSpelling FinalityCheckpoints := .unmarked
instance : ApiSpelling (PendingDeposits preset fork) := .unmarked
instance : ApiSpelling (PendingPartialWithdrawals preset fork) := .unmarked
instance : ApiSpelling (PendingConsolidations preset fork) := .unmarked
instance : ApiSpelling (Vector ValidatorIndex
    ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)) := .unmarked
instance : ApiSpelling (BuilderPendingPayments preset) := .unmarked
instance : ApiSpelling BuilderPendingWithdrawals := .unmarked

/-- The root of a state: its hash tree root. -/
def stateRoot (state : BeaconState preset fork) : Except Err Root :=
  SszType.hashTreeRoot state

/-- The fork of a state: its previous and current versions, and the epoch of the current one. -/
def stateFork (state : BeaconState preset fork) : ForkVersions :=
  state.forkVersions

/-- The finality checkpoints of a state. -/
def finalityCheckpoints (state : BeaconState preset fork) : FinalityCheckpoints :=
  { previousJustified := state.previousJustifiedCheckpoint
    currentJustified := state.currentJustifiedCheckpoint
    finalized := state.finalizedCheckpoint }

/-- The RANDAO mix of a state for an epoch, or for its current epoch when none is given.

The mix is read in the circular buffer of the state, and no epoch is refused.

The source has an error with code 400 for an epoch out of range, but names no range.

The read fails only for a buffer of length 0. -/
def stateRandao (state : BeaconState preset fork) (epoch : Option Epoch) :
    Except AccessorError Bytes32 :=
  getRandaoMix state (epoch.getD (getCurrentEpoch state))

/-- The error of a query on a state before the fork that adds its field, with code 400.

The message names the fork by its consensus version, or by its own name without one. -/
def beforeFork (query : String) (first : Fork) : ErrorMessage :=
  let name := (first.consensusVersion?.map (·.name)).getD first.name
  { code := 400, message := s!"{query} is not in a state before {name}" }

/-- A field that a fork adds, or the error with code 400 for a state before that fork. -/
def sinceFork {α : Type} (query : String) (first : Fork) (field : Since first fork α) :
    Except ErrorMessage α :=
  if since : first ≤ fork then .ok (field since) else .error (beforeFork query first)

/-- The deposits that wait in a state, from Electra. -/
def pendingDeposits (state : BeaconState preset fork) :
    Except ErrorMessage (PendingDeposits preset fork) :=
  sinceFork "pending_deposits" .pectra state.pendingDeposits

/-- The partial withdrawals that wait in a state, from Electra. -/
def pendingPartialWithdrawals (state : BeaconState preset fork) :
    Except ErrorMessage (PendingPartialWithdrawals preset fork) :=
  sinceFork "pending_partial_withdrawals" .pectra state.pendingPartialWithdrawals

/-- The consolidations that wait in a state, from Electra. -/
def pendingConsolidations (state : BeaconState preset fork) :
    Except ErrorMessage (PendingConsolidations preset fork) :=
  sinceFork "pending_consolidations" .pectra state.pendingConsolidations

/-- From Fulu: the proposer of each slot of the current epoch of a state and of the next epochs.

It covers `MIN_SEED_LOOKAHEAD + 1` epochs. -/
def proposerLookahead (state : BeaconState preset fork) :
    Except ErrorMessage (Vector ValidatorIndex
      ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)) :=
  sinceFork "proposer_lookahead" .fusaka state.proposerLookahead

/-- The payments of the bids of the previous and current epochs of a state, from Gloas. -/
def builderPendingPayments (state : BeaconState preset fork) :
    Except ErrorMessage (BuilderPendingPayments preset) :=
  sinceFork "builder_pending_payments" .glamsterdam state.builderPendingPayments

/-- The withdrawals to builders that wait in a state, from Gloas. -/
def builderPendingWithdrawals (state : BeaconState preset fork) :
    Except ErrorMessage BuilderPendingWithdrawals :=
  sinceFork "builder_pending_withdrawals" .glamsterdam state.builderPendingWithdrawals

/-! ## Responses -/

/-- A query of the API that reads one field of a state. -/
inductive StateQuery where
  /-- The root of the state. -/
  | root
  /-- The fork of the state. -/
  | fork
  /-- The finality checkpoints of the state. -/
  | finalityCheckpoints
  /-- The RANDAO mix for an epoch, or for the current epoch. -/
  | randao (epoch : Option Epoch)
  /-- The pending deposits. -/
  | pendingDeposits
  /-- The pending partial withdrawals. -/
  | pendingPartialWithdrawals
  /-- The pending consolidations. -/
  | pendingConsolidations
  /-- The proposer lookahead. -/
  | proposerLookahead
  /-- The pending payments of builders. -/
  | builderPendingPayments
  /-- The pending withdrawals of builders. -/
  | builderPendingWithdrawals
  deriving DecidableEq, Repr

/-- The error of a value that the node cannot encode or compute, with code 500. -/
def internalError (fault : String) : ErrorMessage :=
  { code := 500, message := s!"Internal error: {fault}" }

/-- The JSON of a value, or the error with code 500. -/
def apiJsonOr500 {α : Type} [SszType α] [ApiSpelling α] (x : α) : Except ErrorMessage Json :=
  (toApiJson x).mapError fun fault => internalError (reprStr fault)

/-- The SSZ body of a value, or the error with code 500. -/
def apiSszOr500 {α : Type} [SszType α] (x : α) : Except ErrorMessage ByteArray :=
  (toApiSsz x).mapError fun fault => internalError (reprStr fault)

/-- The response that carries a field of a state of a fork, with the version of that fork. -/
def versioned {α : Type} [SszType α] [ApiSpelling α] (fork : Fork)
    (field : Except ErrorMessage α) : Except ErrorMessage ApiEnvelope := do
  return { version := fork.consensusVersion?, data := ← apiJsonOr500 (← field) }

/-- The response to a query on a state, without the two flags that come from the store.

The root and the RANDAO mix are objects with one key, `root` and `randao`.

The queues, the lookahead and the builder fields also name the consensus version of the state. -/
def stateQuery (state : BeaconState preset fork) : StateQuery → Except ErrorMessage ApiEnvelope
  | .root => do
    let root ← (stateRoot state).mapError fun fault => internalError (reprStr fault)
    return { data := Json.mkObj [("root", .str (toHex root.toArray))] }
  | .fork => do return { data := ← apiJsonOr500 (stateFork state) }
  | .finalityCheckpoints => do return { data := ← apiJsonOr500 (finalityCheckpoints state) }
  | .randao epoch => do
    let mix ← (stateRandao state epoch).mapError fun fault => internalError (reprStr fault)
    return { data := Json.mkObj [("randao", .str (toHex mix.toArray))] }
  | .pendingDeposits => versioned fork (pendingDeposits state)
  | .pendingPartialWithdrawals => versioned fork (pendingPartialWithdrawals state)
  | .pendingConsolidations => versioned fork (pendingConsolidations state)
  | .proposerLookahead => versioned fork (proposerLookahead state)
  | .builderPendingPayments => versioned fork (builderPendingPayments state)
  | .builderPendingWithdrawals => versioned fork (builderPendingWithdrawals state)

/-- The SSZ body of the response to a query on a state, for the queries that have one.

It is the field itself.

The root, the fork, the checkpoints and the mix have no SSZ body. -/
def stateQuerySsz (state : BeaconState preset fork) :
    StateQuery → Option (Except ErrorMessage ByteArray)
  | .pendingDeposits => some (pendingDeposits state >>= apiSszOr500)
  | .pendingPartialWithdrawals => some (pendingPartialWithdrawals state >>= apiSszOr500)
  | .pendingConsolidations => some (pendingConsolidations state >>= apiSszOr500)
  | .proposerLookahead => some (proposerLookahead state >>= apiSszOr500)
  | .builderPendingPayments => some (builderPendingPayments state >>= apiSszOr500)
  | .builderPendingWithdrawals => some (builderPendingWithdrawals state >>= apiSszOr500)
  | _ => none

end EthLib.Consensus.BeaconApi
