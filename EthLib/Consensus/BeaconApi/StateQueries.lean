module

public import EthLib.Consensus.Accessors
public import EthLib.Consensus.BeaconApi.Spelling

/-!
# `Consensus.BeaconApi.StateQueries`

The answers of the Beacon API that read one field of a state.

The [states endpoints] fix each answer, one file per endpoint.

The flags `execution_optimistic` and `finalized` come from the store, not from the state.

SOUNDNESS.md records the points that the source leaves open.

[states endpoints]: https://github.com/ethereum/beacon-APIs/tree/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states
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
  -- The root endpoint: the HashTreeRoot of the BeaconState object.
  SszType.hashTreeRoot state

/-- The fork of a state: its previous and current versions, and the epoch of the current one. -/
def stateFork (state : BeaconState preset fork) : ForkVersions :=
  -- The fork endpoint: the Fork object of the state.
  state.forkVersions

/-- The finality checkpoints of a state. -/
def finalityCheckpoints (state : BeaconState preset fork) : FinalityCheckpoints :=
  -- The finality checkpoints endpoint: the three checkpoints as the state holds them.
  --
  -- Before finality the source asks for epoch 0 and the zero root.
  --
  -- SOUNDNESS.md records which states are shown to hold them.
  { previousJustified := state.previousJustifiedCheckpoint
    currentJustified := state.currentJustifiedCheckpoint
    finalized := state.finalizedCheckpoint }

/-- Whether the circular buffer of a state still holds the RANDAO mix of an epoch.

The buffer has one entry for each of the last epochs, as many as its length, up to the current one.
-/
def holdsRandaoMix (state : BeaconState preset fork) (epoch : Epoch) : Bool :=
  -- A later epoch than the current one has no mix yet.
  epoch.toNat ≤ (getCurrentEpoch state).toNat &&
    -- An epoch a buffer length or more before the current one has had its entry written over.
    (getCurrentEpoch state).toNat < epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat

/-- The error of a query on a state before the fork that adds its field, with code 400.

The message names the fork by its consensus version, or by its own name without one. -/
def beforeFork (query : String) (first : Fork) : ErrorMessage :=
  let name := (first.consensusVersion?.map (·.name)).getD first.name
  -- The source gives code 400 and no message, so the message is EthLib's.
  { code := 400, message := s!"{query} is not in a state before {name}" }

/-- A field that a fork adds, or the error with code 400 for a state before that fork. -/
def sinceFork {α : Type} (query : String) (first : Fork) (field : Since first fork α) :
    Except ErrorMessage α :=
  -- The endpoints: code 400 for a state before the fork that adds the field.
  if since : first ≤ fork then .ok (field since) else .error (beforeFork query first)

/-- The deposits that wait in a state, from Electra. -/
def pendingDeposits (state : BeaconState preset fork) :
    Except ErrorMessage (PendingDeposits preset fork) :=
  -- The pending deposits endpoint: 400 for a state before Electra.
  sinceFork "pending_deposits" .pectra state.pendingDeposits

/-- The partial withdrawals that wait in a state, from Electra. -/
def pendingPartialWithdrawals (state : BeaconState preset fork) :
    Except ErrorMessage (PendingPartialWithdrawals preset fork) :=
  -- The pending partial withdrawals endpoint: 400 for a state before Electra.
  sinceFork "pending_partial_withdrawals" .pectra state.pendingPartialWithdrawals

/-- The consolidations that wait in a state, from Electra. -/
def pendingConsolidations (state : BeaconState preset fork) :
    Except ErrorMessage (PendingConsolidations preset fork) :=
  -- The pending consolidations endpoint: 400 for a state before Electra.
  sinceFork "pending_consolidations" .pectra state.pendingConsolidations

/-- From Fulu: the proposer of each slot of the current epoch of a state and of the next epochs.

It covers `MIN_SEED_LOOKAHEAD + 1` epochs. -/
def proposerLookahead (state : BeaconState preset fork) :
    Except ErrorMessage (Vector ValidatorIndex
      ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)) :=
  -- The proposer lookahead endpoint: 400 for a state before Fulu.
  --
  -- The JSON schema fixes 64 items, the mainnet value.
  --
  -- EthLib follows the preset, as the SSZ type of the source does.
  sinceFork "proposer_lookahead" .fusaka state.proposerLookahead

/-- The payments of the bids of the previous and current epochs of a state, from Gloas. -/
def builderPendingPayments (state : BeaconState preset fork) :
    Except ErrorMessage (BuilderPendingPayments preset) :=
  -- The builder pending payments endpoint: 400 for a state before Gloas.
  sinceFork "builder_pending_payments" .glamsterdam state.builderPendingPayments

/-- The withdrawals to builders that wait in a state, from Gloas. -/
def builderPendingWithdrawals (state : BeaconState preset fork) :
    Except ErrorMessage BuilderPendingWithdrawals :=
  -- The builder pending withdrawals endpoint: 400 for a state before Gloas.
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
  -- The source has no error of its own for such a value.
  --
  -- EthLib gives code 500, the code of the source for an internal error, with its own message.
  { code := 500, message := s!"Internal error: {fault}" }

/-- The JSON of a value, or the error with code 500. -/
def apiJsonOr500 {α : Type} [SszType α] [ApiSpelling α] (x : α) : Except ErrorMessage Json :=
  (toApiJson x).mapError fun _ => internalError "no JSON of a value"

/-- The SSZ body of a value, or the error with code 500. -/
def apiSszOr500 {α : Type} [SszType α] (x : α) : Except ErrorMessage ByteArray :=
  (toApiSsz x).mapError fun _ => internalError "no SSZ of a value"

/-- The response that carries a field of a state of a fork, with the version of that fork. -/
def versioned {α : Type} [SszType α] [ApiSpelling α] (fork : Fork)
    (field : Except ErrorMessage α) : Except ErrorMessage ApiEnvelope := do
  -- The schema requires a version, the consensus version of the fork, with the data.
  --
  -- A fork that the source names no consensus version for gives none, against the schema.
  return { version := fork.consensusVersion?, data := ← apiJsonOr500 (← field) }

/-- The error of a RANDAO query for an epoch whose mix the state does not hold, with code 400.

Its message is the example of the source. -/
def randaoOutOfRange : ErrorMessage :=
  { code := 400, message := "Epoch is out of range for the `randao_mixes` of the state" }

/-- The RANDAO mix of a state for an epoch, or for its current epoch when none is given.

[beacon-APIs, `getStateRandao`][randao] gives the error with code 400 for an epoch out of range.

[randao]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/states/randao.yaml
-/
def stateRandao (state : BeaconState preset fork) (epoch : Option Epoch) :
    Except ErrorMessage Bytes32 := do
  -- The source: the current epoch of the state when no epoch is specified.
  let epoch := epoch.getD (getCurrentEpoch state)
  -- The source: code 400 for an epoch out of range, but it names no range.
  --
  -- EthLib's choice: an epoch whose mix the buffer no longer holds, or does not hold yet.
  --
  -- Reading the buffer at such an epoch would give the mix of another epoch.
  --
  -- A buffer of length 0 holds no mix, so every epoch gets the error.
  unless holdsRandaoMix state epoch do throw randaoOutOfRange
  -- The mix of the epoch in the buffer of the state.
  (getRandaoMix state epoch).mapError fun _ => internalError "no RANDAO mix"

/-- The response to a query on a state, without the two flags that come from the store. -/
def stateQuery (state : BeaconState preset fork) : StateQuery → Except ErrorMessage ApiEnvelope
  | .root => do
    let root ← (stateRoot state).mapError fun _ => internalError "no state root"
    -- The root endpoint: an object with the one required key root.
    return { data := Json.mkObj [("root", .str (toHex ⟨root.toArray⟩))] }
  -- The fork and finality checkpoints endpoints: the object itself, with no version.
  | .fork => do return { data := ← apiJsonOr500 (stateFork state) }
  | .finalityCheckpoints => do return { data := ← apiJsonOr500 (finalityCheckpoints state) }
  | .randao epoch => do
    let mix ← stateRandao state epoch
    -- The RANDAO endpoint: an object with the one required key randao.
    return { data := Json.mkObj [("randao", .str (toHex ⟨mix.toArray⟩))] }
  -- The queues, the lookahead and the builder fields: with the version of the state.
  | .pendingDeposits => versioned fork (pendingDeposits state)
  | .pendingPartialWithdrawals => versioned fork (pendingPartialWithdrawals state)
  | .pendingConsolidations => versioned fork (pendingConsolidations state)
  | .proposerLookahead => versioned fork (proposerLookahead state)
  | .builderPendingPayments => versioned fork (builderPendingPayments state)
  | .builderPendingWithdrawals => versioned fork (builderPendingWithdrawals state)

/-- The SSZ body of the response to a query on a state, for the queries that have one. -/
def stateQuerySsz (state : BeaconState preset fork) :
    StateQuery → Option (Except ErrorMessage ByteArray)
  -- The endpoints with an octet-stream response: the SSZ bytes of the field itself.
  | .pendingDeposits => some (pendingDeposits state >>= apiSszOr500)
  | .pendingPartialWithdrawals => some (pendingPartialWithdrawals state >>= apiSszOr500)
  | .pendingConsolidations => some (pendingConsolidations state >>= apiSszOr500)
  | .proposerLookahead => some (proposerLookahead state >>= apiSszOr500)
  | .builderPendingPayments => some (builderPendingPayments state >>= apiSszOr500)
  | .builderPendingWithdrawals => some (builderPendingWithdrawals state >>= apiSszOr500)
  -- The root, the fork, the checkpoints and the mix: the source gives no SSZ body.
  | _ => none

end EthLib.Consensus.BeaconApi
