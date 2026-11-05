module

public import EthLib.Consensus.Transition.EpochParticipation
public import EthLib.Consensus.Transition.EpochUpdates
public import EthLib.Consensus.Transition.Execution
public import EthLib.Consensus.Transition.Operations
public import EthLib.Consensus.Transition.SyncAggregate

/-!
# `Consensus.Transition.StateTransition`

The beacon state transition: from a state and a signed block to the state after the block.

The state first advances slot by slot to the slot of the block.

Each slot caches the root of the state and of the latest block in the circular buffers of roots.

The last slot of each epoch also runs the epoch transition.

Then the block's signature is checked, the block runs, and the state root of the block is checked.

A failed assertion, a read out of range and a 64-bit overflow all make the block invalid.

Where a later fork changes a rule, the step fails as not yet specified there.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-- From Gloas: the state in which the payload of the slot after the state's slot is unavailable.

Its bit in the circular buffer of payload availability is cleared.

A slot of 2^64 - 1 has no next slot, and is an error. -/
def unsetNextPayloadAvailability (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Except AccessorError (BeaconState preset fork) := do
  let next ← liftArith (addChecked state.slot 1)
  let index := (next % preset.SLOTS_PER_HISTORICAL_ROOT).toNat
  let bits := (state.executionPayloadAvailability gloas).bits
  return { state with executionPayloadAvailability := fun _ => ⟨bits.set! index false⟩ }

/-- The state after the caching of one slot.

The root of the state goes into the circular buffer of state roots.

The latest block header, if its state root is still empty, takes that root.

The root of the latest block header then goes into the circular buffer of block roots.

From Gloas the payload of the next slot is then marked as not yet available. -/
def processSlot (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let index := (state.slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat
  let stateRoot ← liftSsz (hashTreeRoot state)
  let state := { state with stateRoots := state.stateRoots.set! index stateRoot }
  let header := state.latestBlockHeader
  let header :=
    if header.stateRoot = Vector.replicate 32 0 then { header with stateRoot } else header
  let state := { state with latestBlockHeader := header }
  let blockRoot ← liftSsz (hashTreeRoot header)
  let state := { state with blockRoots := state.blockRoots.set! index blockRoot }
  if gloas : .glamsterdam ≤ fork then liftAccessor (unsetNextPayloadAvailability state gloas)
  else return state

/-- From Altair: the state after the epoch transition.

Justification and finalization come first, then the inactivity scores, rewards and penalties.

The registry updates, the slashings and the reset of the deposit votes follow.

Then come the effective balances, the slashings and RANDAO resets, and the history.

Before Capella the history takes a root of each span, and from Capella a summary.

The rotation of the participation flags and the sync committee update come last.

Deneb changes the registry updates, and Electra adds steps.

EthLib does not yet have those rules here, so both fail as not yet specified. -/
def processEpochAltair (config : Config) (state : BeaconState preset fork)
    (altair : .altair ≤ fork) : Except TransitionError (BeaconState preset fork) :=
  if electra : .pectra ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le electra) (by decide)
    let state ← processJustificationAndFinalization state
    let state ← processInactivityUpdates config state altair
    let state ← processRewardsAndPenalties config state
    let state ← processRegistryUpdates config state
    let state ← processSlashings state
    let state ← processEth1DataReset before state
    let state ← processEffectiveBalanceUpdates state
    let state ← processSlashingsReset state
    let state ← processRandaoMixesReset state
    let state ← if capella : .shapella ≤ fork then processHistoricalSummariesUpdate state capella
      else processHistoricalRootsUpdate state
    let state := processParticipationFlagUpdates state altair
    processSyncCommitteeUpdates state altair

/-- The state after the epoch transition.

Before Altair, justification and finalization come first, then rewards and penalties.

The registry updates, the slashings and the reset of the deposit votes follow.

Then come the effective balances, the slashings and RANDAO resets and the historical roots.

The rotation of the pending attestations comes last.

From Altair the participation flags and the sync committees add their steps. -/
def processEpoch (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then processEpochAltair config state altair
  else do
    have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
    let state ← processJustificationAndFinalization state
    let state ← processRewardsAndPenalties config state
    let state ← processRegistryUpdates config state
    let state ← processSlashings state
    let state ← processEth1DataReset before state
    let state ← processEffectiveBalanceUpdates state
    let state ← processSlashingsReset state
    let state ← processRandaoMixesReset state
    let state ← processHistoricalRootsUpdate state
    processParticipationRecordUpdates state

/-- The state after the epoch transition, if a slot is the last of its epoch. -/
def epochIfLast (config : Config) (next : Slot) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if next % preset.SLOTS_PER_EPOCH = 0 then processEpoch config state else pure state

/-- The state after one slot.

The slot is cached, the last slot of an epoch runs the epoch transition, and the slot moves on.

Neither step changes the slot, so the next slot is that of the state plus one. -/
def advanceSlot (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let next ← liftAccessor (liftArith (addChecked state.slot 1))
  let state ← processSlot state
  let state ← epochIfLast config next state
  return { state with slot := next }

/-- The state some count of slots later, one slot at a time. -/
def advanceSlots (config : Config) : Nat → BeaconState preset fork →
    Except TransitionError (BeaconState preset fork)
  | 0, state => pure state
  | count + 1, state => do advanceSlots config count (← advanceSlot config state)

/-- The state at a later slot.

The slot must be after the slot of the state. -/
def processSlots (config : Config) (state : BeaconState preset fork) (slot : Slot) :
    Except TransitionError (BeaconState preset fork) := do
  ensure (state.slot < slot) (.slotNotAfter slot state.slot)
  advanceSlots config (slot.toNat - state.slot.toNat) state

/-- From Bellatrix: the state after the execution part of a block.

Before Capella the payload runs only once execution is enabled, at the merge or after it.

From Capella the withdrawals of the payload run first, and the payload always runs. -/
def processBlockExecution (config : Config) (engine : ExecutionEngine preset fork)
    (state : BeaconState preset fork) (body : BeaconBlockBody preset fork)
    (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    Except TransitionError (BeaconState preset fork) :=
  if capella : .shapella ≤ fork then do
    let state ← processWithdrawals state capella fun _ => body.executionPayload bellatrix
    processExecutionPayload config engine state body bellatrix
  else if isExecutionEnabled state body bellatrix then
    processExecutionPayload config engine state body bellatrix
  else pure state

/-- From Altair: the state after a block.

The header runs first, then from Bellatrix the execution part of the block.

The RANDAO reveal, the vote on the deposit contract and the operations follow.

The sync aggregate comes last.

Deneb changes the voluntary exits, and Electra the operations.

EthLib does not yet have those rules here, so both fail as not yet specified. -/
def processBlockAltair (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (altair : .altair ≤ fork) :
    Except TransitionError (BeaconState preset fork) :=
  if electra : .pectra ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    have before : fork < .glamsterdam := Nat.lt_trans (Nat.lt_of_not_le electra) (by decide)
    let state ← processBlockHeader state block
    let state ← if bellatrix : .bellatrix ≤ fork then
        processBlockExecution config engine state block.body ⟨bellatrix, before⟩
      else pure state
    let state ← processRandao config checks state block.body
    let state ← processEth1Data (Nat.lt_trans before (by decide)) state block.body
    let state ← processOperations config checks state block.body
    processSyncAggregate config checks state altair (block.body.syncAggregate altair)

/-- The state after a block.

Before Altair, the header runs first, then the RANDAO reveal, the deposit vote and the operations.

From Altair the sync aggregate follows, and from Bellatrix the execution part of the block.

The execution layer checks the payloads, as an argument like the signature checks. -/
def processBlock (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then processBlockAltair config checks engine state block altair
  else do
    have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
    let state ← processBlockHeader state block
    let state ← processRandao config checks state block.body
    let state ← processEth1Data before state block.body
    processOperations config checks state block.body

/-- The check, when the result is validated, that a block carries its proposer's signature. -/
def checkBlockSignature (validateResult : Bool) (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBeaconBlock preset fork) :
    Except TransitionError Unit :=
  if validateResult then do
    ensure ((← verifyBlockSignature config checks state signed) = true) .invalidBlockSignature
  else pure ()

/-- The check, when the result is validated, that a block commits to the root of a state. -/
def checkStateRoot (validateResult : Bool) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError Unit :=
  if validateResult then do
    ensure (block.stateRoot = (← liftSsz (hashTreeRoot state))) .wrongStateRoot
  else pure ()

/-- The state after a signed block.

The state advances to the slot of the block, and the block runs.

When the result is validated, the block must carry the signature of its proposer.

Its state root must then be the root of the state after it.

From Bellatrix the execution layer checks the payload of the block. -/
def stateTransition (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (signed : SignedBeaconBlock preset fork) (validateResult : Bool := true) :
    Except TransitionError (BeaconState preset fork) := do
  let block := signed.message
  let state ← processSlots config state block.slot
  checkBlockSignature validateResult config checks state signed
  let state ← processBlock config checks engine state block
  checkStateRoot validateResult state block
  return state

end EthLib.Consensus
