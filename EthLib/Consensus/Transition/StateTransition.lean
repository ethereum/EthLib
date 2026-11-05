module

public import EthLib.Consensus.Transition.EpochUpdates
public import EthLib.Consensus.Transition.Operations

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

/-- The state after the caching of one slot.

The root of the state goes into the circular buffer of state roots.

The latest block header, if its state root is still empty, takes that root.

The root of the latest block header then goes into the circular buffer of block roots.

Gloas also records the availability of the payload, which EthLib does not yet have here. -/
def processSlot (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if .glamsterdam ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    let index := (state.slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat
    let stateRoot ← liftSsz (hashTreeRoot state)
    let state := { state with stateRoots := state.stateRoots.set! index stateRoot }
    let header := state.latestBlockHeader
    let header :=
      if header.stateRoot = Vector.replicate 32 0 then { header with stateRoot } else header
    let state := { state with latestBlockHeader := header }
    let blockRoot ← liftSsz (hashTreeRoot header)
    return { state with blockRoots := state.blockRoots.set! index blockRoot }

/-- The state after the epoch transition, before Altair.

Justification and finalization come first, then rewards and penalties.

The registry updates, the slashings and the reset of the deposit votes follow.

Then come the effective balances, the slashings and RANDAO resets and the historical roots.

The rotation of the pending attestations comes last.

Altair changes the steps, which EthLib does not yet have here. -/
def processEpoch (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
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

/-- The state after a block, before Altair.

The header runs first, then the RANDAO reveal, the vote on the deposit contract and the operations.

Altair adds the sync aggregate, which EthLib does not yet have here. -/
def processBlock (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
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

Its state root must then be the root of the state after it. -/
def stateTransition (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (signed : SignedBeaconBlock preset fork) (validateResult : Bool := true) :
    Except TransitionError (BeaconState preset fork) := do
  let block := signed.message
  let state ← processSlots config state block.slot
  checkBlockSignature validateResult config checks state signed
  let state ← processBlock config checks state block
  checkStateRoot validateResult state block
  return state

end EthLib.Consensus
