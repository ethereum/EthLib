module

public import EthLib.Consensus.Proposers
public import EthLib.Consensus.Transition.BuilderPayments
public import EthLib.Consensus.Transition.EpochParticipation
public import EthLib.Consensus.Transition.EpochPending
public import EthLib.Consensus.Transition.EpochUpdates
public import EthLib.Consensus.Transition.Execution
public import EthLib.Consensus.Transition.Operations
public import EthLib.Consensus.Transition.ParentPayload
public import EthLib.Consensus.Transition.Payload
public import EthLib.Consensus.Transition.Requests
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
  -- The next slot `s + 1`, an error for `s = 2^64 - 1` as for any 64-bit overflow.
  let next ← liftArith (addChecked state.slot 1)
  -- Bit `(s + 1) mod SLOTS_PER_HISTORICAL_ROOT` of the payload availability becomes 0.
  let bits ← writeCircular (state.executionPayloadAvailability gloas).bits next false
  return { state with executionPayloadAvailability := fun _ => ⟨bits⟩ }

/-- The state after the caching of one slot, at the slot `s` of the state. -/
def processSlot (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- `r` is the root of the state at slot `s`.
  let stateRoot ← liftSsz (hashTreeRoot state)
  -- Entry `s mod SLOTS_PER_HISTORICAL_ROOT` of the state roots becomes `r`.
  let stateRoots ← liftAccessor (writeCircularRooted state.stateRoots state.slot stateRoot)
  let state := { state with stateRoots }
  let header := state.latestBlockHeader
  -- The latest block header takes `r` as its state root if that root is still 32 zero bytes.
  --
  -- A block leaves that root empty, so the header of the latest block gets it at the next slot.
  let header :=
    if header.stateRoot = Vector.replicate 32 0 then { header with stateRoot } else header
  let state := { state with latestBlockHeader := header }
  -- Entry `s mod SLOTS_PER_HISTORICAL_ROOT` of the block roots becomes the root of that header.
  let blockRoot ← liftSsz (hashTreeRoot header)
  let blockRoots ← liftAccessor (writeCircularRooted state.blockRoots state.slot blockRoot)
  let state := { state with blockRoots }
  -- From Gloas the payload of slot `s + 1` is marked as not yet available.
  if gloas : .glamsterdam ≤ fork then liftAccessor (unsetNextPayloadAvailability state gloas)
  else return state

/-- From Electra: the state after the pending deposits, then the pending consolidations.

The two queues are those of [EIP-7251].

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer
-/
def processPendingBalances (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Except TransitionError (BeaconState preset fork) :=
  -- From Electra the two queues of EIP-7251 apply: the pending deposits, then the consolidations.
  if electra : .pectra ≤ fork then do
    processPendingConsolidations (← processPendingDeposits config checks state electra) electra
  -- Before Electra neither queue exists, and the state stays the same.
  else pure state

/-- From Altair: the state after the epoch transition.

Heze drops a step, as [EIP-8015] specifies.

Fulu and Gloas add steps, as [EIP-7917] and [EIP-7732] specify.

[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#state-transition
[EIP-8015]: https://eips.ethereum.org/EIPS/eip-8015#validation-changes
-/
def processEpochAltair (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- Justification and finalization come first.
  let state ← processJustificationAndFinalization state
  -- Then the inactivity scores, then the rewards and penalties of the participation flags.
  let state ← processInactivityUpdates config state altair
  let state ← processRewardsAndPenalties config state
  -- Then the registry updates and the slashings.
  let state ← processRegistryUpdates config state
  let state ← processSlashings state
  -- Then the reset of the deposit votes, which Heze drops, as EIP-8015 specifies.
  let state ← (if before : fork < .hegota then processEth1DataReset before state else pure state)
  -- From Electra, the pending deposits and the pending consolidations.
  let state ← processPendingBalances config checks state
  -- From Gloas, the builder payments settle, as EIP-7732 specifies.
  let state ← (if gloas : .glamsterdam ≤ fork then
      liftAccessor (processBuilderPendingPayments state gloas)
    else pure state)
  -- Then the effective balances, then the resets of the slashings and of the RANDAO mix.
  let state ← processEffectiveBalanceUpdates state
  let state ← processSlashingsReset state
  let state ← processRandaoMixesReset state
  -- The history: from Capella a summary of each span, before it a root of each span.
  let state ← if capella : .shapella ≤ fork then processHistoricalSummariesUpdate state capella
    else processHistoricalRootsUpdate state (Nat.lt_of_not_le capella)
  -- Then the rotation of the participation flags and the update of the sync committees.
  let state := processParticipationFlagUpdates state altair
  let state ← processSyncCommitteeUpdates state altair
  -- From Fulu, the lookahead of proposers moves on, as EIP-7917 specifies.
  let state ← (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead state fulu)
    else pure state)
  -- From Gloas, the window of payload committees moves on, as EIP-7732 specifies; it comes last.
  if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow state gloas)
  else pure state

/-- The state after the epoch transition.

From Electra the pending deposits check the signatures of new keys, as an argument says how. -/
def processEpoch (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  -- From Altair the participation flags and the sync committees add their steps.
  if altair : .altair ≤ fork then processEpochAltair config checks state altair
  else do
    have phase0 : fork < .altair := Nat.lt_of_not_le altair
    have before : fork < .hegota := Nat.lt_trans phase0 (by decide)
    -- In Phase 0, justification and finalization, then the rewards and penalties.
    let state ← processJustificationAndFinalization state
    let state ← processRewardsAndPenalties config state
    -- Then the registry updates, the slashings and the reset of the deposit votes.
    let state ← processRegistryUpdates config state
    let state ← processSlashings state
    let state ← processEth1DataReset before state
    -- Then the effective balances, the resets of the slashings and of the RANDAO mix.
    let state ← processEffectiveBalanceUpdates state
    let state ← processSlashingsReset state
    let state ← processRandaoMixesReset state
    -- Then the root of each span of history.
    let state ← processHistoricalRootsUpdate state (Nat.lt_trans phase0 (by decide))
    -- The rotation of the pending attestations comes last.
    processParticipationRecordUpdates state phase0

/-- The state after the epoch transition, if a slot is the last of its epoch. -/
def epochIfLast (config : Config) (checks : SignatureChecks) (next : Slot)
    (state : BeaconState preset fork) : Except TransitionError (BeaconState preset fork) :=
  -- The epoch transition runs when `(s + 1) mod SLOTS_PER_EPOCH = 0`, for the slot `s`.
  if next % preset.SLOTS_PER_EPOCH = 0 then processEpoch config checks state else pure state

/-- The state after one slot. -/
def advanceSlot (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- The next slot `s + 1`, read first: neither step below changes the slot.
  let next ← liftAccessor (liftArith (addChecked state.slot 1))
  -- The slot is cached.
  let state ← processSlot state
  -- The last slot of an epoch runs the epoch transition.
  let state ← epochIfLast config checks next state
  -- The slot moves on to `s + 1`.
  return { state with slot := next }

/-- The state some count of slots later, one slot at a time. -/
def advanceSlots (config : Config) (checks : SignatureChecks) : Nat → BeaconState preset fork →
    Except TransitionError (BeaconState preset fork)
  -- The loop over the slots runs as a recursion on the count of slots left.
  | 0, state => pure state
  | count + 1, state => do advanceSlots config checks count (← advanceSlot config checks state)

/-- The state at a later slot. -/
def processSlots (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (slot : Slot) : Except TransitionError (BeaconState preset fork) := do
  -- The target slot is after the slot `s` of the state.
  ensure (state.slot < slot) (.slotNotAfter slot state.slot)
  -- One slot at a time while `s` is below the target slot.
  advanceSlots config checks (slot.toNat - state.slot.toNat) state

/-- From Bellatrix: the state after the execution part of a block. -/
def processBlockExecution (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (body : BeaconBlockBody preset fork) (bellatrix : .bellatrix ≤ fork) :
    Except TransitionError (BeaconState preset fork) :=
  -- From Gloas the block carries a bid for the payload instead of the payload, as EIP-7732 says.
  if gloas : .glamsterdam ≤ fork then do
    have capella : .shapella ≤ fork := Nat.le_trans (by decide) gloas
    -- The withdrawals come from the state, with no payload, then the bid runs.
    let state ← processWithdrawals state capella fun before =>
      absurd gloas (Nat.not_le_of_lt before)
    processExecutionPayloadBid config checks state gloas (body.signedExecutionPayloadBid gloas)
  else
    have execution : .bellatrix ≤ fork ∧ fork < .glamsterdam := ⟨bellatrix, Nat.lt_of_not_le gloas⟩
    -- From Capella the withdrawals of the payload run first, and the payload always runs.
    if capella : .shapella ≤ fork then do
      let state ← processWithdrawals state capella fun _ => body.executionPayload execution
      processExecutionPayload config engine state body execution
    -- Before Capella the payload runs only once execution is enabled, at the merge or after it.
    else if isExecutionEnabled state body execution then
      processExecutionPayload config engine state body execution
    else pure state

/-- The state that the operations of a block read.

Gloas adds the payload of the parent block, as [EIP-7732] specifies.

Heze drops the deposit vote, as [EIP-8015] specifies.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#state-transition
[EIP-8015]: https://eips.ethereum.org/EIPS/eip-8015#validation-changes
-/
def stateBeforeOperations (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BeaconState preset fork) := do
  -- From Gloas the payload of the parent block runs first, as EIP-7732 specifies.
  --
  -- It changes the state only when the bid of the block builds on that payload.
  --
  -- Otherwise the block must carry no requests of the parent.
  let state ← (if gloas : .glamsterdam ≤ fork then
      processParentExecutionPayload config checks state gloas block.body
    else pure state)
  -- The header comes next.
  let state ← processBlockHeader state block
  -- From Bellatrix, the execution part of the block.
  let state ← (if bellatrix : .bellatrix ≤ fork then
      processBlockExecution config checks engine state block.body bellatrix
    else pure state)
  -- Then the RANDAO reveal.
  let state ← processRandao config checks state block.body
  -- Then the vote on the deposit contract, which Heze drops, as EIP-8015 specifies.
  if before : fork < .hegota then processEth1Data before state block.body else pure state

/-- From Altair: the state after a block. -/
def processBlockAltair (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (altair : .altair ≤ fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- The slot of the parent block, read before the header replaces it.
  --
  -- From Gloas the attestations of the operations read it.
  let parentSlot := state.latestBlockHeader.slot
  -- The parent payload, the header, the execution part, the RANDAO reveal and the deposit vote.
  let state ← stateBeforeOperations config checks engine state block
  -- Then the operations.
  let state ← processOperations config checks state block.body parentSlot
  -- The sync aggregate comes last.
  processSyncAggregate config checks state altair (block.body.syncAggregate altair)

/-- The state after a block.

The execution layer checks the payloads, as an argument like the signature checks. -/
def processBlock (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError (BeaconState preset fork) :=
  -- From Altair the sync aggregate follows the operations.
  if altair : .altair ≤ fork then processBlockAltair config checks engine state block altair
  else do
    -- In Phase 0 the operations ignore the slot of the parent block, which only Gloas reads.
    let parentSlot := state.latestBlockHeader.slot
    -- The header, the RANDAO reveal and the deposit vote, then the operations.
    let state ← stateBeforeOperations config checks engine state block
    processOperations config checks state block.body parentSlot

/-- The check, when the result is validated, that a block carries its proposer's signature. -/
def checkBlockSignature (validateResult : Bool) (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBeaconBlock preset fork) :
    Except TransitionError Unit :=
  -- When the result is validated, the proposer's signature of the block verifies.
  if validateResult then do
    ensure ((← verifyBlockSignature config checks state signed) = true)
      (.invalidBlockSignature signed.message.proposerIndex signed.message.slot)
  else pure ()

/-- The check, when the result is validated, that a block commits to the root of a state. -/
def checkStateRoot (validateResult : Bool) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError Unit :=
  -- When the result is validated, the state root of the block is the root of the state.
  if validateResult then do
    let root ← liftSsz (hashTreeRoot state)
    ensure (block.stateRoot = root) (.wrongStateRoot block.stateRoot root)
  else pure ()

/-- The state after a signed block, on a state already at the slot of the block.

From Bellatrix the execution layer checks the payload of the block. -/
def applySignedBlock (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (signed : SignedBeaconBlock preset fork) (validateResult : Bool) :
    Except TransitionError (BeaconState preset fork) := do
  let block := signed.message
  -- When the result is validated, the block carries the signature of its proposer.
  checkBlockSignature validateResult config checks state signed
  -- The block runs.
  let state ← processBlock config checks engine state block
  -- When the result is validated, its state root is the root of the state after it.
  checkStateRoot validateResult state block
  return state

/-- The state after a signed block. -/
def stateTransition (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (signed : SignedBeaconBlock preset fork) (validateResult : Bool := true) :
    Except TransitionError (BeaconState preset fork) := do
  -- The state advances to the slot of the block, then the signed block applies.
  let state ← processSlots config checks state signed.message.slot
  applySignedBlock config checks engine state signed validateResult

end EthLib.Consensus
