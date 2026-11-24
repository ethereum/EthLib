module

public import EthLib.Consensus.BeaconApi.Committees
public import EthLib.Consensus.BeaconApi.Registries
public import EthLib.Consensus.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochParticipation
public import EthLib.Consensus.Transition.StateTransition
public import EthLib.Consensus.Transition.SyncAggregate

/-!
# `Consensus.BeaconApi.Rewards`

The answers of the Beacon API that split the rewards of validators into their parts.

The [attestation rewards] of an epoch give, for each validator, what each kind of vote earned.

The ideal rewards give the same parts for a validator that voted right and in time.

The [sync committee rewards] of a block give, for each member, what its seats earned or paid.

The [block rewards] give what the proposer of a block earned in it, by the kind of item that paid.

The response [types] fix the fields of each answer.

SOUNDNESS.md records the points that the source leaves open.

[attestation rewards]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/rewards/attestations.yaml
[block rewards]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/rewards/blocks.yaml
[sync committee rewards]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/beacon/rewards/sync_committee.yaml
[types]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/rewards.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Answers -/

/-- What each kind of vote of one validator earned in an epoch, in Gwei.

A negative amount is a net penalty. -/
structure AttestationRewards where
  /-- The index of the validator in the registry. -/
  validatorIndex : ValidatorIndex
  /-- The net reward of the head vote. -/
  head : Int
  /-- The net reward of the target vote. -/
  target : Int
  /-- The net reward of the source vote. -/
  source : Int
  /-- Before Altair, the reward of the validator for the inclusion of its vote; from Altair, none.

  It leaves out what the validator earned as a proposer that included votes. -/
  inclusionDelay : Option Gwei
  /-- The inactivity penalty, as a negative amount. -/
  inactivity : Int
  deriving DecidableEq, Repr

/-- What each kind of vote earns in an epoch for a validator of some balance that voted right. -/
structure IdealAttestationRewards where
  /-- The effective balance of the validator. -/
  effectiveBalance : Gwei
  /-- The reward of the head vote. -/
  head : Int
  /-- The reward of the target vote. -/
  target : Int
  /-- The reward of the source vote. -/
  source : Int
  /-- Before Altair, the reward for an inclusion one slot after the vote; from Altair, nothing. -/
  inclusionDelay : Option Gwei
  /-- The inactivity penalty, as a negative amount. -/
  inactivity : Int
  deriving DecidableEq, Repr

/-- The JSON of a signed amount: its decimal text. -/
def intJson (n : Int) : Json :=
  .str (toString n)

/-- Whether a signed amount fits the 64-bit signed integers of the response types.

The response [types] give each signed amount the type [`Int64`][int64].

Its name reads as a signed 64-bit integer, from `-2^63` to `2^63 - 1`; the schema states no range.

Before Altair, the reward of a matched vote can fall outside.

A sync committee reward stays inside, since it is below `2^58` in absolute value.

[types]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/rewards.yaml
[int64]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/primitive.yaml -/
def int64Fits (n : Int) : Bool :=
  -- `-2^63 <= n < 2^63`.
  decide (-2 ^ 63 ≤ n ∧ n < 2 ^ 63)

/-- Whether each signed amount of the rewards of one validator fits 64 bits. -/
def AttestationRewards.fits (rewards : AttestationRewards) : Bool :=
  int64Fits rewards.head && int64Fits rewards.target && int64Fits rewards.source &&
    int64Fits rewards.inactivity

/-- Whether each signed amount of the ideal rewards of one balance fits 64 bits. -/
def IdealAttestationRewards.fits (rewards : IdealAttestationRewards) : Bool :=
  int64Fits rewards.head && int64Fits rewards.target && int64Fits rewards.source &&
    int64Fits rewards.inactivity

/-- The error of an answer with a signed amount outside 64 bits, with code 500. -/
def rewardOutOfRange : ErrorMessage :=
  internalError "a reward does not fit a signed 64-bit integer"

/-- The fields of the inclusion reward, present only when there is one. -/
def inclusionDelayJson (reward : Option Gwei) : List (String × Json) :=
  -- The types: the inclusion delay field is optional, and for Phase 0 only.
  (reward.map fun amount => ("inclusion_delay", uintJson amount)).toList

/-- The JSON of the rewards of one validator, as the API writes them. -/
def AttestationRewards.toJson (rewards : AttestationRewards) : Json :=
  .mkObj <| [("validator_index", uintJson rewards.validatorIndex),
    ("head", intJson rewards.head), ("target", intJson rewards.target),
    ("source", intJson rewards.source)] ++ inclusionDelayJson rewards.inclusionDelay ++
    [("inactivity", intJson rewards.inactivity)]

/-- The JSON of the ideal rewards of one effective balance, as the API writes them. -/
def IdealAttestationRewards.toJson (rewards : IdealAttestationRewards) : Json :=
  .mkObj <| [("effective_balance", uintJson rewards.effectiveBalance),
    ("head", intJson rewards.head), ("target", intJson rewards.target),
    ("source", intJson rewards.source)] ++ inclusionDelayJson rewards.inclusionDelay ++
    [("inactivity", intJson rewards.inactivity)]

/-! ## Rewards of the validators -/

/-- The reward minus the penalty at a position of some deltas. -/
def netDelta (deltas : Array Gwei × Array Gwei) (position : Nat) : Int :=
  -- `reward - penalty` as an integer, with 0 at a position past the end.
  ((deltas.1.getD position 0).toNat : Int) - (deltas.2.getD position 0).toNat

/-- Before Altair: the inclusion reward of each attester of the previous epoch, at its position.

It is the part of the inclusion deltas that goes to the attester, without the proposer shares. -/
def attesterInclusionRewards (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei) := do
  let size := state.validators.data.size
  -- The attestations of the previous epoch whose source matches, and their signers.
  let attestations ← getMatchingSourceAttestations state before (getPreviousEpoch state)
  let signers ← liftAccessor (attestations.toList.mapM (getPendingAttestingIndices state))
  -- The signers that are not slashed.
  let attesters ← liftAccessor (unslashedAmong state signers)
  let total ← liftAccessor (getTotalActiveBalance state)
  -- For each attester, the first of its attestations with the least inclusion delay.
  let earliest := earliestInclusions size (attestations.zip signers.toArray)
  attesters.foldlM (init := Array.replicate size 0) fun rewards index => do
    let some attestation := earliest.getD index.toNat none
      | throw (.accessor (.indexOutOfRange index))
    let base ← liftAccessor (getBaseReward state total index)
    -- The attester's own part: (b - p) / d rounded down, with b its base reward and d that delay.
    --
    -- Here p is the proposer share of b.
    --
    -- The proposer share of the same deltas goes to the proposer, and is left out here.
    addDelta rewards index (← inclusionAttesterReward preset base attestation.inclusionDelay)

/-- What each kind of vote earned for each named validator in the previous epoch of a state.

The state is the one that the rewards step of the epoch transition reads. -/
def attestationRewards (config : Config) (state : BeaconState preset fork)
    (ids : List ValidatorId) : Except TransitionError (List AttestationRewards) := do
  -- The source: no array names every validator, and so does an empty one here.
  --
  -- An identifier that names no validator gives no entry.
  let indices := selectValidators state ids
  -- The inactivity part is minus the penalty of the inactivity deltas, which hold no reward.
  let inactivity ← getInactivityPenaltyDeltas config state
  if altair : .altair ≤ fork then
    -- From Altair: the deltas of the three flags, in the order the transition applies them.
    let flags ← (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
      (getFlagIndexDeltas state altair)
    -- Each part is the reward minus the penalty of its flag.
    let flag (flagIndex : UInt64) (position : Nat) :=
      netDelta (flags.getD flagIndex.toNat (#[], #[])) position
    -- No inclusion part from Altair, as the types say: Phase 0 only.
    return indices.map fun index =>
      { validatorIndex := index, head := flag TIMELY_HEAD_FLAG_INDEX index.toNat,
        target := flag TIMELY_TARGET_FLAG_INDEX index.toNat,
        source := flag TIMELY_SOURCE_FLAG_INDEX index.toNat, inclusionDelay := none,
        inactivity := -((inactivity.2.getD index.toNat 0).toNat : Int) }
  else
    have before := Nat.lt_of_not_le altair
    -- Before Altair: the deltas of the source, target and head votes.
    let source ← getSourceDeltas state before
    let target ← getTargetDeltas state before
    let head ← getHeadDeltas state before
    -- The inclusion part: the attester's own part of the inclusion deltas.
    let inclusion ← attesterInclusionRewards state before
    -- Each vote part is the reward minus the penalty of its deltas.
    return indices.map fun index =>
      { validatorIndex := index, head := netDelta head index.toNat,
        target := netDelta target index.toNat, source := netDelta source index.toNat,
        inclusionDelay := some (inclusion.getD index.toNat 0),
        inactivity := -((inactivity.2.getD index.toNat 0).toNat : Int) }

/-! ## Ideal rewards -/

/-- The distinct effective balances of the eligible validators, in increasing order.

Each comes with the first eligible validator that has it. -/
def idealBalances (state : BeaconState preset fork) :
    Except TransitionError (List (Gwei × ValidatorIndex)) := do
  -- The validators that the rewards step rewards or penalizes.
  let eligible ← getEligibleValidatorIndices state
  -- Each effective balance once, with the first eligible validator that has it.
  let firsts ← eligible.foldlM (init := ([] : List (Gwei × ValidatorIndex))) fun found index => do
    let balance := (← liftAccessor (getValidator state index)).effectiveBalance
    if found.any (·.1 == balance) then return found else return found ++ [(balance, index)]
  -- EthLib's choice: in increasing order of balance, since the source gives no order.
  return firsts.mergeSort fun a b => a.1.toNat ≤ b.1.toNat

/-- The total effective balance of the unslashed validators of some pending attestations. -/
def attestingBalance (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) : Except TransitionError Gwei :=
  -- The total balance of the unslashed signers of the attestations.
  liftAccessor do getTotalBalance state (← getUnslashedAttestingIndices state attestations)

/-- From Altair: the reward of one flag for an eligible validator that set it.

It is what the transition gives a validator that set it, at the participation of the epoch. -/
def idealFlagReward (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) (index : ValidatorIndex) :
    Except TransitionError Gwei := do
  let size := state.validators.data.size
  -- The unslashed validators that set the flag in the previous epoch, and their balance.
  let participating ← liftAccessor (getUnslashedParticipatingIndices state altair
    flagIndex.val.toUInt64 (getPreviousEpoch state))
  let participatingBalance ← liftAccessor (getTotalBalance state participating)
  let total ← liftAccessor (getTotalActiveBalance state)
  let increment := preset.EFFECTIVE_BALANCE_INCREMENT
  let zeros : Array Gwei := Array.replicate size 0
  -- The delta that the transition gives the validator as one that set the flag.
  --
  -- The balances are counted in increments, as the transition counts them.
  let (rewards, _) ← addFlagDelta state flagIndex (Array.replicate size true) total
    (participatingBalance / increment) (total / increment) (zeros, zeros) index
  -- Its reward; a validator that set the flag pays no penalty for it.
  return rewards.getD index.toNat 0

/-- Before Altair: the reward of one kind of vote for an eligible validator whose vote matched. -/
def idealComponentReward (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) (index : ValidatorIndex) :
    Except TransitionError Gwei := do
  let total ← liftAccessor (getTotalActiveBalance state)
  let base ← liftAccessor (getBaseReward state total index)
  -- The reward of the delta for a vote that matched, at the attesting balance of the epoch.
  return (← componentDelta state true base (← attestingBalance state attestations) total).1

/-- Before Altair: the inactivity penalty of an eligible validator whose target vote matched. -/
def idealInactivityPenalty (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except TransitionError Gwei := do
  if ← isInInactivityLeak state then
    let size := state.validators.data.size
    let total ← liftAccessor (getTotalActiveBalance state)
    -- In a leak: the penalty that the transition gives a validator whose target vote matched.
    let penalties ← addInactivityPenalty state total (← getFinalityDelay state)
      (Array.replicate size true) (Array.replicate size 0) index
    return penalties.getD index.toNat 0
  -- Outside a leak there is none.
  else return 0

/-- The rewards of an eligible validator of some effective balance that voted right and in time.

Its votes match the source, the target and the head, so it pays no penalty for them. -/
def idealRewardsOf (state : BeaconState preset fork) (balance : Gwei) (index : ValidatorIndex) :
    Except TransitionError IdealAttestationRewards := do
  -- From Altair: the reward of each flag, which it set.
  --
  -- It set every flag, so it pays no inactivity penalty, and no inclusion part exists.
  if altair : .altair ≤ fork then
    let flag (flagIndex : UInt64) (inside : flagIndex.toNat < PARTICIPATION_FLAG_WEIGHTS.length) :
        Except TransitionError Int := do
      return ((← idealFlagReward state altair ⟨flagIndex.toNat, inside⟩ index).toNat : Int)
    return { effectiveBalance := balance, head := ← flag TIMELY_HEAD_FLAG_INDEX (by decide),
             target := ← flag TIMELY_TARGET_FLAG_INDEX (by decide),
             source := ← flag TIMELY_SOURCE_FLAG_INDEX (by decide), inclusionDelay := none,
             inactivity := 0 }
  else
    have before := Nat.lt_of_not_le altair
    let previous := getPreviousEpoch state
    let component (attestations : Array (PendingAttestation preset)) :
        Except TransitionError Int := do
      return ((← idealComponentReward state attestations index).toNat : Int)
    let total ← liftAccessor (getTotalActiveBalance state)
    let base ← liftAccessor (getBaseReward state total index)
    -- Before Altair: included one slot after its vote, the least delay.
    let inclusion ← inclusionAttesterReward preset base 1
    -- The reward of each matched vote, and in a leak an inactivity penalty.
    return { effectiveBalance := balance,
             head := ← component (← getMatchingHeadAttestations state before previous),
             target := ← component (← getMatchingTargetAttestations state before previous),
             source := ← component (← getMatchingSourceAttestations state before previous),
             inclusionDelay := some inclusion,
             inactivity := -((← idealInactivityPenalty state index).toNat : Int) }

/-- The ideal rewards of each effective balance of the eligible validators, in increasing order. -/
def idealAttestationRewards (state : BeaconState preset fork) :
    Except TransitionError (List IdealAttestationRewards) := do
  -- Each balance is read at the first eligible validator that has it.
  (← idealBalances state).mapM fun (balance, index) => idealRewardsOf state balance index

/-! ## Response -/

/-- The state that the rewards step of the epoch transition reads, from the state it starts from. -/
def stateBeforeRewards (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- The epoch transition runs justification and finalization first.
  let state ← processJustificationAndFinalization state
  -- Then, from Altair, the update of the inactivity scores.
  if altair : .altair ≤ fork then processInactivityUpdates config state altair else pure state

/-- The error of an epoch that the state does not hold the rewards of, with code 404. -/
def epochNotKnown (epoch : Epoch) : ErrorMessage :=
  -- The example message of the source, with the epoch after its first word.
  { code := 404, message := s!"Epoch {epoch.toNat} not known or required data not available" }

/-- The response of the attestation rewards endpoint, without the flags that come from the store. -/
def attestationRewardsResponse (config : Config) (state : BeaconState preset fork)
    (epoch : Epoch) (ids : List ValidatorId) : Except ErrorMessage ApiEnvelope := do
  -- EthLib's choice of state: one at the last slot of an epoch past the first.
  --
  -- It answers only for the epoch before, and holds every vote of it that the transition rewards.
  --
  -- Any other epoch, or a state at another slot: code 404, epoch not known.
  if getCurrentEpoch state = GENESIS_EPOCH ∨ getPreviousEpoch state ≠ epoch ∨
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 then
    throw (epochNotKnown epoch)
  -- A failure of the rewards computation gives code 500.
  let fault (_ : TransitionError) := internalError "no attestation rewards"
  -- The parts are read after the steps of the epoch transition that come before the rewards.
  let state ← (stateBeforeRewards config state).mapError fault
  let ideal ← (idealAttestationRewards state).mapError fault
  let total ← (attestationRewards config state ids).mapError fault
  -- The response types give each signed amount 64 bits.
  --
  -- An answer with a larger one fails with code 500.
  ensure (ideal.all (·.fits) && total.all (·.fits)) rewardOutOfRange
  -- The types: the ideal rewards, then the total rewards.
  return { data := .mkObj [("ideal_rewards", .arr (ideal.map (·.toJson)).toArray),
    ("total_rewards", .arr (total.map (·.toJson)).toArray)] }

/-! ## Sync committee rewards -/

/-- What the seats of one validator in the sync committee earn or pay in a block, in Gwei.

The amount is taken before a balance stops at zero.

A negative amount is a net penalty. -/
structure SyncCommitteeReward where
  /-- The index of the validator in the registry. -/
  validatorIndex : ValidatorIndex
  /-- The net reward of its seats. -/
  reward : Int
  deriving DecidableEq, Repr

/-- Whether the reward of one member fits 64 bits. -/
def SyncCommitteeReward.fits (entry : SyncCommitteeReward) : Bool :=
  int64Fits entry.reward

/-- The JSON of the reward of one member, as the API writes it. -/
def SyncCommitteeReward.toJson (entry : SyncCommitteeReward) : Json :=
  .mkObj [("validator_index", uintJson entry.validatorIndex), ("reward", intJson entry.reward)]

/-- From Altair: the seats of the sync committee, in committee order. -/
def syncRewardSeats (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (aggregate : SyncAggregate preset) :
    Except TransitionError (List (ValidatorIndex × Bool)) := do
  -- The first validator that holds the key of each seat of the current committee.
  --
  -- A key that no validator holds is an error.
  let members ← (state.currentSyncCommittee altair).value.pubkeys.toArray.mapM
    (validatorIndexOfPubkey state)
  -- With the bit of the seat in the aggregate: set when its member signed.
  return (members.zip aggregate.syncCommitteeBits.bits.toArray).toList

/-- The net reward of one seat: the participant reward if it signed, and minus it otherwise. -/
def seatReward (reward : Gwei) (signed : Bool) : Int :=
  if signed then reward.toNat else -(reward.toNat : Int)

/-- The sum of the net rewards of the seats that a validator holds. -/
def seatsReward (reward : Gwei) (seats : List (ValidatorIndex × Bool)) (index : ValidatorIndex) :
    Int :=
  ((seats.filter (·.1 == index)).map fun seat => seatReward reward seat.2).sum

/-- From Altair: what each named member of the sync committee earned or paid in a block.

The state is the one that the sync aggregate step of the block reads. -/
def syncCommitteeRewards (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (aggregate : SyncAggregate preset) (ids : List ValidatorId) :
    Except TransitionError (List SyncCommitteeReward) := do
  let seats ← syncRewardSeats state altair aggregate
  -- The participant reward of the sync aggregate step.
  let reward ← syncParticipantReward state
  -- The members once each, in increasing order of index, EthLib's choice.
  let members := sortedSet (seats.map (·.1))
  -- The source: no array names every member, and so does an empty one here.
  --
  -- An identifier that names no member gives no entry.
  --
  -- EthLib's choice: a repeated identifier gives one entry, since the schema gives no code for it.
  --
  -- The selection is read only for a request that names validators, since it may be long.
  let named := if ids.isEmpty then members else members.filter (· ∈ selectValidators state ids)
  -- One entry per member: each seat that signed earns the reward, and each other seat pays it.
  return named.map fun index =>
    { validatorIndex := index, reward := seatsReward reward seats index }

/-- The error of a block that has no sync aggregate, before Altair, with code 400. -/
def invalidSyncRewardsRequest : ErrorMessage :=
  { code := 400, message := "Invalid request to retrieve sync committee rewards info" }

/-- The response of the sync committee rewards endpoint, without the flags of the store.

The state is the one that the sync aggregate step of the block reads, with that aggregate.

The rewards do not check the signature of the aggregate, which the block passed. -/
def syncCommitteeRewardsResponse (state : BeaconState preset fork)
    (aggregate : SyncAggregate preset) (ids : List ValidatorId) :
    Except ErrorMessage ApiEnvelope := do
  if altair : .altair ≤ fork then
    -- A failure of the rewards computation gives code 500.
    let entries ← (syncCommitteeRewards state altair aggregate ids).mapError
      fun _ => internalError "no sync committee rewards"
    -- The response types give each reward 64 bits.
    --
    -- No reward leaves that range, so this check never fails.
    ensure (entries.all (·.fits)) rewardOutOfRange
    return { data := .arr (entries.map (·.toJson)).toArray }
  -- A state before Altair, whose block has no sync aggregate: code 400 with the source's example.
  --
  -- EthLib's choice, since the source does not say what such a block gives.
  else throw invalidSyncRewardsRequest

/-! ## Block rewards -/

/-- What the proposer of a block earned in it, in Gwei, by the kind of item that paid it. -/
structure BlockRewards where
  /-- The index of the proposer in the registry. -/
  proposerIndex : ValidatorIndex
  /-- The sum of the four parts. -/
  total : Gwei
  /-- What the attestations of the block paid the proposer. -/
  attestations : Gwei
  /-- What the sync aggregate of the block paid the proposer. -/
  syncAggregate : Gwei
  /-- What the proposer slashings of the block paid the proposer. -/
  proposerSlashings : Gwei
  /-- What the attester slashings of the block paid the proposer. -/
  attesterSlashings : Gwei
  deriving DecidableEq, Repr

/-- The JSON of the block rewards, as the API writes them. -/
def BlockRewards.toJson (rewards : BlockRewards) : Json :=
  .mkObj [("proposer_index", uintJson rewards.proposerIndex), ("total", uintJson rewards.total),
    ("attestations", uintJson rewards.attestations),
    ("sync_aggregate", uintJson rewards.syncAggregate),
    ("proposer_slashings", uintJson rewards.proposerSlashings),
    ("attester_slashings", uintJson rewards.attesterSlashings)]

/-- How much the balance of a validator rose from one state to another, or zero if it did not. -/
def balanceRise (index : ValidatorIndex) (state after : BeaconState preset fork) : Gwei :=
  -- `max(after - before, 0)`, with a balance of 0 at an index past the end.
  Uint64.saturatingSub (after.balances.data.getD index.toNat 0)
    (state.balances.data.getD index.toNat 0)

/-- What the proposer of a block earned in it, from the state of the slot of the block.

A sum or product that overflows 64 bits is an error. -/
def blockRewards (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError BlockRewards := do
  let parentSlot := state.latestBlockHeader.slot
  -- The source: the proposer of the block, who receives these rewards.
  let proposer := block.proposerIndex
  let body := block.body
  -- The steps of the block before its operations.
  let start ← stateBeforeOperations config checks engine state block
  -- Then the proposer slashings, the attester slashings and the attestations, each in block order.
  let slashed ← body.proposerSlashings.data.foldlM (processProposerSlashing config checks) start
  let caught ← body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) slashed
  let attested ←
    body.attestations.data.foldlM (processAttestation config checks · parentSlot ·) caught
  -- From Altair: the proposer's share of the participant reward times the number of signatures.
  --
  -- The share is the one that the sync aggregate step computes after all the operations.
  --
  -- The step itself never runs here.
  --
  -- Before Altair the other operations never run either, and this part is zero.
  let syncAggregate ← if altair : .altair ≤ fork then do
      let operated ← processOperations config checks start body parentSlot
      let share ← syncProposerReward (← syncParticipantReward operated)
      let signed := (body.syncAggregate altair).syncCommitteeBits.bits.toArray.countP id
      liftAccessor (liftArith (mulChecked share signed.toUInt64))
    else pure 0
  -- Each other part is the rise of the proposer's balance over the operations of its kind.
  --
  -- EthLib's choice: before Altair the attestation part is zero.
  --
  -- The proposer's share for included votes is then paid at the epoch transition, not in the block.
  let proposerSlashings := balanceRise proposer start slashed
  let attesterSlashings := balanceRise proposer slashed caught
  let attestations := balanceRise proposer caught attested
  -- The types: total = attestations + sync aggregate + proposer slashings + attester slashings.
  let total ← liftAccessor (liftArith do
    addChecked (← addChecked (← addChecked attestations syncAggregate) proposerSlashings)
      attesterSlashings)
  return { proposerIndex := proposer, total, attestations, syncAggregate, proposerSlashings,
           attesterSlashings }

/-- The response of the block rewards endpoint, without the flags of the store.

The state is the one at the slot of the block, before the block. -/
def blockRewardsResponse (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except ErrorMessage ApiEnvelope := do
  -- A failure of the steps it runs, or of the sums, gives code 500, EthLib's choice.
  --
  -- The source lists 400 and 404 too, but a block that the node imported passed these steps.
  let rewards ← (blockRewards config checks engine state block).mapError
    fun _ => internalError "no block rewards"
  return { data := rewards.toJson }

end EthLib.Consensus.BeaconApi
