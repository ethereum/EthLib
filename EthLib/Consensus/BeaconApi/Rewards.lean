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

They are read from the state at the end of the next epoch, whose previous epoch is the one asked.

The epoch transition first updates justification and, from Altair, the inactivity scores.

Each part is then the reward minus the penalty that the transition computes for that kind.

Before Altair the inclusion part leaves out the shares that a proposer earns for including votes.

The ideal rewards give the same parts for a validator that voted right and in time.

The [sync committee rewards] of a block give, for each member, what its seats earned or paid.

They are read from the state that the sync aggregate step of the block reads.

The [block rewards] give what the proposer of a block earned in it, by the kind of item that paid.

Each other part is the rise of the proposer's balance in the step of the block that pays it.

The sync aggregate part is the proposer's share of each signature, which the step computes.

The response [types] fix the fields of each answer.

SOUNDNESS.md records the points that the source leaves open.

[attestation rewards]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/rewards/attestations.yaml
[block rewards]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/rewards/blocks.yaml
[sync committee rewards]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/rewards/sync_committee.yaml
[types]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/rewards.yaml
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

/-- The fields of the inclusion reward, present only when there is one. -/
def inclusionDelayJson (reward : Option Gwei) : List (String × Json) :=
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
  ((deltas.1.getD position 0).toNat : Int) - (deltas.2.getD position 0).toNat

/-- Before Altair: the inclusion reward of each attester of the previous epoch, at its position.

It is the part of the inclusion deltas that goes to the attester, without the proposer shares. -/
def attesterInclusionRewards (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei) := do
  let size := state.validators.data.size
  let attestations ← getMatchingSourceAttestations state before (getPreviousEpoch state)
  let signers ← liftAccessor (attestations.toList.mapM (getPendingAttestingIndices state))
  let attesters ← liftAccessor (unslashedAmong state signers)
  let total ← liftAccessor (getTotalActiveBalance state)
  let earliest := earliestInclusions size (attestations.zip signers.toArray)
  attesters.foldlM (init := Array.replicate size 0) fun rewards index => do
    let some attestation := earliest.getD index.toNat none
      | throw (.accessor (.indexOutOfRange index))
    let base ← liftAccessor (getBaseReward state total index)
    addDelta rewards index (← inclusionAttesterReward preset base attestation.inclusionDelay)

/-- What each kind of vote earned for each named validator in the previous epoch of a state.

The state is the one that the rewards step of the epoch transition reads.

From Altair the parts are the deltas of the three flags, in the order the transition applies them.

Before Altair they are the deltas of the source, target and head votes.

The inclusion part is then the attester's own part of the inclusion deltas.

The inactivity part is the penalty of the inactivity deltas, which hold no reward.

An empty request names every validator; an identifier that names none gives no entry. -/
def attestationRewards (config : Config) (state : BeaconState preset fork)
    (ids : List ValidatorId) : Except TransitionError (List AttestationRewards) := do
  let indices := selectValidators state ids
  let inactivity ← getInactivityPenaltyDeltas config state
  if altair : .altair ≤ fork then
    let flags ← (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
      (getFlagIndexDeltas state altair)
    let flag (flagIndex : UInt64) (position : Nat) :=
      netDelta (flags.getD flagIndex.toNat (#[], #[])) position
    return indices.map fun index =>
      { validatorIndex := index, head := flag TIMELY_HEAD_FLAG_INDEX index.toNat,
        target := flag TIMELY_TARGET_FLAG_INDEX index.toNat,
        source := flag TIMELY_SOURCE_FLAG_INDEX index.toNat, inclusionDelay := none,
        inactivity := -((inactivity.2.getD index.toNat 0).toNat : Int) }
  else
    have before := Nat.lt_of_not_le altair
    let source ← getSourceDeltas state before
    let target ← getTargetDeltas state before
    let head ← getHeadDeltas state before
    let inclusion ← attesterInclusionRewards state before
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
  let eligible ← getEligibleValidatorIndices state
  let firsts ← eligible.foldlM (init := ([] : List (Gwei × ValidatorIndex))) fun found index => do
    let balance := (← liftAccessor (getValidator state index)).effectiveBalance
    if found.any (·.1 == balance) then return found else return found ++ [(balance, index)]
  return firsts.mergeSort fun a b => a.1.toNat ≤ b.1.toNat

/-- The total effective balance of the unslashed validators of some pending attestations. -/
def attestingBalance (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) : Except TransitionError Gwei :=
  liftAccessor do getTotalBalance state (← getUnslashedAttestingIndices state attestations)

/-- From Altair: the reward of one flag for an eligible validator that set it.

It is what the transition gives a validator that set it, at the participation of the epoch. -/
def idealFlagReward (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) (index : ValidatorIndex) :
    Except TransitionError Gwei := do
  let size := state.validators.data.size
  let participating ← liftAccessor (getUnslashedParticipatingIndices state altair
    flagIndex.val.toUInt64 (getPreviousEpoch state))
  let participatingBalance ← liftAccessor (getTotalBalance state participating)
  let total ← liftAccessor (getTotalActiveBalance state)
  let increment := preset.EFFECTIVE_BALANCE_INCREMENT
  let zeros : Array Gwei := Array.replicate size 0
  let (rewards, _) ← addFlagDelta state flagIndex (Array.replicate size true) total
    (participatingBalance / increment) (total / increment) (zeros, zeros) index
  return rewards.getD index.toNat 0

/-- Before Altair: the reward of one kind of vote for an eligible validator whose vote matched. -/
def idealComponentReward (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) (index : ValidatorIndex) :
    Except TransitionError Gwei := do
  let total ← liftAccessor (getTotalActiveBalance state)
  let base ← liftAccessor (getBaseReward state total index)
  return (← componentDelta state true base (← attestingBalance state attestations) total).1

/-- Before Altair: the inactivity penalty of an eligible validator whose target vote matched.

Outside a leak there is none. -/
def idealInactivityPenalty (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except TransitionError Gwei := do
  if ← isInInactivityLeak state then
    let size := state.validators.data.size
    let total ← liftAccessor (getTotalActiveBalance state)
    let penalties ← addInactivityPenalty state total (← getFinalityDelay state)
      (Array.replicate size true) (Array.replicate size 0) index
    return penalties.getD index.toNat 0
  else return 0

/-- The rewards of an eligible validator of some effective balance that voted right and in time.

Its votes match the source, the target and the head, so it pays no penalty for them.

Before Altair it is included one slot after its vote, and in a leak it pays an inactivity penalty.

From Altair it set every flag, so it pays no inactivity penalty. -/
def idealRewardsOf (state : BeaconState preset fork) (balance : Gwei) (index : ValidatorIndex) :
    Except TransitionError IdealAttestationRewards := do
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
    let inclusion ← inclusionAttesterReward preset base 1
    return { effectiveBalance := balance,
             head := ← component (← getMatchingHeadAttestations state before previous),
             target := ← component (← getMatchingTargetAttestations state before previous),
             source := ← component (← getMatchingSourceAttestations state before previous),
             inclusionDelay := some inclusion,
             inactivity := -((← idealInactivityPenalty state index).toNat : Int) }

/-- The ideal rewards of each effective balance of the eligible validators, in increasing order. -/
def idealAttestationRewards (state : BeaconState preset fork) :
    Except TransitionError (List IdealAttestationRewards) := do
  (← idealBalances state).mapM fun (balance, index) => idealRewardsOf state balance index

/-! ## Response -/

/-- The state that the rewards step of the epoch transition reads, from the state it starts from.

Justification and finalization come first, then from Altair the inactivity scores. -/
def stateBeforeRewards (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let state ← processJustificationAndFinalization state
  if altair : .altair ≤ fork then processInactivityUpdates config state altair else pure state

/-- The error of an epoch that the state does not hold the rewards of, with code 404. -/
def epochNotKnown (epoch : Epoch) : ErrorMessage :=
  { code := 404, message := s!"Epoch {epoch.toNat} not known or required data not available" }

/-- The response of the attestation rewards endpoint, without the flags that come from the store.

A state at the last slot of an epoch past the first answers only for the epoch before.

It holds every vote of that epoch that the transition rewards.

The parts are read after the steps of the epoch transition that come before the rewards.

Any other epoch, or a state at another slot, gives the error with code 404.

A failure of the rewards computation gives the error with code 500. -/
def attestationRewardsResponse (config : Config) (state : BeaconState preset fork)
    (epoch : Epoch) (ids : List ValidatorId) : Except ErrorMessage ApiEnvelope := do
  if getCurrentEpoch state = GENESIS_EPOCH ∨ getPreviousEpoch state ≠ epoch ∨
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 then
    throw (epochNotKnown epoch)
  let fault (_ : TransitionError) := internalError "no attestation rewards"
  let state ← (stateBeforeRewards config state).mapError fault
  let ideal ← (idealAttestationRewards state).mapError fault
  let total ← (attestationRewards config state ids).mapError fault
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

/-- The JSON of the reward of one member, as the API writes it. -/
def SyncCommitteeReward.toJson (entry : SyncCommitteeReward) : Json :=
  .mkObj [("validator_index", uintJson entry.validatorIndex), ("reward", intJson entry.reward)]

/-- From Altair: the seats of the sync committee, in committee order.

Each seat gives the first validator that holds the key of the seat, and whether its bit is set.

A key that no validator holds is an error. -/
def syncRewardSeats (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (aggregate : SyncAggregate preset) :
    Except TransitionError (List (ValidatorIndex × Bool)) := do
  let members ← (state.currentSyncCommittee altair).value.pubkeys.toArray.mapM
    (validatorIndexOfPubkey state)
  return (members.zip aggregate.syncCommitteeBits.bits.toArray).toList

/-- The net reward of one seat: the participant reward if it signed, and minus it otherwise. -/
def seatReward (reward : Gwei) (signed : Bool) : Int :=
  if signed then reward.toNat else -(reward.toNat : Int)

/-- The sum of the net rewards of the seats that a validator holds. -/
def seatsReward (reward : Gwei) (seats : List (ValidatorIndex × Bool)) (index : ValidatorIndex) :
    Int :=
  ((seats.filter (·.1 == index)).map fun seat => seatReward reward seat.2).sum

/-- From Altair: what each named member of the sync committee earned or paid in a block.

The state is the one that the sync aggregate step of the block reads.

Each seat that signed earns the participant reward of that step, and each other seat pays it.

A validator with several seats gets one entry, with the sum of its seats.

The entries are in increasing order of index.

An empty request names every member; an identifier that names no member gives no entry.

A repeated identifier gives one entry. -/
def syncCommitteeRewards (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (aggregate : SyncAggregate preset) (ids : List ValidatorId) :
    Except TransitionError (List SyncCommitteeReward) := do
  let seats ← syncRewardSeats state altair aggregate
  let reward ← syncParticipantReward state
  let members := sortedSet (seats.map (·.1))
  -- The selection is read only for a request that names validators, since it may be long.
  let named := if ids.isEmpty then members else members.filter (· ∈ selectValidators state ids)
  return named.map fun index =>
    { validatorIndex := index, reward := seatsReward reward seats index }

/-- The error of a block that has no sync aggregate, before Altair, with code 400. -/
def invalidSyncRewardsRequest : ErrorMessage :=
  { code := 400, message := "Invalid request to retrieve sync committee rewards info" }

/-- The response of the sync committee rewards endpoint, without the flags of the store.

The state is the one that the sync aggregate step of the block reads, with that aggregate.

The rewards do not check the signature of the aggregate, which the block passed.

A state before Altair gives the error with code 400.

A failure of the rewards computation gives the error with code 500. -/
def syncCommitteeRewardsResponse (state : BeaconState preset fork)
    (aggregate : SyncAggregate preset) (ids : List ValidatorId) :
    Except ErrorMessage ApiEnvelope := do
  if altair : .altair ≤ fork then
    let entries ← (syncCommitteeRewards state altair aggregate ids).mapError
      fun _ => internalError "no sync committee rewards"
    return { data := .arr (entries.map (·.toJson)).toArray }
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
  Uint64.saturatingSub (after.balances.data.getD index.toNat 0)
    (state.balances.data.getD index.toNat 0)

/-- What the proposer of a block earned in it, from the state of the slot of the block.

The state runs the steps of the block before its operations, and the operations in their order.

Each slashing part is the rise of the proposer's balance over the slashings of its kind.

The attestation part is the rise over the attestations, which pay nothing before Altair.

From Altair the sync aggregate part is the proposer's share times the number of signatures.

That share is the one that the sync aggregate step computes after the operations.

Before Altair only the three kinds of operations above run.

The sync aggregate step itself never runs.

A sum or product that overflows 64 bits is an error. -/
def blockRewards (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except TransitionError BlockRewards := do
  let parentSlot := state.latestBlockHeader.slot
  let proposer := block.proposerIndex
  let body := block.body
  let start ← stateBeforeOperations config checks engine state block
  let slashed ← body.proposerSlashings.data.foldlM (processProposerSlashing config checks) start
  let caught ← body.attesterSlashings.data.foldlM (processAttesterSlashing config checks) slashed
  let attested ←
    body.attestations.data.foldlM (processAttestation config checks · parentSlot ·) caught
  let syncAggregate ← if altair : .altair ≤ fork then do
      let operated ← processOperations config checks start body parentSlot
      let share ← syncProposerReward (← syncParticipantReward operated)
      let signed := (body.syncAggregate altair).syncCommitteeBits.bits.toArray.countP id
      liftAccessor (liftArith (mulChecked share signed.toUInt64))
    else pure 0
  let proposerSlashings := balanceRise proposer start slashed
  let attesterSlashings := balanceRise proposer slashed caught
  let attestations := balanceRise proposer caught attested
  let total ← liftAccessor (liftArith do
    addChecked (← addChecked (← addChecked attestations syncAggregate) proposerSlashings)
      attesterSlashings)
  return { proposerIndex := proposer, total, attestations, syncAggregate, proposerSlashings,
           attesterSlashings }

/-- The response of the block rewards endpoint, without the flags of the store.

The state is the one at the slot of the block, before the block.

A failure of the steps it runs, or of the sums, gives the error with code 500. -/
def blockRewardsResponse (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Except ErrorMessage ApiEnvelope := do
  let rewards ← (blockRewards config checks engine state block).mapError
    fun _ => internalError "no block rewards"
  return { data := rewards.toJson }

end EthLib.Consensus.BeaconApi
