module

public import EthLib.Consensus.BeaconApi.Committees
public import EthLib.Consensus.BeaconApi.Registries
public import EthLib.Consensus.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochParticipation

/-!
# `Consensus.BeaconApi.Rewards`

The answers of the Beacon API that split the rewards of validators into their parts.

The [attestation rewards] of an epoch give, for each validator, what each kind of vote earned.

They are read from the state at the end of the next epoch, whose previous epoch is the one asked.

The epoch transition first updates justification and, from Altair, the inactivity scores.

Each part is then the reward minus the penalty that the transition computes for that kind.

Before Altair the inclusion part leaves out the shares that a proposer earns for including votes.

The ideal rewards give the same parts for a validator that voted right and in time.

The response [types] fix the fields of each answer.

SOUNDNESS.md records the points that the source leaves open.

[attestation rewards]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/rewards/attestations.yaml
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
  let fault (error : TransitionError) := internalError (reprStr error)
  let state ← (stateBeforeRewards config state).mapError fault
  let ideal ← (idealAttestationRewards state).mapError fault
  let total ← (attestationRewards config state ids).mapError fault
  return { data := .mkObj [("ideal_rewards", .arr (ideal.map (·.toJson)).toArray),
    ("total_rewards", .arr (total.map (·.toJson)).toArray)] }

end EthLib.Consensus.BeaconApi
