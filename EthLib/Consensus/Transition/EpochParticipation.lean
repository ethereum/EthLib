module

public import EthLib.Consensus.SyncCommittee
public import EthLib.Consensus.Transition.EpochRewards

/-!
# `Consensus.Transition.EpochParticipation`

From Altair: the epoch steps that the participation flags and the sync committees bring.

The inactivity score of a validator grows while it misses the target, and shrinks once it hits.

Outside a leak every score also shrinks by a fixed rate.

The flags of the current epoch become those of the previous epoch, and new flags start empty.

At the end of each sync committee period, the next committee becomes the current one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- From Altair: the new inactivity score of an eligible validator.

A validator that hit the target loses one point, and one that missed gains the score bias.

Outside a leak the score then loses the recovery rate.

A score never falls below zero, and a score past 64 bits is an error. -/
def nextInactivityScore (config : Config) (hit leaking : Bool) (score : UInt64) :
    Except TransitionError UInt64 := do
  let score ← if hit then pure (saturatingSub score 1)
    else liftAccessor (liftArith (addChecked score config.INACTIVITY_SCORE_BIAS))
  return if leaking then score else saturatingSub score config.INACTIVITY_SCORE_RECOVERY_RATE

/-- From Altair: the inactivity scores with the score of one eligible validator updated. -/
def updateInactivityScore (config : Config) (hit : Array Bool) (leaking : Bool)
    (scores : InactivityScores preset fork) (index : ValidatorIndex) :
    Except TransitionError (InactivityScores preset fork) := do
  let some score := scores.data[index.toNat]? | throw (.accessor (.indexOutOfRange index))
  let score ← nextInactivityScore config (hit.getD index.toNat false) leaking score
  return ⟨scores.data.set! index.toNat score, fun before => by simpa using scores.bound before⟩

/-- From Altair: the state after the inactivity scores update.

The first epoch changes nothing, since the scores follow the previous epoch.

Each eligible validator then updates its score, by whether it hit the target of that epoch. -/
def processInactivityUpdates (config : Config) (state : BeaconState preset fork)
    (altair : .altair ≤ fork) : Except TransitionError (BeaconState preset fork) :=
  if getCurrentEpoch state = GENESIS_EPOCH then pure state
  else do
    let participating ← liftAccessor (getUnslashedParticipatingIndices state altair
      TIMELY_TARGET_FLAG_INDEX (getPreviousEpoch state))
    let hit := markIndices state.validators.data.size participating
    let leaking ← isInInactivityLeak state
    let scores ← (← getEligibleValidatorIndices state).foldlM
      (updateInactivityScore config hit leaking) (state.inactivityScores altair)
    return { state with inactivityScores := fun _ => scores }

/-- From Altair: the state after the rotation of the participation flags.

The flags of the current epoch become those of the previous epoch.

Each validator then starts the current epoch with no flag. -/
def processParticipationFlagUpdates (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    BeaconState preset fork :=
  let current := state.currentEpochParticipation altair
  let fresh : EpochParticipation preset fork :=
    ⟨Array.replicate state.validators.data.size 0, fun before => by
      simpa using state.validators.bound before⟩
  { state with
    previousEpochParticipation := fun _ => current
    currentEpochParticipation := fun _ => fresh }

/-- From Altair: the state after the sync committee update.

When the next epoch starts a sync committee period, the next committee becomes the current one.

A new next committee is then drawn. -/
def processSyncCommitteeUpdates (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    Except TransitionError (BeaconState preset fork) := do
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  if nextEpoch % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 then
    let next := state.nextSyncCommittee altair
    let state := { state with currentSyncCommittee := fun _ => next }
    let drawn ← liftAccessor (getNextSyncCommittee state)
    return { state with nextSyncCommittee := fun _ => drawn }
  else return state

end EthLib.Consensus
