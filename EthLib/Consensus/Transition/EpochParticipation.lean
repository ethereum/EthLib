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

The leak test is read after the first change, so an overflow there is the error that comes first.

A score past 64 bits is an error. -/
def nextInactivityScore (config : Config) (hit : Bool) (leaking : Except TransitionError Bool)
    (score : UInt64) : Except TransitionError UInt64 := do
  -- A validator that hit the target in the previous epoch loses 1, but not below 0.
  let score ← if hit then pure (saturatingSub score 1)
    -- One that missed it gains `INACTIVITY_SCORE_BIAS`.
    else liftAccessor (liftArith (addChecked score config.INACTIVITY_SCORE_BIAS))
  -- Outside a leak it then loses `INACTIVITY_SCORE_RECOVERY_RATE`, but not below 0.
  return if ← leaking then score else saturatingSub score config.INACTIVITY_SCORE_RECOVERY_RATE

/-- From Altair: the inactivity scores with the score of one eligible validator updated.

The marks of the validators that hit the target are read first, then the score. -/
def updateInactivityScore (config : Config) (hit : Except TransitionError (Array Bool))
    (leaking : Except TransitionError Bool) (scores : InactivityScores preset fork)
    (index : ValidatorIndex) : Except TransitionError (InactivityScores preset fork) := do
  let hit ← hit
  -- The score of the validator is replaced by its new score; an index past the list is an error.
  if inside : index.toNat < scores.data.size then
    let score ← nextInactivityScore config (hit.getD index.toNat false) leaking
      scores.data[index.toNat]
    return ⟨scores.data.set index.toNat score inside,
      fun before => by simpa using scores.bound before⟩
  else throw (.accessor (.indexOutOfRange index))

/-- From Altair: the state after the inactivity scores update.

The validators that hit the target and the leak test do not change during the update.

Each is computed once, and read for each validator where the update needs it.

So each of their errors arises only once an eligible validator reaches it. -/
def processInactivityUpdates (config : Config) (state : BeaconState preset fork)
    (altair : .altair ≤ fork) : Except TransitionError (BeaconState preset fork) :=
  -- The genesis epoch changes nothing, since the scores follow the previous epoch.
  if getCurrentEpoch state = GENESIS_EPOCH then pure state
  else do
    let eligible ← getEligibleValidatorIndices state
    -- The unslashed validators with the timely target flag in the previous epoch hit the target.
    let hit := liftAccessor ((getUnslashedParticipatingIndices state altair
      TIMELY_TARGET_FLAG_INDEX (getPreviousEpoch state)).map
        (markIndices state.validators.data.size))
    -- Each eligible validator updates its score, in increasing order of index.
    let scores ← eligible.foldlM (updateInactivityScore config hit (isInInactivityLeak state))
      (state.inactivityScores altair)
    return { state with inactivityScores := fun _ => scores }

/-- From Altair: the state after the rotation of the participation flags. -/
def processParticipationFlagUpdates (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    BeaconState preset fork :=
  -- The flags of the current epoch become those of the previous epoch.
  let current := state.currentEpochParticipation altair
  -- Each validator then starts the current epoch with the byte 0, no flag.
  let fresh : EpochParticipation preset fork :=
    ⟨Array.replicate state.validators.data.size 0, fun before => by
      simpa using state.validators.bound before⟩
  { state with
    previousEpochParticipation := fun _ => current
    currentEpochParticipation := fun _ => fresh }

/-- From Altair: the state after the sync committee update. -/
def processSyncCommitteeUpdates (state : BeaconState preset fork) (altair : .altair ≤ fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- The next epoch `e + 1`, an error for `e = 2^64 - 1` as for any 64-bit overflow.
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  -- When `(e + 1) mod EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0`, a new period starts.
  if nextEpoch % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 then
    -- The next committee becomes the current one.
    let next := state.nextSyncCommittee altair
    let state := { state with currentSyncCommittee := fun _ => next }
    -- Then a new next committee is drawn, from the state with that current committee.
    --
    -- The new committee is rooted once here, and keeps its root until the next period.
    let drawn := Serialization.Ssz.Rooted.of (← liftAccessor (getNextSyncCommittee state))
    return { state with nextSyncCommittee := fun _ => drawn }
  else return state

end EthLib.Consensus
