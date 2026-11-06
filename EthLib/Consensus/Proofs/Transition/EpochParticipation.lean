module

public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochParticipation

/-!
# Proofs: the Altair epoch steps of flags, scores and sync committees

The rotation of the flags moves the current flags to the previous epoch.

It then gives each validator an empty set of flags for the current epoch.

The sync committee update moves the next committee to the current one, only at a period's end.

The inactivity scores change nothing in the first epoch, and keep one score per entry.

None of these steps changes the size of the registry or of the balances.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- After the rotation, the previous flags are the current flags from before. -/
theorem processParticipationFlagUpdates_previous (altair : .altair ≤ fork) :
    (processParticipationFlagUpdates state altair).previousEpochParticipation altair =
      state.currentEpochParticipation altair :=
  rfl

/-- After the rotation, each validator has an empty set of flags for the current epoch. -/
theorem processParticipationFlagUpdates_current (altair : .altair ≤ fork) :
    ((processParticipationFlagUpdates state altair).currentEpochParticipation altair).data =
      Array.replicate state.validators.data.size 0 :=
  rfl

/-- The rotation keeps the sizes of the registry and the balances. -/
theorem sameSizes_processParticipationFlagUpdates (altair : .altair ≤ fork) :
    SameSizes state (processParticipationFlagUpdates state altair) :=
  SameSizes.refl state

/-- Outside the last epoch of a period, the sync committee update changes nothing. -/
theorem processSyncCommitteeUpdates_inside {altair : .altair ≤ fork} {next : Epoch}
    (nextOk : addChecked (getCurrentEpoch state) 1 = .ok next)
    (inside : next % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0) :
    processSyncCommitteeUpdates state altair = .ok state := by
  simp [processSyncCommitteeUpdates, liftAccessor, liftArith, nextOk, inside, bind, Except.bind,
    Except.mapError, pure, Except.pure]

/-- After a successful sync committee update at a period's end, the next committee is current. -/
theorem processSyncCommitteeUpdates_current {altair : .altair ≤ fork} {next : Epoch}
    (nextOk : addChecked (getCurrentEpoch state) 1 = .ok next)
    (boundary : next % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0)
    (computed : processSyncCommitteeUpdates state altair = .ok after) :
    after.currentSyncCommittee altair = state.nextSyncCommittee altair := by
  simp only [processSyncCommitteeUpdates, liftAccessor, liftArith, nextOk, boundary, bind,
    Except.bind, Except.mapError, ↓reduceIte] at computed
  split at computed
  · cases computed
  · cases computed
    rfl

/-- The sync committee update keeps the sizes of the registry and the balances. -/
theorem sameSizes_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) : SameSizes state after := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, same⟩ := computed
    subst same
    exact SameSizes.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact SameSizes.refl _

/-- One score update keeps the number of scores. -/
theorem updateInactivityScore_size {config : Config} {hit : Array Bool} {leaking : Bool}
    {scores scores' : InactivityScores preset fork} {index : ValidatorIndex}
    (computed : updateInactivityScore config hit leaking scores index = .ok scores') :
    scores'.data.size = scores.data.size := by
  unfold updateInactivityScore at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, same⟩ := computed
    subst same
    simp
  · simp [throw, throwThe, MonadExceptOf.throw] at computed

/-- In the first epoch, the inactivity scores change nothing. -/
theorem processInactivityUpdates_genesis {config : Config} (altair : .altair ≤ fork)
    (genesis : getCurrentEpoch state = GENESIS_EPOCH) :
    processInactivityUpdates config state altair = .ok state := by
  simp [processInactivityUpdates, genesis, pure, Except.pure]

/-- The inactivity scores update keeps the number of scores.

It also keeps the sizes of the registry and the balances. -/
theorem processInactivityUpdates_sizes {config : Config} {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    SameSizes state after ∧
      (after.inactivityScores altair).data.size = (state.inactivityScores altair).data.size := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨SameSizes.refl _, rfl⟩
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, scores, folded, same⟩ := computed
    subst same
    refine ⟨SameSizes.refl _, ?_⟩
    exact foldlM_ok_invariant (fun s : InactivityScores preset fork =>
      s.data.size = (state.inactivityScores altair).data.size)
      (fun _ _ _ hp step => (updateInactivityScore_size step).trans hp) rfl folded

end EthLib.Consensus
