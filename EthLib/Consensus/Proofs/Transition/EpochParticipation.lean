module

public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Transition.EpochParticipation

/-!
# Proofs: the Altair epoch steps of flags, scores and sync committees

The rotation of the flags moves the current flags to the previous epoch.

It then gives each validator an empty set of flags for the current epoch.

The sync committee update moves the next committee to the current one, only at a period's end.

There it stores as the next committee a draw from the state with that new current committee.

The inactivity scores change nothing in the first epoch, and keep one score per entry.

After the first epoch, each eligible validator gets its next score, and the other scores stay.

An unslashed validator that set the target flag in the previous epoch loses one point.

The other eligible validators gain the score bias.

Outside a leak each of those scores then loses the recovery rate, stopping at zero.

The value of each score needs a registry within its limit.

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

/-- After a successful sync committee update at a period's end, the next committee is a new draw.

The draw reads the state whose current committee is already the old next committee. -/
theorem processSyncCommitteeUpdates_next {altair : .altair ≤ fork}
    (boundary : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0)
    (computed : processSyncCommitteeUpdates state altair = .ok after) :
    getNextSyncCommittee
        { state with currentSyncCommittee := fun _ => state.nextSyncCommittee altair } =
      .ok (after.nextSyncCommittee altair).value := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨epoch, epochOk, computed⟩ := computed
  -- The next epoch that the update computes is the wrapping sum, since the update succeeds.
  rw [liftArith, mapError_ok_iff, addChecked_ok_iff] at epochOk
  have sum : epoch = getCurrentEpoch state + 1 :=
    UInt64.toNat_inj.mp (epochOk.2.trans (toNat_add_of_lt epochOk.1).symm)
  subst sum
  simp only [boundary, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨drawn, drawnOk, same⟩ := computed
  subst same
  exact drawnOk

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
theorem updateInactivityScore_size {config : Config} {hit : Except TransitionError (Array Bool)}
    {leaking : Except TransitionError Bool} {scores scores' : InactivityScores preset fork}
    {index : ValidatorIndex}
    (computed : updateInactivityScore config hit leaking scores index = .ok scores') :
    scores'.data.size = scores.data.size := by
  simp only [updateInactivityScore, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
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
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, scores, folded, same⟩ := computed
    subst same
    refine ⟨SameSizes.refl _, ?_⟩
    exact foldlM_ok_invariant (fun s : InactivityScores preset fork =>
      s.data.size = (state.inactivityScores altair).data.size)
      (fun _ _ _ hp step => (updateInactivityScore_size step).trans hp) rfl folded

/-! ## The value of each inactivity score -/

/-- Take a score update that succeeds, with a leak test that has a result.

A hit loses one point, and a miss gains the score bias.

Outside a leak the score then loses the recovery rate.

Each subtraction stops at zero. -/
theorem nextInactivityScore_toNat {config : Config} {hit leak : Bool} {score score' : UInt64}
    (computed : nextInactivityScore config hit (.ok leak) score = .ok score') :
    score'.toNat = (if hit then score.toNat - 1
        else score.toNat + config.INACTIVITY_SCORE_BIAS.toNat) -
      if leak then 0 else config.INACTIVITY_SCORE_RECOVERY_RATE.toNat := by
  unfold nextInactivityScore at computed
  cases hit
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨changed, first, _, same, computed⟩ := computed
    cases same
    simp only [liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at first
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    cases leak
    · simp only [Bool.false_eq_true, ↓reduceIte, toNat_saturatingSub, first.2]
    · simp only [↓reduceIte, Bool.false_eq_true, Nat.sub_zero, first.2]
  · simp only [↓reduceIte, bind_ok_iff] at computed
    obtain ⟨changed, first, _, same, computed⟩ := computed
    cases same
    simp only [pure, Except.pure, Except.ok.injEq] at first computed
    subst first computed
    cases leak
    · simp only [Bool.false_eq_true, ↓reduceIte, toNat_saturatingSub, UInt64.toNat_one]
    · simp only [↓reduceIte, Nat.sub_zero, toNat_saturatingSub, UInt64.toNat_one]

/-- A score update that succeeds has a result for the leak test. -/
theorem nextInactivityScore_leak {config : Config} {hit : Bool}
    {leaking : Except TransitionError Bool} {score score' : UInt64}
    (computed : nextInactivityScore config hit leaking score = .ok score') :
    ∃ leak, leaking = .ok leak := by
  cases leaking with
  | ok leak => exact ⟨leak, rfl⟩
  | error failure =>
    unfold nextInactivityScore at computed
    split at computed
    all_goals
      simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, absurd, _⟩ := computed
      cases absurd

/-- One score update sets the score of its validator from its mark and the leak test.

The other scores stay. -/
private theorem updateInactivityScore_getElem? {config : Config}
    {hit : Except TransitionError (Array Bool)} {leaking : Except TransitionError Bool}
    {scores scores' : InactivityScores preset fork} {index : ValidatorIndex}
    (computed : updateInactivityScore config hit leaking scores index = .ok scores') :
    (∃ marks score score', hit = .ok marks ∧ scores.data[index.toNat]? = some score ∧
      nextInactivityScore config (marks.getD index.toNat false) leaking score = .ok score' ∧
      scores'.data[index.toNat]? = some score') ∧
    ∀ j, j ≠ index.toNat → scores'.data[j]? = scores.data[j]? := by
  simp only [updateInactivityScore, bind_ok_iff] at computed
  obtain ⟨marks, marked, computed⟩ := computed
  split at computed
  · rename_i inside
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨score', next, rfl⟩ := computed
    refine ⟨⟨marks, scores.data[index.toNat], score', marked, by simp [inside], next, by simp⟩,
      fun j other => ?_⟩
    simp [Ne.symm other]
  · simp [throw, throwThe, MonadExceptOf.throw] at computed

/-- A validator is marked exactly when it is unslashed and set the flag in the given epoch. -/
private theorem getD_markIndices_iff {flagIndex : UInt64} {epoch : Epoch}
    {altair : .altair ≤ fork} {participating : List ValidatorIndex}
    (computed : getUnslashedParticipatingIndices state altair flagIndex epoch = .ok participating)
    (index : ValidatorIndex) :
    (markIndices state.validators.data.size participating).getD index.toNat false = true ↔
      index ∈ participating := by
  rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
  constructor
  · intro marked
    split at marked
    · simp only [Option.getD_some, List.any_eq_true, beq_iff_eq] at marked
      obtain ⟨other, member, same⟩ := marked
      rwa [← UInt64.toNat_inj.mp same]
    · simp at marked
  · intro member
    obtain ⟨-, ⟨validator, found, -⟩, -⟩ :=
      mem_getUnslashedParticipatingIndices computed index member
    have inside : index.toNat < state.validators.data.size := by
      unfold getValidator at found
      split at found
      · rename_i read
        exact (Array.getElem?_eq_some_iff.mp read).1
      · cases found
    simp only [inside, ↓reduceIte, Option.getD_some, List.any_eq_true, beq_iff_eq]
    exact ⟨index, member, rfl⟩

/-- From Altair and after the first epoch, take an update of the inactivity scores that succeeds.

Each eligible validator gets its next score.

That depends on whether it is unslashed and set the target flag in the previous epoch.

A hit loses one point, and a miss gains the score bias.

Outside a leak the score then loses the recovery rate, stopping at zero.

The other scores stay.

That needs a registry within its limit. -/
theorem processInactivityUpdates_scores {config : Config} {altair : .altair ≤ fork}
    (within : state.RegistryWithinLimit) (later : getCurrentEpoch state ≠ GENESIS_EPOCH)
    (computed : processInactivityUpdates config state altair = .ok after) :
    ∃ eligible, getEligibleValidatorIndices state = .ok eligible ∧
      (∀ i, (∀ index ∈ eligible, index.toNat ≠ i) →
        (after.inactivityScores altair).data[i]? = (state.inactivityScores altair).data[i]?) ∧
      ∀ index ∈ eligible, ∃ hitters leak score score',
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
            (getPreviousEpoch state) = .ok hitters ∧
          isInInactivityLeak state = .ok leak ∧
          (state.inactivityScores altair).data[index.toNat]? = some score ∧
          (after.inactivityScores altair).data[index.toNat]? = some score' ∧
          score'.toNat = (if index ∈ hitters then score.toNat - 1
              else score.toNat + config.INACTIVITY_SCORE_BIAS.toNat) -
            if leak then 0 else config.INACTIVITY_SCORE_RECOVERY_RATE.toNat := by
  unfold processInactivityUpdates at computed
  simp only [later, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨eligible, listed, scores, folded, rfl⟩ := computed
  -- The eligible indices name each validator once, so the fold sets each eligible score once.
  have distinct := (getEligibleValidatorIndices_ok within listed).1
  have entry (j : Nat) := foldlM_entry (entry := fun scores : InactivityScores preset fork =>
    scores.data[j]?) (j := j)
    (fun _ _ _ step other => (updateInactivityScore_getElem? step).2 j (Ne.symm other))
    distinct folded
  refine ⟨eligible, listed, fun j absent => (entry j).1 absent, fun index member => ?_⟩
  obtain ⟨last, stepped, start, step, result⟩ := (entry index.toNat).2 index member rfl
  obtain ⟨marks, score, score', marked, found, next, set⟩ :=
    (updateInactivityScore_getElem? step).1
  rw [start] at found
  rw [set] at result
  -- The marks are the unslashed validators that set the target flag in the previous epoch.
  have mapped := liftAccessor_ok.mp marked
  obtain ⟨hitters, hit⟩ : ∃ hitters, getUnslashedParticipatingIndices state altair
      TIMELY_TARGET_FLAG_INDEX (getPreviousEpoch state) = .ok hitters := by
    cases participation : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (getPreviousEpoch state) with
    | error failure =>
      rw [participation] at mapped
      cases mapped
    | ok hitters => exact ⟨hitters, rfl⟩
  rw [hit] at mapped
  have same : markIndices state.validators.data.size hitters = marks := by
    simpa [Except.map] using mapped
  subst same
  obtain ⟨leak, leaking⟩ := nextInactivityScore_leak next
  rw [leaking] at next
  refine ⟨hitters, leak, score, score', hit, leaking, found, result, ?_⟩
  rw [nextInactivityScore_toNat next]
  by_cases member' : index ∈ hitters
  · simp only [(getD_markIndices_iff hit index).mpr member', member', ↓reduceIte]
  · have unmarked :
        (markIndices state.validators.data.size hitters).getD index.toNat false = false := by
      cases marking : (markIndices state.validators.data.size hitters).getD index.toNat false
      · rfl
      · exact absurd ((getD_markIndices_iff hit index).mp marking) member'
    simp only [unmarked, member', Bool.false_eq_true, ↓reduceIte]

end EthLib.Consensus
