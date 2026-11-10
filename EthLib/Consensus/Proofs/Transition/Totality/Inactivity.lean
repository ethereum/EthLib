module

public import EthLib.Consensus.Proofs.Transition.EpochParticipation
public import EthLib.Consensus.Proofs.Transition.Totality.Justification

/-!
# Proofs: the update of the inactivity scores succeeds

From Altair the step lists the eligible validators.

It also lists those that hit the target of the previous epoch.

It tests for a leak, which subtracts the finalized epoch from the previous epoch.

Each eligible validator that missed the target then gains the score bias, with a checked sum.

The step succeeds when each score plus the bias fits in 64 bits.

The registry must stay within its limit, so that each position is a validator index.

The lists of scores and of flags must have one entry for each validator.

The finalized epoch must be at most the previous epoch, so that the subtraction succeeds.

The invariant gives it before justification and finalization, and that step keeps it.

The invariant itself may fail after that step, which can justify the current epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- Each validator is eligible or not, without an error, in the previous epoch. -/
private theorem isEligibleValidator_exists_ok (validator : Validator) :
    ∃ decided, isEligibleValidator (getPreviousEpoch state) validator = .ok decided := by
  have le := getPreviousEpoch_toNat state
  have lt := (getCurrentEpoch state).toNat_lt
  have sum : (getPreviousEpoch state).toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    simp only [UInt64.toNat_one]
    omega
  unfold isEligibleValidator
  split
  · exact ⟨_, rfl⟩
  · split
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure]
      exact ⟨_, _, by rw [liftArith, addChecked_of_lt sum]; rfl, rfl⟩
    · exact ⟨_, rfl⟩

/-- For a registry within its limit, the eligible validators are listed without an error. -/
theorem getEligibleValidatorIndices_exists_ok (within : state.RegistryWithinLimit) :
    ∃ eligible, getEligibleValidatorIndices state = .ok eligible := by
  unfold getEligibleValidatorIndices
  refine filterMapM_ok_of_forall fun ⟨validator, position⟩ member => ?_
  have inside : position < state.validators.data.size := by
    have := (List.mem_zipIdx_iff_getElem?.mp member)
    simpa [Array.getElem?_eq_some_iff] using (Array.getElem?_eq_some_iff.mp (by simpa using this)).1
  have bound : state.validators.data.size ≤ _ := within
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  obtain ⟨decided, ok⟩ := isEligibleValidator_exists_ok (state := state) validator
  simp only [bind_ok_iff, ok]
  cases decided
  · exact ⟨none, _, rfl, rfl⟩
  · refine ⟨some position.toUInt64, true, rfl, ?_⟩
    have conv : liftAccessor (liftArith (ofNatChecked position)) = .ok position.toUInt64 := by
      rw [liftAccessor_ok, liftArith, mapError_ok_iff, ofNatChecked_of_lt (by omega)]
    simp [conv, pure, Except.pure, bind, Except.bind]

/-- A score below the room left by the bias gets a next score. -/
private theorem nextInactivityScore_exists_ok (config : Config) (hit leaking : Bool)
    (score : UInt64) (fits : score.toNat + config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64) :
    ∃ next, nextInactivityScore config hit (.ok leaking) score = .ok next := by
  unfold nextInactivityScore
  cases hit
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure]
    refine ⟨_, score + config.INACTIVITY_SCORE_BIAS,
      (by rw [liftArith, mapError_ok_iff, addChecked_of_lt fits]), leaking, rfl, rfl⟩
  · simp only [↓reduceIte, bind_ok_iff, pure, Except.pure]
    exact ⟨_, _, rfl, leaking, rfl, rfl⟩

/-- A score update at an index with room succeeds, and touches only its own entry. -/
private theorem updateInactivityScore_exists_ok (config : Config) {hit : Array Bool}
    {leaking : Bool} (scores : InactivityScores preset fork) (index : ValidatorIndex)
    (inside : index.toNat < scores.data.size)
    (fits : scores.data[index.toNat].toNat + config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64) :
    ∃ next, updateInactivityScore config (.ok hit) (.ok leaking) scores index = .ok next ∧
      next.data.size = scores.data.size ∧
        ∀ j (h : j < scores.data.size) (h' : j < next.data.size), j ≠ index.toNat →
          next.data[j] = scores.data[j] := by
  obtain ⟨score, scored⟩ := nextInactivityScore_exists_ok config (hit.getD index.toNat false)
    leaking _ fits
  refine ⟨⟨scores.data.set index.toNat score inside,
    fun before => by simpa using scores.bound before⟩, ?_, by simp,
    fun j h h' ne => by simp [Array.getElem_set, Ne.symm ne]⟩
  simp only [updateInactivityScore, bind_ok_iff]
  refine ⟨_, rfl, ?_⟩
  simp only [inside, ↓reduceDIte]
  simp only [pure, Except.pure, bind, Except.bind, scored]

/-- A fold of score updates over distinct indices with room succeeds. -/
private theorem foldlM_updateInactivityScore_exists_ok (config : Config) {hit : Array Bool}
    {leaking : Bool} :
    ∀ (indices : List ValidatorIndex) (scores : InactivityScores preset fork),
      (indices.map UInt64.toNat).Nodup →
      (∀ index ∈ indices, ∃ inside : index.toNat < scores.data.size,
        scores.data[index.toNat].toNat + config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64) →
      ∃ out, indices.foldlM (updateInactivityScore config (.ok hit) (.ok leaking)) scores =
        .ok out
  | [], scores, _, _ => ⟨scores, rfl⟩
  | first :: rest, scores, distinct, room => by
    rw [List.map_cons, List.nodup_cons] at distinct
    obtain ⟨inside, fits⟩ := room first List.mem_cons_self
    obtain ⟨next, stepped, same, keeps⟩ :=
      updateInactivityScore_exists_ok config (hit := hit) (leaking := leaking) scores first inside
        fits
    obtain ⟨out, folded⟩ := foldlM_updateInactivityScore_exists_ok config rest next distinct.2
      (fun index member => by
        have ne : index.toNat ≠ first.toNat := fun eq =>
          distinct.1 (eq ▸ List.mem_map_of_mem member)
        obtain ⟨insideOld, fitsOld⟩ := room index (List.mem_cons_of_mem _ member)
        have insideNew : index.toNat < next.data.size := same ▸ insideOld
        exact ⟨insideNew, by rw [keeps _ insideOld insideNew ne]; exact fitsOld⟩)
    exact ⟨out, by rw [List.foldlM_cons, stepped]; exact folded⟩

/-- Each eligible index is a position of the registry. -/
theorem getEligibleValidatorIndices_lt {eligible : List ValidatorIndex}
    (within : state.RegistryWithinLimit)
    (computed : getEligibleValidatorIndices state = .ok eligible) :
    ∀ index ∈ eligible, index.toNat < state.validators.data.size := by
  intro index member
  rw [getEligibleValidatorIndices_eq computed, List.mem_filterMap] at member
  obtain ⟨⟨validator, k⟩, listed, image⟩ := member
  have inside : k < state.validators.data.size := by
    have := List.mem_zipIdx_iff_getElem?.mp listed
    exact (Array.getElem?_eq_some_iff.mp (by simpa using this)).1
  dsimp only at image
  split at image
  · split at image
    · obtain rfl := Option.some.inj image
      rw [toNat_toUInt64_of_lt within inside]
      exact inside
    · simp at image
  · simp at image

/-- The finalized epoch is at most the previous epoch. -/
def FinalizedSettled (state : BeaconState preset fork) : Prop :=
  state.finalizedCheckpoint.epoch ≤ getPreviousEpoch state

/-- Justification and finalization leave the finalized epoch at most the previous epoch.

The checkpoints must be in order before, and the current justified one at most the previous epoch.

The new finalized checkpoint is then the old one or one of the two old justified ones. -/
theorem processJustificationAndFinalization_finalizedSettled {after : BeaconState preset fork}
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    (computed : processJustificationAndFinalization state = .ok after) :
    FinalizedSettled after := by
  have first := UInt64.le_trans ordered.1 (UInt64.le_trans ordered.2 settled)
  have second := UInt64.le_trans ordered.2 settled
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact first
  · obtain ⟨_, _, finalized, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    have slot : after.slot = state.slot := by rw [← rest]
    unfold FinalizedSettled getPreviousEpoch getCurrentEpoch at *
    rw [slot]
    rcases finalized with same | same | same
    · rw [same]
      exact first
    · rw [same]
      exact second
    · rw [same]
      exact settled

/-- Justification and finalization leave the inactivity scores as they are. -/
theorem processJustificationAndFinalization_inactivityScores {after : BeaconState preset fork}
    (computed : processJustificationAndFinalization state = .ok after) :
    after.inactivityScores = state.inactivityScores := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]

/-- The delay of finality is the previous epoch less the finalized one, without an error.

The finalized epoch must be at most the previous epoch. -/
theorem getFinalityDelay_eq_ok (finalized : FinalizedSettled state) :
    getFinalityDelay state = .ok (getPreviousEpoch state - state.finalizedCheckpoint.epoch) :=
  getFinalityDelay_ok_iff.mpr
    ⟨UInt64.le_iff_toNat_le.mp finalized, UInt64.toNat_sub_of_le _ _ finalized⟩

/-- The test for a leak compares the delay of finality to its threshold, without an error.

The finalized epoch must be at most the previous epoch. -/
theorem isInInactivityLeak_eq_ok (finalized : FinalizedSettled state) :
    isInInactivityLeak state = .ok (preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY <
      getPreviousEpoch state - state.finalizedCheckpoint.epoch) := by
  simp only [isInInactivityLeak, getFinalityDelay_eq_ok finalized]
  rfl

/-- From Altair, the update of the inactivity scores succeeds under bounds.

The registry must stay within its limit.

The finalized epoch must be at most the previous epoch.

The lists of scores and of flags must have one entry for each validator.

Each score plus the score bias must be below 2^64.

A score grows only when its validator missed the target, by the bias, so this bound is enough. -/
theorem processInactivityUpdates_total (config : Config) (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit) (finalized : FinalizedSettled state)
    (scored : InactivityScoresMatch state) (sized : ParticipationMatches state)
    (fits : ∀ score ∈ (state.inactivityScores altair).data,
      score.toNat + config.INACTIVITY_SCORE_BIAS.toNat < 2 ^ 64) :
    ∃ after, processInactivityUpdates config state altair = .ok after := by
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · exact ⟨state, processInactivityUpdates_genesis altair genesis⟩
  obtain ⟨eligible, eligibleOk⟩ := getEligibleValidatorIndices_exists_ok within
  obtain ⟨hits, hitsOk, _⟩ := getUnslashedParticipatingIndices_exists_ok within altair
    TIMELY_TARGET_FLAG_INDEX (Or.inl rfl) sized
  have leakOk := isInInactivityLeak_eq_ok finalized
  have distinct := (getEligibleValidatorIndices_ok within eligibleOk).1
  have inRange := getEligibleValidatorIndices_lt within eligibleOk
  obtain ⟨scores, folded⟩ := foldlM_updateInactivityScore_exists_ok config
    (hit := markIndices state.validators.data.size hits) (leaking := _) eligible
    (state.inactivityScores altair) distinct fun index member =>
      ⟨by rw [scored altair]; exact inRange index member,
        fits _ (Array.getElem_mem _)⟩
  refine ⟨{ state with inactivityScores := fun _ => scores }, ?_⟩
  unfold processInactivityUpdates
  simp only [genesis, ↓reduceIte]
  simp only [bind, Except.bind, eligibleOk, hitsOk, leakOk, liftAccessor, Except.mapError,
    Except.map]
  rw [folded]
  rfl

end EthLib.Consensus
