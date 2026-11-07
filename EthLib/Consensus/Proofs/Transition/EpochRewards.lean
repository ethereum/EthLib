module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochRewards

/-!
# Proofs: rewards and penalties

Adding a delta changes the entry at its index only.

A validator whose vote does not match earns nothing for that kind of vote.

It pays the base reward instead.

So a validator absent from the unslashed signers earns no reward for that kind of vote.

From Altair, a validator that did not set a flag earns no reward for it.

A validator that set it pays no penalty for it, and nobody pays one for the head flag.

The inactivity deltas hold no reward.

From Altair, a validator with a timely target pays no inactivity penalty.

The first epoch has no rewards, and the step keeps one balance for each validator.

The finality delay is the distance from the finalized epoch, and the leak is a delay above a limit.

The earliest inclusions have one entry for each validator, and each comes from a signed attestation.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- Adding a delta keeps the entries at the other indices. -/
theorem addDelta_getD_of_ne {deltas result : Array Gwei} {index : ValidatorIndex}
    {amount : Gwei} (computed : addDelta deltas index amount = .ok result) {j : Nat}
    (other : j ≠ index.toNat) : result.getD j 0 = deltas.getD j 0 := by
  unfold addDelta at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    simp [Array.getD_eq_getD_getElem?, Ne.symm other]
  · cases computed

/-- Adding nothing keeps the deltas. -/
theorem addDelta_zero {deltas result : Array Gwei} {index : ValidatorIndex}
    (computed : addDelta deltas index 0 = .ok result) : result = deltas := by
  unfold addDelta at computed
  split at computed
  · rename_i inside
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff,
      pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨sum, ⟨_, value⟩, rfl⟩ := computed
    have same : sum = deltas[index.toNat] := UInt64.toNat_inj.mp (by simpa using value)
    subst same
    simp
  · cases computed

/-- A validator whose vote does not match earns nothing for that kind of vote.

It pays the base reward instead. -/
theorem componentDelta_unmatched (state : BeaconState preset fork)
    (base attestingBalance totalActiveBalance : Gwei) :
    componentDelta state false base attestingBalance totalActiveBalance = .ok (0, base) := rfl

/-- A validator absent from the unslashed signers of some attestations earns nothing for them.

This holds in a leak and outside one. -/
theorem getAttestationComponentDeltas_absent {attestations : Array (PendingAttestation preset)}
    {rewards penalties : Array Gwei}
    (computed : getAttestationComponentDeltas state attestations = .ok (rewards, penalties))
    {attesters : List ValidatorIndex}
    (signers : getUnslashedAttestingIndices state attestations = .ok attesters) {index : Nat}
    (absent : ∀ attester ∈ attesters, attester.toNat ≠ index) : rewards.getD index 0 = 0 := by
  simp only [getAttestationComponentDeltas, bind_ok_iff, liftAccessor_ok, signers] at computed
  obtain ⟨_, _, _, found, _, _, eligible, _, folded⟩ := computed
  cases found
  have unmarked : (markIndices state.validators.data.size attesters).getD index false = false := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    split
    · simp only [Option.getD_some, List.any_eq_false, beq_iff_eq]
      exact fun attester member => absent attester member
    · rfl
  let P : Array Gwei × Array Gwei → Prop := fun deltas =>
    ∀ j, (markIndices state.validators.data.size attesters).getD j false = false →
      deltas.1.getD j 0 = 0
  have start : P (Array.replicate state.validators.data.size 0,
      Array.replicate state.validators.data.size 0) := by
    intro j _
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have holds := foldlM_ok_invariant P (fun deltas index next before step => by
    obtain ⟨rewards, penalties⟩ := deltas
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨_, _, ⟨reward, penalty⟩, delta, newRewards, rewardsOk, _, _, rfl⟩ := step
    intro j unmarkedJ
    by_cases same : j = index.toNat
    · subst same
      rw [unmarkedJ] at delta
      rw [componentDelta_unmatched] at delta
      cases delta
      rw [addDelta_zero rewardsOk]
      exact before _ unmarkedJ
    · rw [addDelta_getD_of_ne rewardsOk same]
      exact before j unmarkedJ) start folded
  exact holds index unmarked

/-- A fold of steps that keep one entry of the deltas, from zeros, leaves that entry zero. -/
private theorem foldlM_getD_zero {step : Array Gwei × Array Gwei → ValidatorIndex →
      Except TransitionError (Array Gwei × Array Gwei)}
    (pick : Array Gwei × Array Gwei → Array Gwei) {j : Nat}
    (keeps : ∀ deltas index next, step deltas index = .ok next →
      (pick next).getD j 0 = (pick deltas).getD j 0)
    {indices : List ValidatorIndex} {start result : Array Gwei × Array Gwei}
    (zero : (pick start).getD j 0 = 0) (computed : indices.foldlM step start = .ok result) :
    (pick result).getD j 0 = 0 :=
  foldlM_ok_invariant (fun deltas => (pick deltas).getD j 0 = 0)
    (fun deltas index next before done => (keeps deltas index next done).trans before) zero computed

/-- An array of zeros is zero at every index. -/
private theorem replicate_getD_zero (size j : Nat) :
    (Array.replicate size (0 : Gwei)).getD j 0 = 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- One step of the flag deltas keeps the reward of a validator that did not set the flag. -/
theorem addFlagDelta_reward {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next)
    {j : Nat} (unset : participated.getD j false = false) :
    next.1.getD j 0 = deltas.1.getD j 0 := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · rename_i set
    have other : j ≠ index.toNat := fun same => by rw [same, set] at unset; cases unset
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, ok, rfl⟩ := computed
      exact addDelta_getD_of_ne ok other
  · split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, rfl⟩ := computed
      rfl

/-- One step of the flag deltas keeps the penalty of a validator that set the flag.

It keeps every penalty for the head flag. -/
theorem addFlagDelta_penalty {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next)
    {j : Nat} (exempt : participated.getD j false = true ∨
      flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX) :
    next.2.getD j 0 = deltas.2.getD j 0 := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := computed
      rfl
  · rename_i unset
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · rename_i notHead
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, ok, rfl⟩ := computed
      refine addDelta_getD_of_ne ok fun same => ?_
      rcases exempt with set | head
      · rw [same] at set
        exact unset set
      · exact notHead head

/-- From Altair, a validator that did not set a flag in the previous epoch earns no reward for it.

This holds in a leak and outside one. -/
theorem getFlagIndexDeltas_absent {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    {participating : List ValidatorIndex}
    (flagged : getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
      (getPreviousEpoch state) = .ok participating)
    {index : Nat} (absent : ∀ participant ∈ participating, participant.toNat ≠ index) :
    rewards.getD index 0 = 0 := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok, flagged] at computed
  obtain ⟨_, found, _, _, _, _, _, _, folded⟩ := computed
  cases found
  have unset : (markIndices state.validators.data.size participating).getD index false = false := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    split
    · simp only [Option.getD_some, List.any_eq_false, beq_iff_eq]
      exact fun participant member => absent participant member
    · rfl
  exact foldlM_getD_zero Prod.fst (fun _ _ _ step => addFlagDelta_reward step unset)
    (replicate_getD_zero _ _) folded

/-- From Altair, a validator that set a flag in the previous epoch pays no penalty for it. -/
theorem getFlagIndexDeltas_present {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    {participating : List ValidatorIndex}
    (flagged : getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
      (getPreviousEpoch state) = .ok participating)
    {index : ValidatorIndex} (present : index ∈ participating)
    (inside : index.toNat < state.validators.data.size) :
    penalties.getD index.toNat 0 = 0 := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok, flagged] at computed
  obtain ⟨_, found, _, _, _, _, _, _, folded⟩ := computed
  cases found
  have set : (markIndices state.validators.data.size participating).getD index.toNat false =
      true := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    simpa [inside] using ⟨index, present, rfl⟩
  exact foldlM_getD_zero Prod.snd (fun _ _ _ step => addFlagDelta_penalty step (.inl set))
    (replicate_getD_zero _ _) folded

/-- From Altair, the head flag has no penalties. -/
theorem getFlagIndexDeltas_head {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    (head : flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX) (j : Nat) :
    penalties.getD j 0 = 0 := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, folded⟩ := computed
  exact foldlM_getD_zero Prod.snd (fun _ _ _ step => addFlagDelta_penalty step (.inr head))
    (replicate_getD_zero _ _) folded

/-- The inactivity deltas hold no reward, at every fork. -/
theorem getInactivityPenaltyDeltas_rewards {config : Config} {rewards penalties : Array Gwei}
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties)) (j : Nat) :
    rewards.getD j 0 = 0 := by
  unfold getInactivityPenaltyDeltas at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact replicate_getD_zero _ _
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := computed
      exact replicate_getD_zero _ _
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
      obtain ⟨rfl, _⟩ := computed
      exact replicate_getD_zero _ _

/-- One step of the inactivity penalties keeps the penalty of a validator with a timely target. -/
theorem addInactivityScorePenalty_matched {config : Config} {altair : .altair ≤ fork}
    {targetMatched : Array Bool} {penalties next : Array Gwei} {index : ValidatorIndex}
    (computed : addInactivityScorePenalty config state altair targetMatched penalties index =
      .ok next)
    {j : Nat} (matched : targetMatched.getD j false = true) :
    next.getD j 0 = penalties.getD j 0 := by
  unfold addInactivityScorePenalty at computed
  split at computed
  · cases computed
    rfl
  · rename_i unmatched
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, _, _, ok⟩ := computed
      exact addDelta_getD_of_ne ok fun same => unmatched (same ▸ matched)
    · cases computed

/-- From Altair, a validator with a timely target in the previous epoch pays no inactivity penalty.

This holds in a leak and outside one. -/
theorem getInactivityPenaltyDeltas_target {config : Config} (altair : .altair ≤ fork)
    {rewards penalties : Array Gwei}
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties))
    {matching : List ValidatorIndex}
    (timely : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (getPreviousEpoch state) = .ok matching)
    {index : ValidatorIndex} (present : index ∈ matching)
    (inside : index.toNat < state.validators.data.size) :
    penalties.getD index.toNat 0 = 0 := by
  unfold getInactivityPenaltyDeltas at computed
  dsimp only at computed
  simp only [altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok, timely, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨_, found, _, _, _, folded, _, rfl⟩ := computed
  cases found
  have set : (markIndices state.validators.data.size matching).getD index.toNat false = true := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    simpa [inside] using ⟨index, present, rfl⟩
  exact foldlM_ok_invariant (fun deltas : Array Gwei => deltas.getD index.toNat 0 = 0)
    (fun _ _ _ before step => (addInactivityScorePenalty_matched step set).trans before)
    (replicate_getD_zero _ _) folded

/-- In the first epoch, rewards and penalties change nothing. -/
theorem processRewardsAndPenalties_genesis (config : Config)
    (genesis : getCurrentEpoch state = GENESIS_EPOCH) :
    processRewardsAndPenalties config state = .ok state := by
  simp [processRewardsAndPenalties, genesis, pure, Except.pure]

/-- Applying the deltas of one validator keeps the sizes. -/
theorem sameSizes_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : SameSizes state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨raised, raisedOk, lowered⟩ := computed
  exact (sameSizes_increaseBalance raisedOk).trans (sameSizes_decreaseBalance lowered)

/-- Applying some deltas to every validator keeps the sizes. -/
theorem sameSizes_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : SameSizes state after :=
  foldlM_ok_invariant (SameSizes state) (fun _ _ _ sizes step =>
    sizes.trans (sameSizes_applyDeltas step)) (SameSizes.refl state) computed

/-- Rewards and penalties keep the sizes, at every fork. -/
theorem processRewardsAndPenalties_sameSizes {config : Config}
    (computed : processRewardsAndPenalties config state = .ok after) : SameSizes state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact foldlM_ok_invariant (SameSizes state) (fun before _ _ sizes step =>
      sizes.trans (sameSizes_applyAllDeltas step)) (SameSizes.refl state) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact sameSizes_applyAllDeltas applied

/-! ## Finality delay and the inactivity leak -/

/-- The finality delay exists exactly when the finalized epoch is not after the previous epoch.

It is then the difference of the two. -/
theorem getFinalityDelay_ok_iff {delay : Epoch} :
    getFinalityDelay state = .ok delay ↔
      state.finalizedCheckpoint.epoch.toNat ≤ (getPreviousEpoch state).toNat ∧
        delay.toNat = (getPreviousEpoch state).toNat - state.finalizedCheckpoint.epoch.toNat := by
  unfold getFinalityDelay
  rw [liftAccessor_ok, liftArith, mapError_ok_iff, subChecked_ok_iff]

/-- The chain leaks exactly when its finality delay exists and exceeds the fixed number of epochs.

The answer says whether it does. -/
theorem isInInactivityLeak_ok_iff {leak : Bool} :
    isInInactivityLeak state = .ok leak ↔
      ∃ delay, getFinalityDelay state = .ok delay ∧
        (leak = true ↔ preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY < delay) := by
  unfold isInInactivityLeak
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨delay, found, rfl⟩
    exact ⟨delay, found, by simp⟩
  · rintro ⟨delay, found, iff⟩
    refine ⟨delay, found, ?_⟩
    cases leak <;> simp_all

/-! ## The earliest inclusion of each signer -/

/-- A fold keeps a property of its accumulator when each step from an item of the list keeps it. -/
theorem list_foldl_invariant {α β : Type} (P : β → Prop) {f : β → α → β} {start : β}
    (h : P start) :
    ∀ xs : List α, (∀ b, P b → ∀ x ∈ xs, P (f b x)) → P (xs.foldl f start)
  | [], _ => h
  | x :: rest, step =>
    list_foldl_invariant P (step _ h x (List.mem_cons_self ..)) rest
      fun b hb y mem => step b hb y (List.mem_cons_of_mem _ mem)

/-- The earliest inclusions have one entry for each validator.

An entry that holds an attestation holds the attestation of one of the signed pairs. -/
theorem earliestInclusions_size_and_mem {size : Nat}
    {signed : Array (PendingAttestation preset × List ValidatorIndex)} :
    (earliestInclusions size signed).size = size ∧
      ∀ (i : Nat) (a : PendingAttestation preset),
        (earliestInclusions size signed)[i]? = some (some a) →
          ∃ signers, (a, signers) ∈ signed.toList := by
  let Inv (best : Array (Option (PendingAttestation preset))) : Prop :=
    best.size = size ∧ ∀ (i : Nat) (a : PendingAttestation preset), best[i]? = some (some a) →
      ∃ signers, (a, signers) ∈ signed.toList
  suffices h : Inv (earliestInclusions size signed) from h
  unfold earliestInclusions
  rw [← Array.foldl_toList]
  -- The start holds no attestation.
  refine list_foldl_invariant Inv ⟨by simp, fun i a found => ?_⟩ _ ?_
  · rw [Array.getElem?_replicate] at found
    split at found <;> cases found
  rintro best ⟨sized, kept⟩ ⟨attestation, signers⟩ pair
  refine list_foldl_invariant Inv ⟨sized, kept⟩ signers fun best ⟨sized, kept⟩ index _ => ?_
  -- Each way of updating the entry of a signer keeps the size and the origin of the entries.
  have put : ∀ i, Inv (best.setIfInBounds i (some attestation)) := by
    intro i
    refine ⟨by simpa using sized, fun j a found => ?_⟩
    rw [Array.getElem?_setIfInBounds] at found
    split at found
    · split at found
      · exact ⟨signers, by cases found; exact pair⟩
      · cases found
    · exact kept j a found
  show Inv (match best.getD index.toNat none with
    | some kept => if attestation.inclusionDelay < kept.inclusionDelay then
        best.setIfInBounds index.toNat (some attestation) else best
    | none => best.setIfInBounds index.toNat (some attestation))
  split
  · split
    · exact put _
    · exact ⟨sized, kept⟩
  · exact put _

end EthLib.Consensus
