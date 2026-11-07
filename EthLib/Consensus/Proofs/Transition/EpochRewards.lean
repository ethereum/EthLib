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

For a registry within its limit, the deltas add each reward to its balance without overflow.

They then subtract each penalty, stopping at zero.

After the first epoch, the step applies the attestation deltas once before Altair.

From Altair it applies the deltas of each flag, then those of inactivity.

The balances past the registry stay.
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
  refine List.foldlRecOn (motive := Inv) _ _ ⟨by simp, fun i a found => ?_⟩ ?_
  · rw [Array.getElem?_replicate] at found
    split at found <;> cases found
  rintro best ⟨sized, kept⟩ ⟨attestation, signers⟩ pair
  refine List.foldlRecOn (motive := Inv) signers _ ⟨sized, kept⟩
    fun best ⟨sized, kept⟩ index _ => ?_
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


/-! ## Balances after the rewards and penalties -/

/-- The deltas of one validator apply exactly when its position names a balance.

The position is taken as a 64-bit index, and the reward added to the balance stays below `2^64`.

The new balance is the old one plus the reward, minus the penalty, or zero if the penalty is larger.

A reward or penalty past the end of its array counts as zero. -/
theorem applyDeltas_eq_ok_iff {rewards penalties : Array Gwei} {index : Nat} :
    applyDeltas rewards penalties state index = .ok after ↔
      ∃ inside : index.toUInt64.toNat < state.balances.data.size,
        state.balances.data[index.toUInt64.toNat].toNat + (rewards.getD index 0).toNat < 2 ^ 64 ∧
          after = state.putBalance index.toUInt64.toNat inside
            (saturatingSub (state.balances.data[index.toUInt64.toNat] + rewards.getD index 0)
              (penalties.getD index 0)) := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok, increaseBalance_eq_ok_iff,
    decreaseBalance_eq_ok_iff]
  constructor
  · rintro ⟨_, ⟨inside, fits, rfl⟩, again, rfl⟩
    exact ⟨inside, fits, by simp [BeaconState.putBalance]⟩
  · rintro ⟨inside, fits, rfl⟩
    exact ⟨_, ⟨inside, fits, rfl⟩, by simpa [BeaconState.putBalance] using inside,
      by simp [BeaconState.putBalance]⟩

/-- The deltas of the first positions, at most `2^64` of them, each apply at their own position.

The other balances stay. -/
private theorem foldlM_applyDeltas_balances {rewards penalties : Array Gwei} {count : Nat}
    (small : count ≤ 2 ^ 64)
    (computed : (List.range count).foldlM (applyDeltas rewards penalties) state = .ok after) :
    ∀ i, (i < count → ∃ balance, state.balances.data[i]? = some balance ∧
      balance.toNat + (rewards.getD i 0).toNat < 2 ^ 64 ∧
      after.balances.data[i]? =
        some (saturatingSub (balance + rewards.getD i 0) (penalties.getD i 0))) ∧
    (count ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  induction count generalizing after with
  | zero =>
    simp only [List.range_zero, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact fun _ => ⟨fun lt => absurd lt (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ count ih =>
    rw [List.range_succ, List.foldlM_append, bind_ok_iff] at computed
    obtain ⟨middle, folded, last⟩ := computed
    simp only [List.foldlM_cons, List.foldlM_nil, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at last
    obtain ⟨final, step, rfl⟩ := last
    have low := ih (by omega) folded
    have same : count.toUInt64.toNat = count := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    -- The last position is below `2^64`, so it is its own validator index.
    obtain ⟨balance, found, fits, atCount, other⟩ : ∃ balance,
        middle.balances.data[count]? = some balance ∧
          balance.toNat + (rewards.getD count 0).toNat < 2 ^ 64 ∧
          final.balances.data[count]? =
            some (saturatingSub (balance + rewards.getD count 0) (penalties.getD count 0)) ∧
          ∀ j, j ≠ count → final.balances.data[j]? = middle.balances.data[j]? := by
      obtain ⟨inside, fits, rfl⟩ := applyDeltas_eq_ok_iff.mp step
      have inside' : count < middle.balances.data.size := same ▸ inside
      refine ⟨middle.balances.data[count], Array.getElem?_eq_getElem inside',
        by simpa [same] using fits, ?_, fun j ne => ?_⟩
      · simp [BeaconState.putBalance, same, inside']
      · simp [BeaconState.putBalance, same, Ne.symm ne]
    rw [(low count).2 (Nat.le_refl _)] at found
    intro i
    refine ⟨fun lt => ?_, fun ge => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
      · rw [other i (by omega)]
        exact (low i).1 lt
      · exact ⟨balance, found, fits, atCount⟩
    · rw [other i (by omega)]
      exact (low i).2 (by omega)

/-- For a registry within its limit, applying some deltas changes the balance of each validator.

It becomes the old balance plus the reward, minus the penalty, or zero if the penalty is larger.

That old balance exists, and adding the reward to it stays below `2^64`.

The balances past the registry stay.

A reward or penalty past the end of its array counts as zero. -/
theorem applyAllDeltas_balances {rewards penalties : Array Gwei}
    (within : state.RegistryWithinLimit)
    (computed : applyAllDeltas state (rewards, penalties) = .ok after) (i : Nat) :
    (i < state.validators.data.size → ∃ balance, state.balances.data[i]? = some balance ∧
      balance.toNat + (rewards.getD i 0).toNat < 2 ^ 64 ∧
      after.balances.data[i]? =
        some (saturatingSub (balance + rewards.getD i 0) (penalties.getD i 0))) ∧
    (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) :=
  have bound : state.validators.data.size ≤ _ := within
  foldlM_applyDeltas_balances (by have := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt; omega)
    computed i

/-- For a registry within its limit, a list of deltas acts on each balance in the order of the list.

Each one adds the reward of the validator, then subtracts its penalty, stopping at zero.

The balances past the registry stay. -/
theorem foldlM_applyAllDeltas_balances {deltas : List (Array Gwei × Array Gwei)}
    (within : state.RegistryWithinLimit)
    (computed : deltas.foldlM applyAllDeltas state = .ok after) (i : Nat) :
    (i < state.validators.data.size → after.balances.data[i]? =
      state.balances.data[i]?.map fun balance => deltas.foldl (fun balance delta =>
        saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) balance) ∧
    (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  induction deltas generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ => by cases state.balances.data[i]? <;> rfl, fun _ => rfl⟩
  | cons delta deltas ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, applied, folded⟩ := computed
    -- The first deltas keep the registry, so the rest apply to a registry of the same size.
    have sizes := sameSizes_applyAllDeltas applied
    have later := ih (state := middle)
      (by unfold BeaconState.RegistryWithinLimit; rw [sizes.1]; exact within) folded
    rw [sizes.1] at later
    have first := applyAllDeltas_balances (rewards := delta.1) (penalties := delta.2) within
      applied i
    refine ⟨fun lt => ?_, fun ge => (later.2 ge).trans (first.2 ge)⟩
    obtain ⟨balance, found, -, raised⟩ := first.1 lt
    rw [later.1 lt, raised, found]
    rfl

/-- Before Altair and after the first epoch, rewards and penalties apply the attestation deltas.

The registry must be within its limit.

The balance of each validator becomes the old balance plus the reward, minus the penalty.

It stops at zero when the penalty is larger.

That old balance exists, and adding the reward to it stays below `2^64`.

The balances past the registry stay. -/
theorem processRewardsAndPenalties_balances_of_lt_altair {config : Config}
    (before : fork < .altair) (within : state.RegistryWithinLimit)
    (later : getCurrentEpoch state ≠ GENESIS_EPOCH)
    (computed : processRewardsAndPenalties config state = .ok after) :
    ∃ rewards penalties, getAttestationDeltas config state before = .ok (rewards, penalties) ∧
      ∀ i, (i < state.validators.data.size → ∃ balance, state.balances.data[i]? = some balance ∧
        balance.toNat + (rewards.getD i 0).toNat < 2 ^ 64 ∧
        after.balances.data[i]? =
          some (saturatingSub (balance + rewards.getD i 0) (penalties.getD i 0))) ∧
      (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  simp only [processRewardsAndPenalties, later, notAltair, ↓reduceIte, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨⟨rewards, penalties⟩, found, applied⟩ := computed
  exact ⟨rewards, penalties, found, applyAllDeltas_balances within applied⟩

/-- From Altair and after the first epoch, rewards and penalties apply the deltas of each flag.

They then apply the inactivity deltas, and the registry must be within its limit.

Each one adds the reward of the validator to its balance, then subtracts its penalty.

The balance stops at zero when the penalty is larger.

The balances past the registry stay. -/
theorem processRewardsAndPenalties_balances_of_altair {config : Config}
    (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    (later : getCurrentEpoch state ≠ GENESIS_EPOCH)
    (computed : processRewardsAndPenalties config state = .ok after) :
    ∃ flagDeltas inactivityDeltas,
      (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM (getFlagIndexDeltas state altair) =
        .ok flagDeltas ∧
      getInactivityPenaltyDeltas config state = .ok inactivityDeltas ∧
      ∀ i, (i < state.validators.data.size → after.balances.data[i]? =
        state.balances.data[i]?.map fun balance =>
          (flagDeltas ++ [inactivityDeltas]).foldl (fun balance delta =>
            saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) balance) ∧
      (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  simp only [processRewardsAndPenalties, later, altair, ↓reduceIte, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨flagDeltas, flagged, inactivityDeltas, penalized, applied⟩ := computed
  exact ⟨flagDeltas, inactivityDeltas, flagged, penalized,
    foldlM_applyAllDeltas_balances within applied⟩

end EthLib.Consensus
