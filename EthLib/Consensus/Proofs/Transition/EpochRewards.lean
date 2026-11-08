module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Participation
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochRewards

/-!
# Proofs: rewards and penalties

Adding a delta changes the entry at its index only.

It adds its amount there.

A validator whose vote does not match earns nothing for that kind of vote.

It pays the base reward instead.

So a validator absent from the unslashed signers earns no reward for that kind of vote.

From Altair, a validator that did not set a flag earns no reward for it.

A validator that set it pays no penalty for it, and nobody pays one for the head flag.

An unslashed validator that set a flag earns nothing for it in a leak.

Otherwise it earns the weight of the flag in its base reward, scaled by the share that set it.

That needs a registry within its limit, in which the eligible validators increase strictly.

The inactivity deltas hold no reward.

From Altair, a validator with a timely target pays no inactivity penalty.

The first epoch has no rewards, and the step keeps one balance for each validator.

The finality delay is the distance from the finalized epoch, and the leak is a delay above a limit.

The earliest inclusions have one entry for each validator, and each comes from a signed attestation.

A fold whose steps each act on the balance at their own position acts on each of those balances.

For a registry within its limit, deltas that apply add each reward to its balance below `2^64`.

They then subtract each penalty, stopping at zero.

After the first epoch, the step applies the attestation deltas once before Altair.

From Altair it applies the deltas of each flag, then those of inactivity.

Take a step that succeeds on a registry within its limit.

Then each addition of a reward to a balance stays below `2^64`.

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

/-- Adding a delta adds its amount at its index. -/
theorem addDelta_getD_self {deltas result : Array Gwei} {index : ValidatorIndex}
    {amount : Gwei} (computed : addDelta deltas index amount = .ok result) :
    (result.getD index.toNat 0).toNat = (deltas.getD index.toNat 0).toNat + amount.toNat := by
  unfold addDelta at computed
  split at computed
  · rename_i inside
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff,
      pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨sum, ⟨_, value⟩, rfl⟩ := computed
    simp [Array.getD_eq_getD_getElem?, inside, value]
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

/-- One step of the flag deltas keeps the reward of a validator that did not set the flag.

It keeps the reward at each other index. -/
theorem addFlagDelta_reward {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next)
    {j : Nat} (kept : participated.getD j false = false ∨ j ≠ index.toNat) :
    next.1.getD j 0 = deltas.1.getD j 0 := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · rename_i set
    have other : j ≠ index.toNat := by
      rcases kept with unset | other
      · exact fun same => by rw [same, set] at unset; cases unset
      · exact other
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
  exact foldlM_getD_zero Prod.fst (fun _ _ _ step => addFlagDelta_reward step (.inl unset))
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

/-- One step of the flag deltas reads the base reward of its validator. -/
private theorem addFlagDelta_base {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next) :
    ∃ base, getBaseReward state total index = .ok base := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨base, based, -⟩ := computed
  exact ⟨base, based⟩

/-- One step of the flag deltas at a validator that set the flag reads the leak. -/
private theorem addFlagDelta_leak {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next)
    (set : participated.getD index.toNat false = true) :
    ∃ leak, isInInactivityLeak state = .ok leak := by
  obtain ⟨base, based⟩ := addFlagDelta_base computed
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff, liftAccessor_ok, based, set, Except.ok.injEq,
    exists_eq_left', ↓reduceIte] at computed
  obtain ⟨leak, leaked, -⟩ := computed
  exact ⟨leak, leaked⟩

/-- One step of the flag deltas at a validator that set the flag adds what it earns to its reward.

It earns nothing in a leak.

Otherwise it earns the weight of the flag in its base reward, scaled by the share that set it. -/
theorem addFlagDelta_reward_of_set {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements base : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex} {leak : Bool}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next)
    (set : participated.getD index.toNat false = true)
    (based : getBaseReward state total index = .ok base)
    (leaking : isInInactivityLeak state = .ok leak) :
    (next.1.getD index.toNat 0).toNat = (deltas.1.getD index.toNat 0).toNat + if leak then 0 else
      base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat * participatingIncrements.toNat /
        (activeIncrements.toNat * WEIGHT_DENOMINATOR.toNat) := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff, liftAccessor_ok, based, set, leaking, Except.ok.injEq,
    exists_eq_left', ↓reduceIte] at computed
  cases leak
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
      mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, ⟨_, scaledOk, numeratorOk⟩, _, denominatorOk, _, rewardOk, _, ok, rfl⟩ := computed
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Each checked step succeeded, so it gives the exact product or quotient.
    rw [addDelta_getD_self ok, (divChecked_ok_iff.mp rewardOk).2,
      (mulChecked_ok_iff.mp numeratorOk).2, (mulChecked_ok_iff.mp scaledOk).2,
      (mulChecked_ok_iff.mp denominatorOk).2]
  · simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp

/-- A fold of the flag deltas over other validators keeps the reward of a validator. -/
private theorem foldlM_addFlagDelta_reward_of_not_mem
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {participated : Array Bool}
    {total participatingIncrements activeIncrements : Gwei} {index : ValidatorIndex} :
    ∀ {indices : List ValidatorIndex} {start result : Array Gwei × Array Gwei}, index ∉ indices →
      indices.foldlM (addFlagDelta state flagIndex participated total participatingIncrements
        activeIncrements) start = .ok result →
      result.1.getD index.toNat 0 = start.1.getD index.toNat 0
  | [], _, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    rw [computed]
  | other :: rest, _, _, absent, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, computed⟩ := computed
    rw [List.mem_cons, not_or] at absent
    rw [foldlM_addFlagDelta_reward_of_not_mem absent.2 computed]
    exact addFlagDelta_reward first (.inr fun same => absent.1 (UInt64.toNat_inj.mp same))

/-- A filter map in `Except` that succeeds is a filter map of the values of its calls. -/
private theorem filterMapM_ok_eq_filterMap {α β ε : Type} {f : α → Except ε (Option β)}
    {g : α → Option β} :
    ∀ {l : List α} {out : List β}, (∀ x ∈ l, ∀ y, f x = .ok y → g x = y) →
      l.filterMapM f = .ok out → out = l.filterMap g
  | [], out, _, mapped => by
    simp only [List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at mapped
    simp [← mapped]
  | x :: l, out, values, mapped => by
    rw [List.filterMapM_cons, bind_ok_iff] at mapped
    obtain ⟨image, first, mapped⟩ := mapped
    have rest : ∀ x' ∈ l, ∀ y, f x' = .ok y → g x' = y :=
      fun x' member => values x' (List.mem_cons_of_mem x member)
    rw [List.filterMap_cons, values x List.mem_cons_self image first]
    cases image with
    | none => exact filterMapM_ok_eq_filterMap rest mapped
    | some z =>
      simp only at mapped
      rw [bind_ok_iff] at mapped
      obtain ⟨tail, tailOk, mapped⟩ := mapped
      simp only [pure, Except.pure, Except.ok.injEq] at mapped
      subst mapped
      simp only [filterMapM_ok_eq_filterMap rest tailOk]

/-- The eligible indices are the positions of the validators whose test holds. -/
private theorem getEligibleValidatorIndices_eq {eligible : List ValidatorIndex}
    (computed : getEligibleValidatorIndices state = .ok eligible) :
    eligible = state.validators.data.toList.zipIdx.filterMap fun pair =>
      (match isEligibleValidator (getPreviousEpoch state) pair.1 with
        | .ok true => some pair.2.toUInt64
        | _ => none) := by
  unfold getEligibleValidatorIndices at computed
  refine filterMapM_ok_eq_filterMap (fun ⟨validator, position⟩ _ image step => ?_) computed
  dsimp only at step ⊢
  rw [bind_ok_iff] at step
  obtain ⟨eligibility, tested, step⟩ := step
  simp only [pure, Except.pure, Except.ok.injEq] at step
  subst step
  rw [tested]
  cases eligibility <;> rfl

/-- The eligible indices increase strictly, for a registry within its limit. -/
theorem getEligibleValidatorIndices_sorted {eligible : List ValidatorIndex}
    (within : state.RegistryWithinLimit)
    (computed : getEligibleValidatorIndices state = .ok eligible) :
    eligible.Pairwise (· < ·) := by
  rw [getEligibleValidatorIndices_eq computed]
  -- Each index is the position of its validator, as a 64-bit index.
  have image : ∀ {validator : Validator} {position : Nat} {index : ValidatorIndex},
      index ∈ (match isEligibleValidator (getPreviousEpoch state) validator with
        | .ok true => some position.toUInt64
        | _ => none) → index = position.toUInt64 := by
    intro validator position index member
    split at member
    · exact (Option.some.inj (Option.mem_def.mp member)).symm
    · cases member
  have base : state.validators.data.toList.zipIdx.Pairwise (fun a b => a.2 < b.2) := by
    have := List.pairwise_lt_range' (s := 0) (n := state.validators.data.toList.length)
    rw [← List.zipIdx_map_snd 0] at this
    exact List.pairwise_map.mp this
  refine List.Pairwise.filterMap _ ?_ (List.Pairwise.and_mem.mp base)
  rintro ⟨v, i⟩ ⟨w, j⟩ ⟨mi, mj, lt⟩ a ha b hb
  rw [image (validator := v) (position := i) ha, image (validator := w) (position := j) hb]
  have hi : i < state.validators.data.size := by simpa using (List.mem_zipIdx' mi).1
  have hj : j < state.validators.data.size := by simpa using (List.mem_zipIdx' mj).1
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64_of_lt within hi, toNat_toUInt64_of_lt within hj]
  exact lt

/-- Each validator active in the previous epoch is eligible for the rewards of that epoch. -/
theorem mem_getEligibleValidatorIndices_of_active {eligible : List ValidatorIndex}
    (computed : getEligibleValidatorIndices state = .ok eligible) {index : ValidatorIndex}
    {validator : Validator} (found : state.validators.data[index.toNat]? = some validator)
    (active : isActiveValidator validator (getPreviousEpoch state) = true) :
    index ∈ eligible := by
  rw [getEligibleValidatorIndices_eq computed, List.mem_filterMap]
  refine ⟨(validator, index.toNat), ?_, ?_⟩
  · rw [List.mem_zipIdx_iff_getElem?]
    simpa using found
  · simp [isEligibleValidator, active, pure, Except.pure]

/-- From Altair, take an unslashed validator that set a flag in the previous epoch.

It earns nothing for the flag in a leak.

Otherwise it earns the weight of the flag in its base reward, scaled by the share that set it.

That share is the balance that set the flag over the active balance, both in whole increments.

That needs a registry within its limit. -/
theorem getFlagIndexDeltas_reward {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (within : state.RegistryWithinLimit)
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    {participating : List ValidatorIndex}
    (flagged : getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
      (getPreviousEpoch state) = .ok participating)
    {participatingBalance total : Gwei}
    (weighed : getTotalBalance state participating = .ok participatingBalance)
    (active : getTotalActiveBalance state = .ok total)
    {index : ValidatorIndex} (present : index ∈ participating) :
    ∃ base leak, getBaseReward state total index = .ok base ∧
      isInInactivityLeak state = .ok leak ∧
      (rewards.getD index.toNat 0).toNat = if leak then 0 else
        base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
          (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
          (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok, flagged] at computed
  obtain ⟨_, found, balance, balanced, sum, summed, eligible, listed, folded⟩ := computed
  cases found
  obtain rfl : balance = participatingBalance := Except.ok.inj (balanced.symm.trans weighed)
  obtain rfl : sum = total := Except.ok.inj (summed.symm.trans active)
  -- The validator is active in the previous epoch, so the fold reaches it once.
  obtain ⟨activeBefore, -, -⟩ := mem_getUnslashedParticipatingIndices flagged index present
  obtain ⟨validator, read, isActive⟩ := (mem_getActiveValidatorIndices within).mp activeBefore
  have inside : index.toNat < state.validators.data.size := (Array.getElem?_eq_some_iff.mp read).1
  have sorted := getEligibleValidatorIndices_sorted within listed
  obtain ⟨first, last, rfl⟩ :=
    List.append_of_mem (mem_getEligibleValidatorIndices_of_active listed read isActive)
  rw [List.pairwise_append, List.pairwise_cons] at sorted
  have notFirst : index ∉ first :=
    fun mem => UInt64.lt_irrefl _ (sorted.2.2 index mem index List.mem_cons_self)
  have notLast : index ∉ last := fun mem => UInt64.lt_irrefl _ (sorted.2.1.1 index mem)
  have set : (markIndices state.validators.data.size participating).getD index.toNat false =
      true := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    simpa [inside] using ⟨index, present, rfl⟩
  rw [List.foldlM_append, bind_ok_iff] at folded
  obtain ⟨middle, before, folded⟩ := folded
  rw [List.foldlM_cons, bind_ok_iff] at folded
  obtain ⟨step, stepped, after⟩ := folded
  have zero := foldlM_addFlagDelta_reward_of_not_mem notFirst before
  have kept := foldlM_addFlagDelta_reward_of_not_mem notLast after
  simp only at zero kept
  -- The step reads the base reward of the validator and the leak.
  obtain ⟨base, based⟩ := addFlagDelta_base stepped
  obtain ⟨leak, leaking⟩ := addFlagDelta_leak stepped set
  refine ⟨base, leak, based, leaking, ?_⟩
  rw [kept, addFlagDelta_reward_of_set stepped set based leaking, zero, replicate_getD_zero,
    UInt64.toNat_zero, Nat.zero_add, UInt64.toNat_div, UInt64.toNat_div]

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

/-- A fold over the first positions whose step acts on the balance at its own position.

Each step from a state with a kept property gives a state with that property.

It relates the old and new entries at its position, and keeps the other entries.

The fold then gives a state with that property.

It relates the old and new entries at each of those positions, and keeps the entries past them. -/
theorem foldlM_range_balances {ε : Type}
    {step : BeaconState preset fork → Nat → Except ε (BeaconState preset fork)}
    (Keep : BeaconState preset fork → Prop) (Relates : Nat → Option Gwei → Option Gwei → Prop)
    {count : Nat}
    (stepped : ∀ {last next : BeaconState preset fork} {j : Nat}, j < count → Keep last →
      step last j = .ok next → Keep next ∧
        Relates j last.balances.data[j]? next.balances.data[j]? ∧
        ∀ k, k ≠ j → next.balances.data[k]? = last.balances.data[k]?)
    (kept : Keep state)
    (computed : (List.range count).foldlM step state = .ok after) :
    Keep after ∧ ∀ i, (i < count → Relates i state.balances.data[i]? after.balances.data[i]?) ∧
      (count ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  induction count generalizing after with
  | zero =>
    simp only [List.range_zero, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨kept, fun _ => ⟨fun lt => absurd lt (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  | succ count ih =>
    rw [List.range_succ, List.foldlM_append, bind_ok_iff] at computed
    obtain ⟨middle, folded, last⟩ := computed
    simp only [List.foldlM_cons, List.foldlM_nil, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at last
    obtain ⟨final, step, rfl⟩ := last
    obtain ⟨keptMiddle, low⟩ := ih (fun lt => stepped (Nat.lt_succ_of_lt lt)) folded
    obtain ⟨keptFinal, atCount, other⟩ := stepped (Nat.lt_succ_self count) keptMiddle step
    rw [(low count).2 (Nat.le_refl _)] at atCount
    refine ⟨keptFinal, fun i => ⟨fun lt => ?_, fun ge => ?_⟩⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | rfl
      · rw [other i (by omega)]
        exact (low i).1 lt
      · exact atCount
    · rw [other i (by omega)]
      exact (low i).2 (by omega)

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
  refine (foldlM_range_balances (fun _ => True) (fun i old new => ∃ balance, old = some balance ∧
    balance.toNat + (rewards.getD i 0).toNat < 2 ^ 64 ∧
    new = some (saturatingSub (balance + rewards.getD i 0) (penalties.getD i 0)))
    (fun {middle final j} lt _ step => ?_) trivial computed).2
  have same : j.toUInt64.toNat = j := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  -- The position is below `2^64`, so it is its own validator index.
  obtain ⟨inside, fits, rfl⟩ := applyDeltas_eq_ok_iff.mp step
  have inside' : j < middle.balances.data.size := same ▸ inside
  refine ⟨trivial, ⟨middle.balances.data[j], Array.getElem?_eq_getElem inside',
    by simpa [same] using fits, ?_⟩, fun k ne => ?_⟩
  · simp [BeaconState.putBalance, same, inside']
  · simp [BeaconState.putBalance, same, Ne.symm ne]

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

This holds when the deltas apply.

Each one adds the reward of the validator, then subtracts its penalty, stopping at zero.

Each of those sums stays below `2^64`, so a checked addition of each reward succeeds.

The balances past the registry stay. -/
theorem foldlM_applyAllDeltas_balances {deltas : List (Array Gwei × Array Gwei)}
    (within : state.RegistryWithinLimit)
    (computed : deltas.foldlM applyAllDeltas state = .ok after) (i : Nat) :
    (i < state.validators.data.size → after.balances.data[i]? =
      state.balances.data[i]?.map fun balance => deltas.foldl (fun balance delta =>
        saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) balance) ∧
    (i < state.validators.data.size → ∀ balance, state.balances.data[i]? = some balance →
      deltas.foldlM (fun balance delta => (addChecked balance (delta.1.getD i 0)).map
          fun raised => saturatingSub raised (delta.2.getD i 0)) balance =
        .ok (deltas.foldl (fun balance delta =>
          saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) balance)) ∧
    (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  induction deltas generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ => by cases state.balances.data[i]? <;> rfl, fun _ _ _ => rfl, fun _ => rfl⟩
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
    refine ⟨fun lt => ?_, fun lt balance held => ?_, fun ge => (later.2.2 ge).trans (first.2 ge)⟩
    · obtain ⟨balance, found, -, raised⟩ := first.1 lt
      rw [later.1 lt, raised, found]
      rfl
    · obtain ⟨balance', found, fits, raised⟩ := first.1 lt
      obtain rfl : balance' = balance := Option.some.inj (found.symm.trans held)
      -- The first reward fits, so the checked addition gives the wrapping sum.
      rw [List.foldlM_cons, addChecked_of_lt fits]
      exact later.2.1 lt _ raised

/-- Before Altair and after the first epoch, rewards and penalties apply the attestation deltas.

This holds when the step succeeds.

The balance of each validator becomes the old balance plus the reward, minus the penalty.

It stops at zero when the penalty is larger.

That old balance exists, and adding the reward to it stays below `2^64`.

The balances past the registry stay. -/
theorem processRewardsAndPenalties_balances_of_lt_altair {config : Config}
    (before : fork < .altair) (later : getCurrentEpoch state ≠ GENESIS_EPOCH)
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
  -- Before Gloas the type of the registry keeps it within its limit.
  have within : state.RegistryWithinLimit :=
    state.validators.bound (Nat.lt_trans before (by decide))
  exact ⟨rewards, penalties, found, applyAllDeltas_balances within applied⟩

/-- From Altair and after the first epoch, rewards and penalties apply the deltas of each flag.

They then apply the inactivity deltas.

This holds when the step succeeds on a registry within its limit.

Each set of deltas adds the reward of a validator to its balance, then subtracts its penalty.

The balance stops at zero when the penalty is larger.

Each of those sums stays below `2^64`, so a checked addition of each reward succeeds.

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
      (i < state.validators.data.size → ∀ balance, state.balances.data[i]? = some balance →
        (flagDeltas ++ [inactivityDeltas]).foldlM (fun balance delta =>
            (addChecked balance (delta.1.getD i 0)).map
              fun raised => saturatingSub raised (delta.2.getD i 0)) balance =
          .ok ((flagDeltas ++ [inactivityDeltas]).foldl (fun balance delta =>
            saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) balance)) ∧
      (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  simp only [processRewardsAndPenalties, later, altair, ↓reduceIte, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨flagDeltas, flagged, inactivityDeltas, penalized, applied⟩ := computed
  exact ⟨flagDeltas, inactivityDeltas, flagged, penalized,
    foldlM_applyAllDeltas_balances within applied⟩

end EthLib.Consensus
