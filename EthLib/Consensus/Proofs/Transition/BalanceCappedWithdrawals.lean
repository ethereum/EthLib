module

public import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: the withdrawals keep the capped balance of a validator that may not yet withdraw

The capped balance of a validator is the lesser of its balance and its largest effective balance.

The sweep of a block pays a validator that may not yet withdraw only the part above that cap.

It reads the balance left after the withdrawals before it, so a second visit takes nothing more.

A queued partial withdrawal can take more, so none may name the validator.

From Gloas the withdrawals of builders lower no balance of a validator.

So the withdrawals of a block keep the capped balance of such a validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- A withdrawal appended at the end adds its amount to the total of its validator only. -/
theorem appendWithdrawal_withdrawnFrom_eq {withdrawals after : Array Withdrawal}
    {next next' : WithdrawalIndex} {target : ValidatorIndex} {address : ExecutionAddress}
    {amount : Gwei}
    (computed : appendWithdrawal withdrawals next target address amount = .ok (after, next'))
    (prior : Array Withdrawal) (index : ValidatorIndex) :
    withdrawnFrom (prior ++ after) index = withdrawnFrom (prior ++ withdrawals) index +
      if target = index then amount.toNat else 0 := by
  simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at computed
  obtain ⟨_, _, rfl, rfl⟩ := computed
  rw [Array.append_push, withdrawnFrom_push]

/-- The loop of the queued partial withdrawals takes nothing from an index that no entry names. -/
theorem getPendingPartialWithdrawals_loop_unnamed {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} {index : ValidatorIndex} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ pending ∈ queue, pending.validatorIndex ≠ index) →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    withdrawnFrom (prior ++ result.1) index = withdrawnFrom (prior ++ withdrawals) index
  | [], _, _, _, _, _, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | pending :: rest, _, _, _, _, apart, computed => by
    have others : ∀ other ∈ rest, other.validatorIndex ≠ index :=
      fun other member => apart other (List.mem_cons_of_mem _ member)
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
        rw [getPendingPartialWithdrawals_loop_unnamed rest _ _ _ others rest',
          appendWithdrawal_withdrawnFrom_eq appendedOk]
        simp [apart pending List.mem_cons_self]
      · exact getPendingPartialWithdrawals_loop_unnamed rest _ _ _ others computed

/-- The loop of the sweep leaves a validator that may not yet withdraw its capped balance.

What the withdrawals take from it, plus its capped balance, stays within its balance. -/
theorem getValidatorsSweepWithdrawals_loop_capped {state : BeaconState preset fork}
    {prior : Array Withdrawal} {count limit : Nat} {index : ValidatorIndex}
    {validator : Validator} {balance : Gwei}
    (found : state.validators.data[index.toNat]? = some validator)
    (held : state.balances.data[index.toNat]? = some balance)
    (unwithdrawable : getCurrentEpoch state < validator.withdrawableEpoch) :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (target : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    withdrawnFrom (prior ++ withdrawals) index +
        min balance.toNat (withdrawalMaxEffectiveBalance preset fork validator).toNat ≤
      balance.toNat →
    getValidatorsSweepWithdrawals.loop state prior (getCurrentEpoch state) count limit visits
      withdrawals next target processed = .ok result →
    withdrawnFrom (prior ++ result.1) index +
        min balance.toNat (withdrawalMaxEffectiveBalance preset fork validator).toNat ≤
      balance.toNat
  | 0, _, _, _, _, _, bounded, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact bounded
  | visits + 1, withdrawals, _, target, _, _, bounded, computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact bounded
    simp only [bind_ok_iff] at computed
    obtain ⟨visited, visitedOk, left, leftOk, computed⟩ := computed
    have leftOk := liftAccessor_ok.mp leftOk
    -- The validator at the target is the tracked one when the target is its index.
    have same : target = index → visited = validator := by
      rintro rfl
      simp only [liftAccessor_ok, getValidator, found] at visitedOk
      exact (Except.ok.inj visitedOk).symm
    split at computed
    · rename_i full
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
      refine getValidatorsSweepWithdrawals_loop_capped found held unwithdrawable visits _ _ _ _
        ?_ rest
      rw [appendWithdrawal_withdrawnFrom_eq appendedOk]
      split
      · rename_i named
        rw [same named] at full
        simp only [isFullyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq] at full
        exact absurd full.1.2 (UInt64.not_le.mpr unwithdrawable)
      · simpa using bounded
    split at computed
    · rename_i excess
      simp only [isPartiallyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq]
        at excess
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
      refine getValidatorsSweepWithdrawals_loop_capped found held unwithdrawable visits _ _ _ _
        ?_ rest
      rw [appendWithdrawal_withdrawnFrom_eq appendedOk]
      split
      · rename_i named
        subst named
        have above := excess.2
        rw [same rfl] at above ⊢
        obtain ⟨read, readAt, sum⟩ := getBalanceAfterWithdrawals_ok leftOk
        rw [held, Option.some.injEq] at readAt
        subst readAt
        have lt := UInt64.lt_iff_toNat_lt.mp above
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)]
        omega
      · simpa using bounded
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
      obtain ⟨_, _, rest⟩ := computed
      exact getValidatorsSweepWithdrawals_loop_capped found held unwithdrawable visits _ _ _ _
        bounded rest

/-- The expected withdrawals leave a validator that may not yet withdraw its capped balance.

No queued partial withdrawal may name it.

This holds before Gloas, and from Gloas for an index that names no builder. -/
theorem getExpectedWithdrawals_capped {state : BeaconState preset fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals} {index : ValidatorIndex}
    (named : fork < .glamsterdam ∨ isBuilderIndex index = false)
    (computed : getExpectedWithdrawals state capella = .ok expected)
    {validator : Validator} (found : state.validators.data[index.toNat]? = some validator)
    {balance : Gwei} (held : state.balances.data[index.toNat]? = some balance)
    (unwithdrawable : getCurrentEpoch state < validator.withdrawableEpoch)
    (unqueued : ∀ electra : .pectra ≤ fork,
      ∀ pending ∈ (state.pendingPartialWithdrawals electra).data,
        pending.validatorIndex ≠ index) :
    withdrawnFrom expected.withdrawals index +
        min balance.toNat (withdrawalMaxEffectiveBalance preset fork validator).toNat ≤
      balance.toNat := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, _⟩, buildersOk, ⟨partials, index2, _⟩, partialsOk,
    ⟨buildersSweep, index3, _⟩, buildersSweepOk, ⟨sweep, index4, _⟩, sweepOk, rfl⟩ := computed
  -- The withdrawals before the sweep take nothing from the validator.
  have quiet : ∀ {first : Array Withdrawal}, withdrawnFrom first index = 0 →
      ∀ {start : WithdrawalIndex} {result : Array Withdrawal × WithdrawalIndex × Nat},
      (if electra : .pectra ≤ fork then
          getPendingPartialWithdrawals state electra start first
        else pure (#[], start, 0)) = .ok result →
      withdrawnFrom (first ++ result.1) index = 0 := by
    intro first zero start result ok
    split at ok
    · rename_i electra
      unfold getPendingPartialWithdrawals at ok
      simp only [bind_ok_iff, ensure_ok_iff] at ok
      obtain ⟨_, _, _, _, loopOk⟩ := ok
      rw [getPendingPartialWithdrawals_loop_unnamed _ _ _ _
        (fun pending member => unqueued electra pending (Array.mem_toList_iff.mp member)) loopOk]
      simpa using zero
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      simpa using zero
  have sweepFrom {first : Array Withdrawal} (zero : withdrawnFrom first index = 0)
      (sweepOk : getValidatorsSweepWithdrawals state capella index3 first =
        .ok (sweep, index4, ‹_›)) :
      withdrawnFrom (first ++ sweep) index +
          min balance.toNat (withdrawalMaxEffectiveBalance preset fork validator).toNat ≤
        balance.toNat := by
    unfold getValidatorsSweepWithdrawals at sweepOk
    simp only [bind_ok_iff, ensure_ok_iff] at sweepOk
    obtain ⟨_, _, loopOk⟩ := sweepOk
    exact getValidatorsSweepWithdrawals_loop_capped found held unwithdrawable _ _ _ _ _
      (by simpa [zero] using Nat.min_le_left _ _) loopOk
  by_cases gloas : .glamsterdam ≤ fork
  · -- From Gloas the withdrawals of builders take nothing from the validator.
    have notBuilder : isBuilderIndex index = false :=
      named.resolve_left (Nat.not_lt_of_le gloas)
    simp only [gloas, ↓reduceDIte] at buildersOk buildersSweepOk
    have one : AllBuilders builders := fun withdrawal member => by
      obtain ⟨_, -, named, -⟩ := getBuilderWithdrawals_pays buildersOk withdrawal member
      rw [named]
      exact isBuilderIndex_convertBuilderIndexToValidatorIndex _
    have three : AllBuilders buildersSweep := fun withdrawal member => by
      obtain ⟨k, inside, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp member)
      obtain ⟨_, _, _, named, -⟩ := getBuildersSweepWithdrawals_pays buildersSweepOk k inside
      rw [named]
      exact isBuilderIndex_convertBuilderIndexToValidatorIndex _
    have two := quiet (withdrawnFrom_of_allBuilders one notBuilder) partialsOk
    exact sweepFrom (by
      rw [withdrawnFrom_append, two, withdrawnFrom_of_allBuilders three notBuilder]) sweepOk
  · simp only [gloas, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at buildersOk buildersSweepOk
    obtain ⟨rfl, rfl, _⟩ := buildersOk
    obtain ⟨rfl, rfl, _⟩ := buildersSweepOk
    have two := quiet (first := #[]) (by simp [withdrawnFrom]) partialsOk
    exact sweepFrom (by rw [withdrawnFrom_append, two]; simp [withdrawnFrom]) sweepOk

/-- Withdrawals keep the balance at a position when each one that names it pays a builder. -/
theorem applyWithdrawals_unnamed {index : Nat} :
    ∀ (withdrawals : List Withdrawal) (state after : BeaconState preset fork),
    withdrawals.foldlM applyWithdrawal state = .ok after →
    (∀ withdrawal ∈ withdrawals, withdrawal.validatorIndex.toNat = index →
      .glamsterdam ≤ fork ∧ isBuilderIndex withdrawal.validatorIndex = true) →
    after.balances.data[index]? = state.balances.data[index]?
  | [], state, after, computed, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | withdrawal :: rest, state, after, computed, builders => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, computed⟩ := computed
    rw [applyWithdrawals_unnamed rest middle after computed
      fun other member => builders other (List.mem_cons_of_mem _ member)]
    unfold applyWithdrawal at step
    split at step
    · simp only [bind_ok_iff] at step
      obtain ⟨_, _, set⟩ := step
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      rfl
    · rename_i plain
      obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp step
      have apart : withdrawal.validatorIndex.toNat ≠ index :=
        fun same => plain (builders withdrawal List.mem_cons_self same)
      simp [BeaconState.putBalance, apart]

/-- The withdrawals of a block keep the capped balance of a validator that may not yet withdraw.

The cap is the largest effective balance of the validator.

No queued partial withdrawal may name it. -/
theorem processWithdrawals_capped {state after : BeaconState preset fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unwithdrawable : getCurrentEpoch state < validator.withdrawableEpoch)
    (unqueued : ∀ electra : .pectra ≤ fork,
      ∀ pending ∈ (state.pendingPartialWithdrawals electra).data,
        pending.validatorIndex.toNat ≠ index) :
    ∀ earlier, state.balances.data[index]? = some earlier →
      ∃ later, after.balances.data[index]? = some later ∧
        min earlier (withdrawalMaxEffectiveBalance preset fork validator) ≤
          min later (withdrawalMaxEffectiveBalance preset fork validator) := by
  intro earlier atEarlier
  -- A balance that the withdrawals lower to no less than its capped value keeps it.
  have kept : ∀ applied : BeaconState preset fork, after.balances = applied.balances →
      ∀ later, applied.balances.data[index]? = some later →
      min earlier.toNat (withdrawalMaxEffectiveBalance preset fork validator).toNat ≤
        later.toNat →
      ∃ later, after.balances.data[index]? = some later ∧
        min earlier (withdrawalMaxEffectiveBalance preset fork validator) ≤
          min later (withdrawalMaxEffectiveBalance preset fork validator) := by
    intro applied balances later atLater low
    refine ⟨later, by rw [balances]; exact atLater, ?_⟩
    rw [UInt64.le_iff_toNat_le, Uint64.toNat_min, Uint64.toNat_min]
    omega
  -- The withdrawals that the step applies are the expected ones, or there are none.
  have applies : ∀ expected, getExpectedWithdrawals state capella = .ok expected →
      applyExpectedWithdrawals state capella expected = .ok after →
      ∃ later, after.balances.data[index]? = some later ∧
        min earlier (withdrawalMaxEffectiveBalance preset fork validator) ≤
          min later (withdrawalMaxEffectiveBalance preset fork validator) := by
    intro expected expectedOk appliedOk
    obtain ⟨applied, appliedOk, balances, -⟩ := applyExpectedWithdrawals_balances appliedOk
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    by_cases plain : index < 2 ^ 64 ∧
        ¬ (.glamsterdam ≤ fork ∧ isBuilderIndex index.toUInt64 = true)
    · -- The index names the validator, and only the sweep pays it.
      have same : index.toUInt64.toNat = index := UInt64.toNat_ofNat_of_lt' plain.1
      have named : fork < .glamsterdam ∨ isBuilderIndex index.toUInt64 = false := by
        by_cases gloas : .glamsterdam ≤ fork
        · exact .inr (Bool.eq_false_iff.mpr fun builder => plain.2 ⟨gloas, builder⟩)
        · exact .inl (Nat.lt_of_not_le gloas)
      rw [← same] at found atEarlier
      have bound := getExpectedWithdrawals_capped named expectedOk found atEarlier
        unwithdrawable fun electra pending member equal =>
          unqueued electra pending member (by rw [equal, same])
      have lowered := applyWithdrawals_balance named _ _ _ _ appliedOk atEarlier
        (by simp only [Array.toArray_toList]; omega)
      rw [same] at lowered
      cases atLater : applied.balances.data[index]? with
      | none => simp [atLater] at lowered
      | some later =>
        simp only [atLater, Option.map_some, Option.some.injEq, Array.toArray_toList] at lowered
        exact kept applied balances later atLater (by omega)
    · -- No withdrawal lowers the balance at the index.
      have unchanged := applyWithdrawals_unnamed (index := index) _ _ _ appliedOk
        fun withdrawal _ atIndex => by
          have small : index < 2 ^ 64 := by
            have := UInt64.toNat_lt_size withdrawal.validatorIndex
            simp only [UInt64.size] at this
            omega
          have equal : withdrawal.validatorIndex = index.toUInt64 :=
            UInt64.toNat_inj.mp (by rw [UInt64.toNat_ofNat_of_lt' small, atIndex])
          rw [equal]
          exact Classical.not_not.mp fun builder => plain ⟨small, builder⟩
      exact kept applied balances earlier (unchanged.trans atEarlier) (Nat.min_le_left _ _)
  by_cases gloas : .glamsterdam ≤ fork
  · cases full : isParentBlockFull state gloas
    · rw [processWithdrawals_of_parentEmpty payload gloas full, Except.ok.injEq] at computed
      subst computed
      exact ⟨earlier, atEarlier, UInt64.le_refl _⟩
    · obtain ⟨expected, expectedOk, appliedOk, -⟩ :=
        processWithdrawals_recorded gloas full computed
      exact applies expected expectedOk appliedOk
  · obtain ⟨expected, expectedOk, -, appliedOk⟩ :=
      processWithdrawals_expected (Nat.lt_of_not_le gloas) computed
    exact applies expected expectedOk appliedOk

end EthLib.Consensus
