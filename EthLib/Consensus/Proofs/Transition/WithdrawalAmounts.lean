module

public import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: the amounts that the withdrawals take, at every fork from Capella

The step applies the expected withdrawals before Gloas, and from Gloas after a full parent.

They lower a validator's balance by their total for it, before Gloas or for a non-builder index.

That total never exceeds the balance, and a builder's balance stops at zero.

Each queued partial withdrawal and each withdrawal of the validator sweep pays an exact amount.

The sweep of validators names each validator at most once and comes last.

So a validator that it pays in full ends the step at zero.

One that it pays partially ends at exactly its largest effective balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-! ## The withdrawal step -/

/-- The withdrawal step applies the expected withdrawals, unless it changes nothing.

It applies them before Gloas, and from Gloas after a parent with its payload.

Only they change the balances and the builders.

From Gloas, after a parent without its payload, the step changes nothing. -/
private theorem processWithdrawals_applies {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    {expected : ExpectedWithdrawals}
    (expectedOk : getExpectedWithdrawals state capella = .ok expected)
    (full : ∀ gloas : .glamsterdam ≤ fork, isParentBlockFull state gloas = true) :
    ∃ applied, applyWithdrawals state expected.withdrawals = .ok applied ∧
      after.balances = applied.balances ∧ after.builders = applied.builders := by
  by_cases gloas : .glamsterdam ≤ fork
  · obtain ⟨found, foundOk, appliedOk, -⟩ := processWithdrawals_recorded gloas (full gloas) computed
    obtain rfl : found = expected := Except.ok.inj (foundOk.symm.trans expectedOk)
    exact applyExpectedWithdrawals_balances appliedOk
  · obtain ⟨found, foundOk, -, appliedOk⟩ :=
      processWithdrawals_expected (Nat.lt_of_not_le gloas) computed
    obtain rfl : found = expected := Except.ok.inj (foundOk.symm.trans expectedOk)
    exact applyExpectedWithdrawals_balances appliedOk

/-- The withdrawal step lowers the balance of a validator by exactly what it withdraws.

This holds at every fork from Capella: before Gloas, or for an index that names no builder.

The withdrawals are the expected ones.

The step applies them before Gloas, and from Gloas after a parent with its payload.

They never take more than the balance.

So the subtraction never stops at zero, and a validator that withdraws nothing keeps its balance.

Before Gloas the same holds for the withdrawals that the payload carries. -/
theorem processWithdrawals_balance_of_notBuilder {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    {expected : ExpectedWithdrawals}
    (expectedOk : getExpectedWithdrawals state capella = .ok expected)
    (full : ∀ gloas : .glamsterdam ≤ fork, isParentBlockFull state gloas = true)
    {index : ValidatorIndex} (named : fork < .glamsterdam ∨ isBuilderIndex index = false)
    {balance : Gwei} (found : state.balances.data[index.toNat]? = some balance) :
    withdrawnFrom expected.withdrawals index ≤ balance.toNat ∧
      (after.balances.data[index.toNat]?).map UInt64.toNat =
        some (balance.toNat - withdrawnFrom expected.withdrawals index) := by
  obtain ⟨applied, applyOk, balances, -⟩ := processWithdrawals_applies computed expectedOk full
  have bounded := getExpectedWithdrawals_withdrawnFrom named expectedOk found
  unfold applyWithdrawals at applyOk
  rw [← Array.foldlM_toList] at applyOk
  refine ⟨bounded, ?_⟩
  rw [balances]
  simpa using applyWithdrawals_balance named _ _ _ _ applyOk found
    (by simpa using bounded)

/-- The withdrawal step lowers the balance of each validator of the registry by what it withdraws.

The registry must be within its limit, and that limit at most `2^40`.

Then no validator index names a builder. -/
theorem processWithdrawals_balance_of_registry {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    {expected : ExpectedWithdrawals}
    (expectedOk : getExpectedWithdrawals state capella = .ok expected)
    (full : ∀ gloas : .glamsterdam ≤ fork, isParentBlockFull state gloas = true)
    (within : state.RegistryWithinLimit) (limit : preset.VALIDATOR_REGISTRY_LIMIT.toNat ≤ 2 ^ 40)
    {index : ValidatorIndex} (member : index.toNat < state.validators.data.size) {balance : Gwei}
    (found : state.balances.data[index.toNat]? = some balance) :
    withdrawnFrom expected.withdrawals index ≤ balance.toNat ∧
      (after.balances.data[index.toNat]?).map UInt64.toNat =
        some (balance.toNat - withdrawnFrom expected.withdrawals index) :=
  processWithdrawals_balance_of_notBuilder computed expectedOk full
    (.inr (isBuilderIndex_eq_false_of_registry within limit member)) found

/-! ## The balances of builders -/

/-- From Gloas, withdrawals lower the balance of a builder by their total for it, to at least zero.

The builder index must be below `2^40`, so that the index of its withdrawals names it alone. -/
theorem foldlM_applyWithdrawal_builder (gloas : .glamsterdam ≤ fork) {index : BuilderIndex}
    (small : index.toNat < 2 ^ 40) :
    ∀ (withdrawals : List Withdrawal) (state after : BeaconState preset fork),
    withdrawals.foldlM applyWithdrawal state = .ok after →
    ((after.builders gloas).data[index.toNat]?).map (·.balance.toNat) =
      ((state.builders gloas).data[index.toNat]?).map fun builder => builder.balance.toNat -
        withdrawnFrom withdrawals.toArray (convertBuilderIndexToValidatorIndex index)
  | [], state, after, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    cases (state.builders gloas).data[index.toNat]? <;> simp [withdrawnFrom]
  | withdrawal :: rest, state, after, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, computed⟩ := computed
    rw [foldlM_applyWithdrawal_builder gloas small rest middle after computed]
    simp only [withdrawnFrom_cons]
    unfold applyWithdrawal at step
    split at step
    · rename_i flagged
      simp only [bind_ok_iff] at step
      obtain ⟨builder, builderOk, set⟩ := step
      obtain ⟨inside, rfl⟩ := setBuilder_ok set
      -- The withdrawal names this builder exactly when its builder index is this one.
      have named := convertValidatorIndexToBuilderIndex_eq_iff flagged.2 small
      by_cases same : convertValidatorIndexToBuilderIndex withdrawal.validatorIndex = index
      · have equal := named.mp same
        simp only [getBuilder, same] at builderOk
        split at builderOk
        · rename_i read
          cases builderOk
          simp [BeaconState.putBuilder, read, equal, toNat_saturatingSub, Nat.sub_sub,
            convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex small]
        · cases builderOk
      · have apart : (convertValidatorIndexToBuilderIndex withdrawal.validatorIndex).toNat ≠
            index.toNat := fun h => same (UInt64.toNat_inj.mp h)
        have other : withdrawal.validatorIndex ≠ convertBuilderIndexToValidatorIndex index :=
          fun h => same (named.mpr h)
        simp [BeaconState.putBuilder, apart, other]
    · -- A withdrawal of a validator keeps the builders.
      rename_i notFlagged
      have other : withdrawal.validatorIndex ≠ convertBuilderIndexToValidatorIndex index :=
        fun h => notFlagged ⟨gloas, h ▸ isBuilderIndex_convertBuilderIndexToValidatorIndex index⟩
      simp only [decreaseBalance, bind_ok_iff] at step
      obtain ⟨_, _, set⟩ := step
      obtain ⟨_, rfl⟩ := setBalance_ok set
      simp [BeaconState.putBalance, other]

/-- From Gloas, after a parent with its payload, the step lowers each builder's balance.

It lowers it by what the builder withdraws among the expected withdrawals, and stops at zero.

The builder index must be below `2^40`.

The step does not check a queued payment of a builder against its balance. -/
theorem processWithdrawals_builder {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (gloas : .glamsterdam ≤ fork) (full : isParentBlockFull state gloas = true)
    (computed : processWithdrawals state capella payload = .ok after)
    {expected : ExpectedWithdrawals}
    (expectedOk : getExpectedWithdrawals state capella = .ok expected) {index : BuilderIndex}
    (small : index.toNat < 2 ^ 40) :
    ((after.builders gloas).data[index.toNat]?).map (·.balance.toNat) =
      ((state.builders gloas).data[index.toNat]?).map fun builder => builder.balance.toNat -
        withdrawnFrom expected.withdrawals (convertBuilderIndexToValidatorIndex index) := by
  obtain ⟨applied, applyOk, -, builders⟩ :=
    processWithdrawals_applies computed expectedOk fun _ => full
  unfold applyWithdrawals at applyOk
  rw [← Array.foldlM_toList] at applyOk
  rw [builders]
  simpa using foldlM_applyWithdrawal_builder gloas small _ _ _ applyOk

/-! ## The bounds of the sweeps -/

/-- The sweep of validators visits at most the visits it is given. -/
theorem getValidatorsSweepWithdrawals_loop_processed {prior : Array Withdrawal} {epoch : Epoch}
    {count limit : Nat} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getValidatorsSweepWithdrawals.loop state prior epoch count limit visits withdrawals next index
      processed = .ok result →
    result.2.2 ≤ processed + visits
  | 0, _, _, _, _, _, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | visits + 1, _, _, _, _, _, computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, _, _, _, rest⟩ := computed
        have := getValidatorsSweepWithdrawals_loop_processed visits _ _ _ _ rest
        omega
      · split at computed
        · simp only [bind_ok_iff, liftAccessor_ok] at computed
          obtain ⟨_, _, _, _, rest⟩ := computed
          have := getValidatorsSweepWithdrawals_loop_processed visits _ _ _ _ rest
          omega
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left']
            at computed
          obtain ⟨_, _, rest⟩ := computed
          have := getValidatorsSweepWithdrawals_loop_processed visits _ _ _ _ rest
          omega

/-- The sweep of builders visits at most the visits it is given. -/
theorem getBuildersSweepWithdrawals_loop_processed {gloas : .glamsterdam ≤ fork}
    {prior : Array Withdrawal} {epoch : Epoch} {count : Nat} {limit : UInt64} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getBuildersSweepWithdrawals.loop state gloas prior epoch count limit visits withdrawals next
      index processed = .ok result →
    result.2.2 ≤ processed + visits
  | 0, _, _, _, _, _, computed => by
    simp only [getBuildersSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | visits + 1, _, _, _, _, _, computed => by
    simp only [getBuildersSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, _, _, _, rest⟩ := computed
        have := getBuildersSweepWithdrawals_loop_processed visits _ _ _ _ rest
        omega
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
        obtain ⟨_, _, rest⟩ := computed
        have := getBuildersSweepWithdrawals_loop_processed visits _ _ _ _ rest
        omega

/-- The queued partial withdrawals that a payload reads number at most the queue. -/
theorem getPendingPartialWithdrawals_loop_processed {prior : Array Withdrawal} {epoch : Epoch}
    {limit : Nat} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    result.2.2 ≤ processed + queue.length
  | [], _, _, _, _, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | _ :: rest, _, _, _, _, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, _, rest'⟩ := computed
        have := getPendingPartialWithdrawals_loop_processed rest _ _ _ rest'
        simp only [List.length_cons]
        omega
      · have := getPendingPartialWithdrawals_loop_processed rest _ _ _ computed
        simp only [List.length_cons]
        omega

/-- The queued builder withdrawals that a payload reads number at most the queue. -/
theorem getBuilderWithdrawals_loop_processed {prior : Array Withdrawal} {limit : UInt64} :
    ∀ (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getBuilderWithdrawals.loop prior limit queue withdrawals next processed = .ok result →
    result.2.2 ≤ processed + queue.length
  | [], _, _, _, _, computed => by
    simp only [getBuilderWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | _ :: rest, _, _, _, _, computed => by
    simp only [getBuilderWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, rest'⟩ := computed
      have := getBuilderWithdrawals_loop_processed rest _ _ _ rest'
      simp only [List.length_cons]
      omega

/-- The bounds of the parts of the expected withdrawals.

The sweep visits at most the registry and at most the most validators per sweep.

From Gloas the sweep of builders visits at most their registry and the most builders per sweep.

From Electra the queued partial withdrawals that are read number at most the queue.

From Gloas the queued builder withdrawals that are read number at most their queue. -/
theorem getExpectedWithdrawals_bounds {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    expected.processedSweepWithdrawalsCount ≤
        min state.validators.data.size preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP.toNat ∧
      (∀ gloas : .glamsterdam ≤ fork, expected.processedBuildersSweepCount ≤
        min (state.builders gloas).data.size preset.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP.toNat) ∧
      (∀ electra : .pectra ≤ fork, expected.processedPartialWithdrawalsCount ≤
        (state.pendingPartialWithdrawals electra).data.size) ∧
      (∀ gloas : .glamsterdam ≤ fork, expected.processedBuilderWithdrawalsCount ≤
        (state.builderPendingWithdrawals gloas).data.size) := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, builderCount⟩, buildersOk, ⟨partials, index2, partialCount⟩,
    partialsOk, ⟨buildersSweep, index3, buildersSweepCount⟩, buildersSweepOk,
    ⟨sweep, index4, sweepCount⟩, sweepOk, rfl⟩ := computed
  refine ⟨?_, fun gloas => ?_, fun electra => ?_, fun gloas => ?_⟩
  · unfold getValidatorsSweepWithdrawals at sweepOk
    simp only [bind_ok_iff, ensure_ok_iff] at sweepOk
    obtain ⟨_, _, loopOk⟩ := sweepOk
    simpa using getValidatorsSweepWithdrawals_loop_processed _ _ _ _ _ loopOk
  · simp only [gloas, ↓reduceDIte] at buildersSweepOk
    unfold getBuildersSweepWithdrawals at buildersSweepOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersSweepOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersSweepOk
    simpa using getBuildersSweepWithdrawals_loop_processed _ _ _ _ _ loopOk
  · simp only [electra, ↓reduceDIte] at partialsOk
    unfold getPendingPartialWithdrawals at partialsOk
    simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
    obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
    simpa using getPendingPartialWithdrawals_loop_processed _ _ _ _ loopOk
  · simp only [gloas, ↓reduceDIte] at buildersOk
    unfold getBuilderWithdrawals at buildersOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersOk
    simpa using getBuilderWithdrawals_loop_processed _ _ _ _ loopOk

/-! ## What the sweep pays each validator -/

/-- What the sweep pays one validator, after the withdrawals of the payload before it.

The validator's balance left after those withdrawals is the amount it can still withdraw.

A fully withdrawable validator withdraws all of it.

Otherwise a partially withdrawable one withdraws the part above its largest effective balance. -/
private def SweepPays (state : BeaconState preset fork) (epoch : Epoch) (before : Array Withdrawal)
    (withdrawal : Withdrawal) : Prop :=
  ∃ validator left, getValidator state withdrawal.validatorIndex = .ok validator ∧
    getBalanceAfterWithdrawals state withdrawal.validatorIndex before = .ok left ∧
    ((isFullyWithdrawableValidator fork validator left epoch = true ∧ withdrawal.amount = left) ∨
      (isFullyWithdrawableValidator fork validator left epoch = false ∧
        isPartiallyWithdrawableValidator preset fork validator left = true ∧
        withdrawal.amount = left - withdrawalMaxEffectiveBalance preset fork validator))

/-- Two positions of a sweep that wraps around a registry name different validators.

The positions are fewer than the size of the registry. -/
private theorem mod_ne_of_lt {start t u count : Nat} (lt : t < u) (small : u < count) :
    (start + t) % count ≠ (start + u) % count := by
  intro same
  have divides : count ∣ (start + u) - (start + t) :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq same.symm)
  have := Nat.le_of_dvd (by omega) divides
  omega

/-- The loop of the sweep pays each validator it visits as a full or partial sweep, at most once.

The sweep starts at a validator of the registry, and wraps around it.

It visits fewer validators than the registry holds. -/
private theorem getValidatorsSweepWithdrawals_loop_pays {prior : Array Withdrawal} {epoch : Epoch}
    {limit : Nat} (within : state.RegistryWithinLimit) {start : Nat}
    (first : start < state.validators.data.size) :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    index.toNat = (start + processed) % state.validators.data.size →
    processed + visits ≤ state.validators.data.size →
    (∀ k (inside : k < withdrawals.size),
      SweepPays state epoch (prior ++ withdrawals.extract 0 k) withdrawals[k]) →
    (∀ k (inside : k < withdrawals.size), ∃ t < processed,
      withdrawals[k].validatorIndex.toNat = (start + t) % state.validators.data.size) →
    (withdrawals.toList.map (·.validatorIndex.toNat)).Nodup →
    getValidatorsSweepWithdrawals.loop state prior epoch state.validators.data.size limit visits
      withdrawals next index processed = .ok result →
    (∀ k (inside : k < result.1.size),
      SweepPays state epoch (prior ++ result.1.extract 0 k) result.1[k]) ∧
    (result.1.toList.map (·.validatorIndex.toNat)).Nodup
  | 0, _, _, _, _, _, _, _, pays, _, distinct, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨pays, distinct⟩
  | visits + 1, withdrawals, next, index, processed, _, position, room, pays, named, distinct,
      computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact ⟨pays, distinct⟩
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, validatorOk, left, leftOk, computed⟩ := computed
    -- The next visit is the next validator of the registry, wrapping at its end.
    have advance : ∀ following : ValidatorIndex, following.toNat = index.toNat + 1 →
        ((following.toNat % state.validators.data.size).toUInt64).toNat =
          (start + (processed + 1)) % state.validators.data.size := by
      intro following value
      rw [toNat_toUInt64_of_lt within (Nat.mod_lt _ (by omega)), value, position,
        Nat.mod_add_mod]
      rfl
    -- A withdrawal appended for this validator keeps what the loop keeps.
    have append : ∀ {appended : Array Withdrawal} {following : WithdrawalIndex} {amount : Gwei},
        appendWithdrawal withdrawals next index (credentialAddress validator.withdrawalCredentials)
          amount = .ok (appended, following) →
        (isFullyWithdrawableValidator fork validator left epoch = true ∧ amount = left) ∨
          (isFullyWithdrawableValidator fork validator left epoch = false ∧
            isPartiallyWithdrawableValidator preset fork validator left = true ∧
            amount = left - withdrawalMaxEffectiveBalance preset fork validator) →
        (∀ k (inside : k < appended.size),
          SweepPays state epoch (prior ++ appended.extract 0 k) appended[k]) ∧
        (∀ k (inside : k < appended.size), ∃ t < processed + 1,
          appended[k].validatorIndex.toNat = (start + t) % state.validators.data.size) ∧
        (appended.toList.map (·.validatorIndex.toNat)).Nodup := by
      intro appended following amount appendedOk kind
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      refine ⟨fun k inside => ?_, fun k inside => ?_, ?_⟩
      · simp only [Array.size_push] at inside
        by_cases old : k < withdrawals.size
        · rw [Array.getElem_push_lt old, Array.extract_push_of_le (by omega)]
          exact pays k old
        · obtain rfl : k = withdrawals.size := by omega
          rw [Array.getElem_push_eq, Array.extract_push_of_le (Nat.le_refl _),
            Array.extract_eq_self_of_le (Nat.le_refl _)]
          exact ⟨validator, left, validatorOk, leftOk, kind⟩
      · simp only [Array.size_push] at inside
        by_cases old : k < withdrawals.size
        · rw [Array.getElem_push_lt old]
          obtain ⟨t, earlier, value⟩ := named k old
          exact ⟨t, by omega, value⟩
        · obtain rfl : k = withdrawals.size := by omega
          rw [Array.getElem_push_eq]
          exact ⟨processed, by omega, position⟩
      · rw [Array.toList_push, List.map_append, List.nodup_append]
        refine ⟨distinct, by simp, fun earlier member last isLast equal => ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at isLast
        obtain ⟨withdrawal, listed, rfl⟩ := List.mem_map.mp member
        obtain ⟨k, inside, found⟩ := List.getElem_of_mem listed
        rw [Array.getElem_toList] at found
        obtain ⟨t, earlier, value⟩ := named k (by simpa using inside)
        rw [← found, value, isLast, position] at equal
        exact mod_ne_of_lt earlier (by omega) equal
    split at computed
    · rename_i full
      simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
        addChecked_ok_iff] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, nextIndex, ⟨_, nextValue⟩, rest⟩ := computed
      obtain ⟨pays', named', distinct'⟩ := append appendedOk (.inl ⟨full, rfl⟩)
      exact getValidatorsSweepWithdrawals_loop_pays within first visits _ _ _ _
        (advance nextIndex (by simpa using nextValue)) (by omega) pays' named' distinct' rest
    · rename_i notFull
      split at computed
      · rename_i excess
        simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
          addChecked_ok_iff] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, nextIndex, ⟨_, nextValue⟩, rest⟩ := computed
        obtain ⟨pays', named', distinct'⟩ :=
          append appendedOk (.inr ⟨by simpa using notFull, excess, rfl⟩)
        exact getValidatorsSweepWithdrawals_loop_pays within first visits _ _ _ _
          (advance nextIndex (by simpa using nextValue)) (by omega) pays' named' distinct' rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left',
          liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at computed
        obtain ⟨nextIndex, ⟨_, nextValue⟩, rest⟩ := computed
        exact getValidatorsSweepWithdrawals_loop_pays within first visits _ _ _ _
          (advance nextIndex (by simpa using nextValue)) (by omega) pays
          (fun k inside => by
            obtain ⟨t, earlier, value⟩ := named k inside
            exact ⟨t, by omega, value⟩) distinct rest

/-- A sweep that starts past the registry pays nothing, or fails at its first visit. -/
private theorem getValidatorsSweepWithdrawals_loop_outside {prior : Array Withdrawal}
    {epoch : Epoch} {count limit : Nat} {visits : Nat} {next : WithdrawalIndex}
    {index : ValidatorIndex} {result : Array Withdrawal × WithdrawalIndex × Nat}
    (outside : state.validators.data.size ≤ index.toNat)
    (computed : getValidatorsSweepWithdrawals.loop state prior epoch count limit visits #[] next
      index 0 = .ok result) :
    result.1 = #[] := by
  cases visits with
  | zero =>
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    rw [← computed]
  | succ visits =>
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      rw [← computed]
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, found, _⟩ := computed
      simp [getValidator, Array.getElem?_eq_none outside] at found

/-- The sweep pays each validator it visits at most once. -/
private theorem getValidatorsSweepWithdrawals_sweepPays {capella : .shapella ≤ fork}
    (within : state.RegistryWithinLimit) {start : WithdrawalIndex}
    {prior sweep : Array Withdrawal} {next : WithdrawalIndex} {processed : Nat}
    (computed : getValidatorsSweepWithdrawals state capella start prior =
      .ok (sweep, next, processed)) :
    (∀ k (inside : k < sweep.size),
      SweepPays state (getCurrentEpoch state) (prior ++ sweep.extract 0 k) sweep[k]) ∧
    (sweep.toList.map (·.validatorIndex.toNat)).Nodup := by
  unfold getValidatorsSweepWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, loopOk⟩ := computed
  by_cases first : (state.nextWithdrawalValidatorIndex capella).toNat < state.validators.data.size
  · exact getValidatorsSweepWithdrawals_loop_pays within first _ _ _ _ _
      (by simp [Nat.mod_eq_of_lt first]) (by simpa using Nat.min_le_left _ _)
      (fun _ inside => absurd inside (by simp)) (fun _ inside => absurd inside (by simp))
      (by simp) loopOk
  · have empty := getValidatorsSweepWithdrawals_loop_outside (Nat.le_of_not_lt first) loopOk
    simp only at empty
    subst empty
    exact ⟨fun _ inside => absurd inside (by simp), by simp⟩

/-- For a registry within its limit, what each withdrawal of the sweep pays.

Each amount is read from the balance left after the withdrawals before it.

A fully withdrawable validator withdraws all of that balance.

Otherwise a partially withdrawable one withdraws the part above its largest effective balance.

The sweep names each validator at most once. -/
theorem getValidatorsSweepWithdrawals_pays {capella : .shapella ≤ fork}
    (within : state.RegistryWithinLimit) {start : WithdrawalIndex}
    {prior sweep : Array Withdrawal} {next : WithdrawalIndex} {processed : Nat}
    (computed : getValidatorsSweepWithdrawals state capella start prior =
      .ok (sweep, next, processed)) :
    (∀ k (inside : k < sweep.size),
      ∃ validator left, getValidator state sweep[k].validatorIndex = .ok validator ∧
        getBalanceAfterWithdrawals state sweep[k].validatorIndex (prior ++ sweep.extract 0 k) =
          .ok left ∧
        ((isFullyWithdrawableValidator fork validator left (getCurrentEpoch state) = true ∧
            sweep[k].amount = left) ∨
          (isFullyWithdrawableValidator fork validator left (getCurrentEpoch state) = false ∧
            isPartiallyWithdrawableValidator preset fork validator left = true ∧
            sweep[k].amount = left - withdrawalMaxEffectiveBalance preset fork validator))) ∧
    (sweep.toList.map (·.validatorIndex.toNat)).Nodup :=
  getValidatorsSweepWithdrawals_sweepPays within computed

/-- The total of a validator over withdrawals that name each validator once.

It is the total over those before its own, plus its own amount. -/
private theorem withdrawnFrom_split {sweep : Array Withdrawal}
    (distinct : (sweep.toList.map (·.validatorIndex.toNat)).Nodup) {k : Nat}
    (inside : k < sweep.size) :
    withdrawnFrom sweep sweep[k].validatorIndex =
      withdrawnFrom (sweep.extract 0 k) sweep[k].validatorIndex + sweep[k].amount.toNat := by
  have insideList : k < sweep.toList.length := by simpa using inside
  have pieces : sweep.toList = sweep.toList.take k ++
      sweep.toList[k] :: sweep.toList.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons insideList, List.take_append_drop]
  -- No withdrawal after this one names the same validator.
  have later : ∀ other ∈ sweep.toList.drop (k + 1),
      other.validatorIndex ≠ sweep[k].validatorIndex := by
    intro other member same
    have whole : (sweep.toList.take (k + 1) ++ sweep.toList.drop (k + 1)).map
        (·.validatorIndex.toNat) |>.Nodup := by
      rw [List.take_append_drop]
      exact distinct
    rw [List.map_append, List.nodup_append] at whole
    refine whole.2.2 _ (List.mem_map_of_mem (List.getElem_mem (l := sweep.toList.take (k + 1))
      (n := k) (by simp; omega))) _ (List.mem_map_of_mem member) ?_
    simp [same]
  unfold withdrawnFrom
  rw [pieces]
  simp only [List.filter_append, List.filter_cons, Array.getElem_toList, decide_true,
    ↓reduceIte, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  rw [List.filter_eq_nil_iff.mpr fun other member same => later other member
    (of_decide_eq_true same)]
  simp [Array.toList_extract, List.extract_eq_take_drop]

/-- A validator that the sweep pays withdraws, in all, its balance or its excess.

The excess is the part above its largest effective balance.

All its other withdrawals come before the sweep pays it. -/
private theorem withdrawnFrom_of_sweepPays {epoch : Epoch} {prior sweep : Array Withdrawal}
    (pays : ∀ k (inside : k < sweep.size),
      SweepPays state epoch (prior ++ sweep.extract 0 k) sweep[k])
    (distinct : (sweep.toList.map (·.validatorIndex.toNat)).Nodup) {k : Nat}
    (inside : k < sweep.size) :
    ∃ validator balance left, getValidator state sweep[k].validatorIndex = .ok validator ∧
      state.balances.data[sweep[k].validatorIndex.toNat]? = some balance ∧
      getBalanceAfterWithdrawals state sweep[k].validatorIndex (prior ++ sweep.extract 0 k) =
        .ok left ∧
      ((isFullyWithdrawableValidator fork validator left epoch = true ∧
          withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex = balance.toNat) ∨
        (isFullyWithdrawableValidator fork validator left epoch = false ∧
          isPartiallyWithdrawableValidator preset fork validator left = true ∧
          withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex = balance.toNat -
            (withdrawalMaxEffectiveBalance preset fork validator).toNat ∧
          (withdrawalMaxEffectiveBalance preset fork validator).toNat < balance.toNat)) := by
  obtain ⟨validator, left, validatorOk, leftOk, kind⟩ := pays k inside
  obtain ⟨balance, found, sum⟩ := getBalanceAfterWithdrawals_ok leftOk
  -- The sweep pays no later withdrawal to this validator.
  have total : withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex =
      withdrawnFrom (prior ++ sweep.extract 0 k) sweep[k].validatorIndex +
        sweep[k].amount.toNat := by
    rw [withdrawnFrom_append, withdrawnFrom_append, Nat.add_assoc]
    congr 1
    exact withdrawnFrom_split distinct inside
  refine ⟨validator, balance, left, validatorOk, found, leftOk, ?_⟩
  rcases kind with ⟨full, amount⟩ | ⟨notFull, excess, amount⟩
  · refine .inl ⟨full, ?_⟩
    rw [total, amount]
    omega
  · simp only [isPartiallyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq]
      at excess
    have above := UInt64.lt_iff_toNat_lt.mp excess.2
    refine .inr ⟨notFull, ?_, ?_, by omega⟩
    · simp [isPartiallyWithdrawableValidator, excess.1.1, excess.1.2, excess.2]
    · rw [total, amount, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt excess.2)]
      omega

/-- For a registry within its limit, the sweep leaves each validator it pays at a fixed balance.

The registry limit must be at most `2^40`.

The sweep is the last part of the expected withdrawals, after the withdrawals before it.

The step applies the expected withdrawals before Gloas, and from Gloas after a full parent.

A validator that the sweep pays in full ends the step at zero.

One that it pays partially ends at exactly its largest effective balance.

Whether it pays in full or partially is read from the balance left after the earlier withdrawals.

Those are the queued withdrawals and the earlier visits of the sweep. -/
theorem processWithdrawals_sweep {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (within : state.RegistryWithinLimit) (limit : preset.VALIDATOR_REGISTRY_LIMIT.toNat ≤ 2 ^ 40)
    {expected : ExpectedWithdrawals}
    (expectedOk : getExpectedWithdrawals state capella = .ok expected)
    (full : ∀ gloas : .glamsterdam ≤ fork, isParentBlockFull state gloas = true)
    {start next : WithdrawalIndex} {prior sweep : Array Withdrawal} {processed : Nat}
    (sweepOk : getValidatorsSweepWithdrawals state capella start prior =
      .ok (sweep, next, processed))
    (split : expected.withdrawals = prior ++ sweep) :
    ∀ k (inside : k < sweep.size), ∃ validator left final,
      getValidator state sweep[k].validatorIndex = .ok validator ∧
      getBalanceAfterWithdrawals state sweep[k].validatorIndex (prior ++ sweep.extract 0 k) =
        .ok left ∧
      after.balances.data[sweep[k].validatorIndex.toNat]? = some final ∧
      ((isFullyWithdrawableValidator fork validator left (getCurrentEpoch state) = true ∧
          final = 0) ∨
        (isFullyWithdrawableValidator fork validator left (getCurrentEpoch state) = false ∧
          isPartiallyWithdrawableValidator preset fork validator left = true ∧
          final = withdrawalMaxEffectiveBalance preset fork validator)) := by
  intro k inside
  obtain ⟨pays, distinct⟩ := getValidatorsSweepWithdrawals_sweepPays within sweepOk
  obtain ⟨validator, balance, left, validatorOk, found, leftOk, kind⟩ :=
    withdrawnFrom_of_sweepPays pays distinct inside
  have member : sweep[k].validatorIndex.toNat < state.validators.data.size :=
    (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp validatorOk)).1
  obtain ⟨_, lowered⟩ :=
    processWithdrawals_balance_of_registry computed expectedOk full within limit member found
  rw [split] at lowered
  obtain ⟨final, finalFound, finalValue⟩ : ∃ final,
      after.balances.data[sweep[k].validatorIndex.toNat]? = some final ∧
        final.toNat = balance.toNat - withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex := by
    cases read : after.balances.data[sweep[k].validatorIndex.toNat]? with
    | none => rw [read] at lowered; cases lowered
    | some final =>
      rw [read, Option.map_some, Option.some.injEq] at lowered
      exact ⟨final, rfl, lowered⟩
  refine ⟨validator, left, final, validatorOk, leftOk, finalFound, ?_⟩
  rcases kind with ⟨full, total⟩ | ⟨notFull, excess, total, above⟩
  · exact .inl ⟨full, UInt64.toNat_inj.mp (by rw [finalValue, total]; simp)⟩
  · exact .inr ⟨notFull, excess, UInt64.toNat_inj.mp (by rw [finalValue, total]; omega)⟩

/-! ## What a queued partial withdrawal pays -/

/-- What a queued partial withdrawal pays, after the withdrawals of the payload before it.

It is a withdrawable entry of the queue, for a validator still eligible.

It pays the balance left above the activation balance, or the amount asked if that is less. -/
private def PartialPays (state : BeaconState preset fork) (epoch : Epoch)
    (queue : List PendingPartialWithdrawal) (before : Array Withdrawal)
    (withdrawal : Withdrawal) : Prop :=
  ∃ pending ∈ queue, ∃ validator left, pending.withdrawableEpoch ≤ epoch ∧
    withdrawal.validatorIndex = pending.validatorIndex ∧
    getValidator state pending.validatorIndex = .ok validator ∧
    getBalanceAfterWithdrawals state pending.validatorIndex before = .ok left ∧
    isEligibleForPartialWithdrawals preset validator left = true ∧
    withdrawal.amount = min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount

/-- Each withdrawal of the loop of the queued partial withdrawals pays by the rule above. -/
private theorem getPendingPartialWithdrawals_loop_pays {prior : Array Withdrawal} {epoch : Epoch}
    {limit : Nat} {whole : List PendingPartialWithdrawal} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ pending ∈ queue, pending ∈ whole) →
    (∀ k (inside : k < withdrawals.size),
      PartialPays state epoch whole (prior ++ withdrawals.extract 0 k) withdrawals[k]) →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    ∀ k (inside : k < result.1.size),
      PartialPays state epoch whole (prior ++ result.1.extract 0 k) result.1[k]
  | [], _, _, _, _, _, pays, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact pays
  | pending :: rest, withdrawals, next, _, _, within, pays, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact pays
    rename_i ready
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, validatorOk, left, leftOk, computed⟩ := computed
    have rest' : ∀ other ∈ rest, other ∈ whole :=
      fun other member => within other (List.mem_cons_of_mem _ member)
    split at computed
    · rename_i eligible
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, loopOk⟩ := computed
      refine getPendingPartialWithdrawals_loop_pays rest _ _ _ rest' (fun k inside => ?_) loopOk
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      simp only [Array.size_push] at inside
      by_cases old : k < withdrawals.size
      · rw [Array.getElem_push_lt old, Array.extract_push_of_le (by omega)]
        exact pays k old
      · obtain rfl : k = withdrawals.size := by omega
        rw [Array.getElem_push_eq, Array.extract_push_of_le (Nat.le_refl _),
          Array.extract_eq_self_of_le (Nat.le_refl _)]
        have ready' : pending.withdrawableEpoch ≤ epoch := by
          simp only [not_or, Nat.not_le] at ready
          exact UInt64.not_lt.mp ready.1
        exact ⟨pending, within pending List.mem_cons_self, validator, left, ready', rfl,
          validatorOk, leftOk, eligible, rfl⟩
    · exact getPendingPartialWithdrawals_loop_pays rest _ _ _ rest' pays computed

/-- From Electra, each queued partial withdrawal that a payload pays follows that rule. -/
private theorem getPendingPartialWithdrawals_partialPays {electra : .pectra ≤ fork}
    {start : WithdrawalIndex}
    {prior partials : Array Withdrawal} {next : WithdrawalIndex} {processed : Nat}
    (computed : getPendingPartialWithdrawals state electra start prior =
      .ok (partials, next, processed)) :
    ∀ k (inside : k < partials.size), PartialPays state (getCurrentEpoch state)
      (state.pendingPartialWithdrawals electra).data.toList (prior ++ partials.extract 0 k)
      partials[k] := by
  unfold getPendingPartialWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, loopOk⟩ := computed
  exact getPendingPartialWithdrawals_loop_pays _ _ _ _ (fun _ member => member)
    (fun _ inside => absurd inside (by simp)) loopOk

/-- From Electra, what each queued partial withdrawal of a payload pays.

It is a withdrawable entry of the queue of the state, for a validator still eligible.

It pays the balance left above the activation balance, or the amount asked if that is less.

The balance left is read after the withdrawals before it. -/
theorem getPendingPartialWithdrawals_pays {electra : .pectra ≤ fork} {start : WithdrawalIndex}
    {prior partials : Array Withdrawal} {next : WithdrawalIndex} {processed : Nat}
    (computed : getPendingPartialWithdrawals state electra start prior =
      .ok (partials, next, processed)) :
    ∀ k (inside : k < partials.size),
      ∃ pending ∈ (state.pendingPartialWithdrawals electra).data.toList, ∃ validator left,
        pending.withdrawableEpoch ≤ getCurrentEpoch state ∧
        partials[k].validatorIndex = pending.validatorIndex ∧
        getValidator state pending.validatorIndex = .ok validator ∧
        getBalanceAfterWithdrawals state pending.validatorIndex (prior ++ partials.extract 0 k) =
          .ok left ∧
        isEligibleForPartialWithdrawals preset validator left = true ∧
        partials[k].amount = min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount :=
  getPendingPartialWithdrawals_partialPays computed

/-! ## Every withdrawal of a payload -/

/-- The expected withdrawals are the four parts that their calls compute, in payload order.

From Gloas, the queued builder withdrawals come first.

The count of queued builder withdrawals read is the count of that first part.

From Electra, the queued partial withdrawals follow.

From Gloas, the sweep of builders follows.

The sweep of validators comes last.

Each part reads the parts before it.

Before its fork a part is empty and keeps the withdrawal index.

Theorems above state what the partial withdrawals and the validator sweep pay.

The withdrawal proofs state what the builder parts pay. -/
theorem getExpectedWithdrawals_parts {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    ∃ (builders partials buildersSweep sweep : Array Withdrawal)
      (index1 index2 index3 index4 : WithdrawalIndex) (count1 count2 count3 count4 : Nat),
      expected.withdrawals = builders ++ partials ++ buildersSweep ++ sweep ∧
      expected.processedBuilderWithdrawalsCount = count1 ∧
      (∀ gloas : .glamsterdam ≤ fork, getBuilderWithdrawals state gloas
        (state.nextWithdrawalIndex capella) #[] = .ok (builders, index1, count1)) ∧
      (fork < .glamsterdam → builders = #[] ∧ index1 = state.nextWithdrawalIndex capella) ∧
      (∀ electra : .pectra ≤ fork, getPendingPartialWithdrawals state electra index1 builders =
        .ok (partials, index2, count2)) ∧
      (fork < .pectra → partials = #[] ∧ index2 = index1) ∧
      (∀ gloas : .glamsterdam ≤ fork, getBuildersSweepWithdrawals state gloas index2
        (builders ++ partials) = .ok (buildersSweep, index3, count3)) ∧
      (fork < .glamsterdam → buildersSweep = #[] ∧ index3 = index2) ∧
      getValidatorsSweepWithdrawals state capella index3 (builders ++ partials ++ buildersSweep) =
        .ok (sweep, index4, count4) := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, count1⟩, buildersOk, ⟨partials, index2, count2⟩, partialsOk,
    ⟨buildersSweep, index3, count3⟩, buildersSweepOk, ⟨sweep, index4, count4⟩, sweepOk, rfl⟩ :=
    computed
  refine ⟨builders, partials, buildersSweep, sweep, index1, index2, index3, index4, count1,
    count2, count3, count4, rfl, rfl, fun gloas => ?_, fun before => ?_, fun electra => ?_,
    fun before => ?_, fun gloas => ?_, fun before => ?_, sweepOk⟩
  · simpa only [gloas, ↓reduceDIte] using buildersOk
  · have outside : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    simp only [outside, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at buildersOk
    exact ⟨buildersOk.1.symm, buildersOk.2.1.symm⟩
  · simpa only [electra, ↓reduceDIte] using partialsOk
  · have outside : ¬ .pectra ≤ fork := Nat.not_le_of_lt before
    simp only [outside, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at partialsOk
    exact ⟨partialsOk.1.symm, partialsOk.2.1.symm⟩
  · simpa only [gloas, ↓reduceDIte] using buildersSweepOk
  · have outside : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    simp only [outside, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at buildersSweepOk
    exact ⟨buildersSweepOk.1.symm, buildersSweepOk.2.1.symm⟩

end EthLib.Consensus
