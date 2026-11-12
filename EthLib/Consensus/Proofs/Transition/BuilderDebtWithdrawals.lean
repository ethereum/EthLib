module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtBid
public import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts

/-!
# Proofs: the withdrawals of a block keep each builder's debt covered

From Gloas, after a full parent, a block pays the withdrawals that the state expects.

The queued builder withdrawals come first.

Together they pay what each builder owes in the queued entries that are read.

The queued partial withdrawals and the sweep of validators pay validators, never a builder.

The sweep of builders pays only withdrawable builders, which have started to exit and owe nothing.

A withdrawal names a builder by its index with a flag at bit 40.

So an index must stay below 2^40 to name one builder alone, for builders and for validators.

Nothing in the state transition bounds the registries.

So the theorems on the debt assume both bounds.

The theorem that the debt stays covered also assumes an epoch before the far future epoch.

That holds when an epoch has at least two slots.

A builder that has not started to exit is then not yet withdrawable.

[EIP-7732] adds the withdrawals of builders.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-! ## Totals of withdrawals -/

/-- What queued builder withdrawals pay under one withdrawal index. -/
private def paidUnder (named : ValidatorIndex) (queue : List BuilderPendingWithdrawal) : Nat :=
  (queue.map fun pending => if convertBuilderIndexToValidatorIndex pending.builderIndex = named
    then pending.amount.toNat else 0).sum

/-- What is paid under the index of a builder is what it owes, without aliases that pay. -/
private theorem paidUnder_eq_owedBy {index : BuilderIndex} :
    ∀ {queue : List BuilderPendingWithdrawal}, (∀ pending ∈ queue,
      convertBuilderIndexToValidatorIndex pending.builderIndex =
        convertBuilderIndexToValidatorIndex index →
        pending.builderIndex = index ∨ pending.amount = 0) →
    paidUnder (convertBuilderIndexToValidatorIndex index) queue = owedBy index queue
  | [], _ => rfl
  | pending :: rest, alias => by
    have := paidUnder_eq_owedBy (queue := rest) fun other member =>
      alias other (List.mem_cons_of_mem _ member)
    simp only [paidUnder, owedBy, List.map_cons, List.sum_cons] at this ⊢
    rw [this]
    congr 1
    by_cases same : pending.builderIndex = index
    · simp [same]
    · by_cases named : convertBuilderIndexToValidatorIndex pending.builderIndex =
          convertBuilderIndexToValidatorIndex index
      · rcases alias pending List.mem_cons_self named with equal | zero
        · exact absurd equal same
        · simp [zero]
      · simp [same, named]

/-- A queued withdrawal is part of what its builder owes. -/
private theorem amount_le_owedBy : ∀ {queue : List BuilderPendingWithdrawal}
    {pending : BuilderPendingWithdrawal}, pending ∈ queue →
    pending.amount.toNat ≤ owedBy pending.builderIndex queue
  | [], _, member => absurd member List.not_mem_nil
  | first :: rest, pending, member => by
    rcases List.mem_cons.mp member with rfl | member
    · simp [owedBy]
    · have := amount_le_owedBy member
      simp only [owedBy, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- A queued withdrawal whose index aliases that of a builder is its own or pays nothing.

A builder past a registry of at most 2^40 entries has no balance, so it owes nothing. -/
private theorem BuilderDebtSettled.alias {gloas : .glamsterdam ≤ fork}
    (holds : BuilderDebtSettled state gloas)
    (buildersFit : (state.builders gloas).data.size ≤ 2 ^ 40) {index : BuilderIndex}
    (small : index.toNat < 2 ^ 40) :
    ∀ pending ∈ (state.builderPendingWithdrawals gloas).data.toList,
      convertBuilderIndexToValidatorIndex pending.builderIndex =
        convertBuilderIndexToValidatorIndex index →
        pending.builderIndex = index ∨ pending.amount = 0 := by
  intro pending member same
  by_cases inside : pending.builderIndex.toNat < 2 ^ 40
  · exact .inl ((convertBuilderIndexToValidatorIndex_inj inside small).mp same)
  · right
    have none : builderBalance state gloas pending.builderIndex = 0 := by
      simp [builderBalance, Array.getElem?_eq_none (by omega :
        (state.builders gloas).data.size ≤ pending.builderIndex.toNat)]
    have covered := holds.covered pending.builderIndex
    have := amount_le_owedBy member
    unfold pendingBuilderTotal at covered
    exact UInt64.toNat_inj.mp (by simp; omega)

/-! ## The parts of the expected withdrawals -/

/-- The loop of the queued builder withdrawals pays the first entries that it reads. -/
private theorem getBuilderWithdrawals_loop_paid {prior : Array Withdrawal} {limit : UInt64} :
    ∀ (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getBuilderWithdrawals.loop prior limit queue withdrawals next processed = .ok result →
    ∃ read ≤ queue.length, result.2.2 = processed + read ∧ ∀ named,
      withdrawnFrom result.1 named = withdrawnFrom withdrawals named +
        paidUnder named (queue.take read)
  | [], _, _, _, _, computed => by
    simp only [getBuilderWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨0, Nat.le_refl _, rfl, fun _ => by simp [paidUnder]⟩
  | pending :: rest, withdrawals, _, processed, _, computed => by
    simp only [getBuilderWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact ⟨0, Nat.zero_le _, rfl, fun _ => by simp [paidUnder]⟩
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, loopOk⟩ := computed
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      obtain ⟨read, le, count, paid⟩ := getBuilderWithdrawals_loop_paid rest _ _ _ loopOk
      refine ⟨read + 1, by simpa using le, by omega, fun named => ?_⟩
      rw [paid, withdrawnFrom_push]
      simp only [paidUnder, List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

/-- Each withdrawal of the loop of the sweep of validators names a validator of the registry. -/
private theorem getValidatorsSweepWithdrawals_loop_registry {prior : Array Withdrawal}
    {epoch : Epoch} {count limit : Nat} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ withdrawal ∈ withdrawals.toList,
      withdrawal.validatorIndex.toNat < state.validators.data.size) →
    getValidatorsSweepWithdrawals.loop state prior epoch count limit visits withdrawals next index
      processed = .ok result →
    ∀ withdrawal ∈ result.1.toList,
      withdrawal.validatorIndex.toNat < state.validators.data.size
  | 0, _, _, _, _, _, inside, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact inside
  | visits + 1, withdrawals, next, index, _, _, inside, computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact inside
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, validatorOk, _, _, computed⟩ := computed
    have member : index.toNat < state.validators.data.size :=
      (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp validatorOk)).1
    -- A withdrawal appended for this validator names the registry.
    have append : ∀ {appended : Array Withdrawal} {following : WithdrawalIndex}
        {address : ExecutionAddress} {amount : Gwei},
        appendWithdrawal withdrawals next index address amount = .ok (appended, following) →
        ∀ withdrawal ∈ appended.toList,
          withdrawal.validatorIndex.toNat < state.validators.data.size := by
      intro appended following address amount appendedOk withdrawal listed
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at listed
      rcases listed with listed | rfl
      · exact inside _ listed
      · exact member
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
      exact getValidatorsSweepWithdrawals_loop_registry visits _ _ _ _ (append appendedOk) rest
    · split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
        exact getValidatorsSweepWithdrawals_loop_registry visits _ _ _ _ (append appendedOk) rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left']
          at computed
        obtain ⟨_, _, rest⟩ := computed
        exact getValidatorsSweepWithdrawals_loop_registry visits _ _ _ _ inside rest

/-- The balance of a builder left after some withdrawals is its balance less their total for it.
-/
private theorem getBuilderBalanceAfterWithdrawals_ok {gloas : .glamsterdam ≤ fork}
    {index : BuilderIndex} {withdrawals : Array Withdrawal} {left : Gwei}
    (computed : getBuilderBalanceAfterWithdrawals state gloas index withdrawals = .ok left) :
    ∃ builder, getBuilder state gloas index = .ok builder ∧
      left.toNat = builder.balance.toNat -
        withdrawnFrom withdrawals (convertBuilderIndexToValidatorIndex index) := by
  unfold getBuilderBalanceAfterWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨withdrawn, folded, builder, found, rfl⟩ := computed
  rw [← Array.foldlM_toList] at folded
  have total := foldlM_withdrawnFrom _ _ _ folded
  refine ⟨builder, found, ?_⟩
  rw [Uint64.toNat_saturatingSub, total]
  simp [withdrawnFrom]

/-! ## The sweep of builders -/

/-- The sweep of builders pays nothing to a builder that has not started to exit.

The epoch must be before the far future one.

Each registry of builders must hold at most 2^40 entries. -/
private theorem getBuildersSweepWithdrawals_withdrawnFrom_zero {gloas : .glamsterdam ≤ fork}
    {start : WithdrawalIndex} {prior swept : Array Withdrawal} {next : WithdrawalIndex}
    {processed : Nat}
    (computed : getBuildersSweepWithdrawals state gloas start prior =
      .ok (swept, next, processed))
    (buildersFit : (state.builders gloas).data.size ≤ 2 ^ 40) {index : BuilderIndex}
    {builder : Builder} (found : getBuilder state gloas index = .ok builder)
    (far : builder.withdrawableEpoch = FAR_FUTURE_EPOCH)
    (early : getCurrentEpoch state ≠ FAR_FUTURE_EPOCH) :
    withdrawnFrom swept (convertBuilderIndexToValidatorIndex index) = 0 := by
  refine withdrawnFrom_eq_zero fun withdrawal member same => ?_
  obtain ⟨k, inside, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp member)
  obtain ⟨other, paid, _, named, paidOk, -, ready, -⟩ :=
    getBuildersSweepWithdrawals_pays computed k inside
  have equal : other = index := (convertBuilderIndexToValidatorIndex_inj
    (by have := (Array.getElem?_eq_some_iff.mp (getBuilder_eq_ok_iff.mp paidOk)).1; omega)
    (by have := (Array.getElem?_eq_some_iff.mp (getBuilder_eq_ok_iff.mp found)).1; omega)).mp
    (named.symm.trans same)
  subst equal
  rw [found, Except.ok.injEq] at paidOk
  subst paidOk
  rw [far] at ready
  exact early (Uint64.eq_of_le_max ready)

/-- The sweep of builders keeps the total of a builder within its balance.

It pays a builder at most the balance left after the withdrawals before it.

Each registry of builders must hold at most 2^40 entries. -/
private theorem getBuildersSweepWithdrawals_withdrawnFrom_le {gloas : .glamsterdam ≤ fork}
    {start : WithdrawalIndex} {prior swept : Array Withdrawal} {next : WithdrawalIndex}
    {processed : Nat}
    (computed : getBuildersSweepWithdrawals state gloas start prior =
      .ok (swept, next, processed))
    (buildersFit : (state.builders gloas).data.size ≤ 2 ^ 40) {index : BuilderIndex}
    {builder : Builder} (found : getBuilder state gloas index = .ok builder)
    (bounded : withdrawnFrom prior (convertBuilderIndexToValidatorIndex index) ≤
      builder.balance.toNat) :
    withdrawnFrom (prior ++ swept) (convertBuilderIndexToValidatorIndex index) ≤
      builder.balance.toNat := by
  have step : ∀ k, k ≤ swept.size → withdrawnFrom (prior ++ swept.extract 0 k)
      (convertBuilderIndexToValidatorIndex index) ≤ builder.balance.toNat := by
    intro k
    induction k with
    | zero => intro _; simpa using bounded
    | succ k ih =>
      intro le
      have inside : k < swept.size := by omega
      have before := ih (by omega)
      rw [Array.extract_succ_right (by omega) inside, Array.append_push, withdrawnFrom_push]
      split
      · rename_i same
        obtain ⟨other, paid, left, named, paidOk, leftOk, -, -, amount⟩ :=
          getBuildersSweepWithdrawals_pays computed k inside
        have equal : other = index := (convertBuilderIndexToValidatorIndex_inj
          (by have := (Array.getElem?_eq_some_iff.mp (getBuilder_eq_ok_iff.mp paidOk)).1; omega)
          (by have := (Array.getElem?_eq_some_iff.mp (getBuilder_eq_ok_iff.mp found)).1; omega)).mp
          (named.symm.trans same)
        subst equal
        obtain ⟨read, readOk, leftValue⟩ := getBuilderBalanceAfterWithdrawals_ok leftOk
        rw [found, Except.ok.injEq] at readOk
        subst readOk
        rw [amount, leftValue]
        omega
      · simpa using before
  simpa using step swept.size (Nat.le_refl _)

/-! ## What the expected withdrawals take from a builder -/

/-- From Gloas, what the expected withdrawals take from a builder of the registry.

Before the sweep of builders, they take what it owes in the queued withdrawals that are read.

The sweep of builders then reads those withdrawals before it.

The sweep of validators takes nothing. -/
private theorem getExpectedWithdrawals_builder (gloas : .glamsterdam ≤ fork)
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (holds : BuilderDebtSettled state gloas)
    (validatorsFit : state.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (state.builders gloas).data.size ≤ 2 ^ 40)
    (expectedOk : getExpectedWithdrawals state capella = .ok expected) {index : BuilderIndex}
    (member : index.toNat < (state.builders gloas).data.size) :
    ∃ (before swept : Array Withdrawal) (start next : WithdrawalIndex) (processed : Nat),
      getBuildersSweepWithdrawals state gloas start before = .ok (swept, next, processed) ∧
      withdrawnFrom before (convertBuilderIndexToValidatorIndex index) =
        owedBy index ((state.builderPendingWithdrawals gloas).data.toList.take
          expected.processedBuilderWithdrawalsCount) ∧
      withdrawnFrom expected.withdrawals (convertBuilderIndexToValidatorIndex index) =
        withdrawnFrom (before ++ swept) (convertBuilderIndexToValidatorIndex index) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) gloas
  obtain ⟨builders, partials, swept, sweep, _, index2, index3, _, builderCount, _, sweptCount, _,
    whole, counted, buildersOk, -, partialsOk, -, sweptOk, -, sweepOk⟩ :=
    getExpectedWithdrawals_parts expectedOk
  replace buildersOk := buildersOk gloas
  replace partialsOk := partialsOk electra
  replace sweptOk := sweptOk gloas
  refine ⟨builders ++ partials, swept, index2, index3, sweptCount, sweptOk, ?_, ?_⟩
  · -- The queued builder withdrawals pay what the builder owes in those that are read.
    unfold getBuilderWithdrawals at buildersOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersOk
    obtain ⟨read, -, count, paid⟩ := getBuilderWithdrawals_loop_paid _ _ _ _ loopOk
    simp only at count paid
    subst count
    rw [counted]
    -- The queued partial withdrawals pay validators of the registry.
    have none : withdrawnFrom partials (convertBuilderIndexToValidatorIndex index) = 0 := by
      refine withdrawnFrom_eq_zero fun withdrawal listed => ?_
      obtain ⟨k, inside, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp listed)
      obtain ⟨pending, -, validator, -, -, same, validatorOk, -⟩ :=
        getPendingPartialWithdrawals_pays partialsOk k inside
      refine ne_convertBuilderIndexToValidatorIndex_of_lt ?_ index
      rw [same]
      have := (Array.getElem?_eq_some_iff.mp (getValidator_eq_ok_iff.mp validatorOk)).1
      omega
    have empty : withdrawnFrom #[] (convertBuilderIndexToValidatorIndex index) = 0 := rfl
    rw [withdrawnFrom_append, none, paid, empty, Nat.zero_add, Nat.add_zero]
    simp only [Nat.zero_add]
    have small : index.toNat < 2 ^ 40 := by omega
    refine paidUnder_eq_owedBy fun pending listed => ?_
    exact holds.alias buildersFit small pending (List.mem_of_mem_take listed)
  · -- The sweep of validators pays validators of the registry.
    unfold getValidatorsSweepWithdrawals at sweepOk
    simp only [bind_ok_iff, ensure_ok_iff] at sweepOk
    obtain ⟨_, _, loopOk⟩ := sweepOk
    have registry := getValidatorsSweepWithdrawals_loop_registry _ _ _ _ _
      (fun _ absent => absurd absent (by simp)) loopOk
    have none : withdrawnFrom sweep (convertBuilderIndexToValidatorIndex index) = 0 :=
      withdrawnFrom_eq_zero fun withdrawal listed =>
        ne_convertBuilderIndexToValidatorIndex_of_lt
          (by have := registry withdrawal listed; omega) index
    rw [whole, withdrawnFrom_append, none, Nat.add_zero]

/-! ## What the step keeps -/

/-- What a step keeps of the builders: the size and each exit epoch. -/
private def BuildersKept (gloas : .glamsterdam ≤ fork) (state after : BeaconState preset fork) :
    Prop :=
  (after.builders gloas).data.size = (state.builders gloas).data.size ∧
    ∀ i : Nat, ((after.builders gloas).data[i]?).map (·.withdrawableEpoch) =
      ((state.builders gloas).data[i]?).map (·.withdrawableEpoch)

/-- Two steps that keep the builders keep them in turn. -/
private theorem BuildersKept.trans {gloas : .glamsterdam ≤ fork}
    {first second third : BeaconState preset fork} (one : BuildersKept gloas first second)
    (two : BuildersKept gloas second third) : BuildersKept gloas first third :=
  ⟨two.1.trans one.1, fun i => (two.2 i).trans (one.2 i)⟩

/-- A step that keeps the builders keeps what is kept of them. -/
private theorem BuildersKept.of_eq {gloas : .glamsterdam ≤ fork}
    (builders : after.builders = state.builders) : BuildersKept gloas state after :=
  ⟨by rw [builders], fun _ => by rw [builders]⟩

/-- A withdrawal keeps all of each builder but its balance. -/
private theorem applyWithdrawal_kept (gloas : .glamsterdam ≤ fork) {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : BuildersKept gloas state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨builder, builderOk, set⟩ := computed
    obtain ⟨inside, rfl⟩ := setBuilder_ok set
    refine ⟨by simp [BeaconState.putBuilder], fun i => ?_⟩
    have read := getBuilder_eq_ok_iff.mp builderOk
    by_cases same : i = (convertValidatorIndexToBuilderIndex withdrawal.validatorIndex).toNat
    · subst same
      simp [BeaconState.putBuilder, read]
    · simp [BeaconState.putBuilder, Ne.symm same]
  · simp only [decreaseBalance, bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact BuildersKept.of_eq rfl

/-- From Gloas, the expected withdrawals keep all of each builder but its balance. -/
private theorem applyExpectedWithdrawals_kept (gloas : .glamsterdam ≤ fork)
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    BuildersKept gloas state after := by
  obtain ⟨applied, appliedOk, -, builders⟩ := applyExpectedWithdrawals_balances computed
  unfold applyWithdrawals at appliedOk
  rw [← Array.foldlM_toList] at appliedOk
  exact (foldlM_ok_invariant (BuildersKept gloas state)
    (fun _ _ _ holds ok => holds.trans (applyWithdrawal_kept gloas ok)) (BuildersKept.of_eq rfl)
    appliedOk).trans (BuildersKept.of_eq builders)

/-- From Gloas, the withdrawals of a block keep each builder's debt covered.

This assumes that each registry holds at most 2^40 entries.

It also assumes that the epoch is before the far future one. -/
theorem BuilderDebtSettled.processWithdrawals {gloas : .glamsterdam ≤ fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (holds : BuilderDebtSettled state gloas)
    (validatorsFit : state.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (state.builders gloas).data.size ≤ 2 ^ 40)
    (early : getCurrentEpoch state ≠ FAR_FUTURE_EPOCH)
    (computed : processWithdrawals state capella payload = .ok after) :
    BuilderDebtSettled after gloas := by
  cases full : isParentBlockFull state gloas
  · rw [processWithdrawals_of_parentEmpty payload gloas full, Except.ok.injEq] at computed
    rw [← computed]
    exact holds
  obtain ⟨expected, expectedOk, appliedOk, -⟩ := processWithdrawals_recorded gloas full computed
  obtain ⟨size, epochs⟩ := applyExpectedWithdrawals_kept gloas appliedOk
  have payments := processWithdrawals_payments gloas computed
  have queue := (applyExpectedWithdrawals_builderQueues gloas appliedOk).2
  have slot := (payloadInputs_processWithdrawals computed).slot
  -- The step drops from what each builder owes the queued withdrawals that it pays.
  have total : ∀ index, pendingBuilderTotal after gloas index +
      owedBy index ((state.builderPendingWithdrawals gloas).data.toList.take
        expected.processedBuilderWithdrawalsCount) = pendingBuilderTotal state gloas index := by
    intro index
    have parts := owedBy_append (index := index)
      ((state.builderPendingWithdrawals gloas).data.toList.take
        expected.processedBuilderWithdrawalsCount)
      ((state.builderPendingWithdrawals gloas).data.toList.drop
        expected.processedBuilderWithdrawalsCount)
    rw [List.take_append_drop] at parts
    unfold pendingBuilderTotal
    rw [payments, queue]
    omega
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun position later => ?_⟩
  · have before := total index
    cases read : (state.builders gloas).data[index.toNat]? with
    | none =>
      -- A builder past the registry owes nothing.
      have covered := holds.covered index
      simp only [builderBalance, read] at covered
      omega
    | some builder =>
      have member : index.toNat < (state.builders gloas).data.size :=
        (Array.getElem?_eq_some_iff.mp read).1
      have lowered := processWithdrawals_builder gloas full computed expectedOk
        (index := index) (by omega)
      rw [read] at lowered
      have balance : builderBalance after gloas index = builder.balance.toNat -
          withdrawnFrom expected.withdrawals (convertBuilderIndexToValidatorIndex index) := by
        unfold builderBalance
        cases readAfter : (after.builders gloas).data[index.toNat]? with
        | none => rw [readAfter] at lowered; cases lowered
        | some kept =>
          rw [readAfter, Option.map_some, Option.map_some, Option.some.injEq] at lowered
          exact lowered
      rw [balance]
      by_cases far : builder.withdrawableEpoch = FAR_FUTURE_EPOCH
      · -- A builder that has not started to exit withdraws only what it owes.
        have found : getBuilder state gloas index = .ok builder := by simp [getBuilder, read]
        obtain ⟨prior, swept, _, _, _, sweptOk, owed, whole⟩ :=
          getExpectedWithdrawals_builder gloas holds validatorsFit buildersFit expectedOk member
        have none := getBuildersSweepWithdrawals_withdrawnFrom_zero sweptOk buildersFit found far
          early
        rw [whole, withdrawnFrom_append, none, owed]
        have covered := holds.covered index
        simp only [builderBalance, read] at covered
        omega
      · -- A builder that has started to exit owes nothing.
        have := holds.exitedClear index builder read far
        omega
  · -- The exit epoch of each builder is kept.
    have epoch := epochs index.toNat
    rw [found] at epoch
    cases read : (state.builders gloas).data[index.toNat]? with
    | none => rw [read] at epoch; cases epoch
    | some old =>
      rw [read, Option.map_some, Option.map_some, Option.some.injEq] at epoch
      have := holds.exitedClear index old read (epoch ▸ exited)
      have := total index
      omega
  · rw [slot] at later
    simpa only [paymentAt, payments] using holds.laterEmpty position later

/-- From Gloas, the withdrawals of a block keep the number of builders. -/
theorem processWithdrawals_builders_size {gloas : .glamsterdam ≤ fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    (after.builders gloas).data.size = (state.builders gloas).data.size := by
  cases full : isParentBlockFull state gloas
  · rw [processWithdrawals_of_parentEmpty payload gloas full, Except.ok.injEq] at computed
    rw [computed]
  · obtain ⟨_, -, appliedOk, -⟩ := processWithdrawals_recorded gloas full computed
    exact (applyExpectedWithdrawals_kept gloas appliedOk).1

/-- From Gloas, the expected withdrawals take from each builder of the registry at most its balance.

So no prefix of them takes more than that balance.

The debt of each builder must be covered.

This assumes that each registry holds at most 2^40 entries. -/
theorem BuilderDebtSettled.withdrawnFrom_le {gloas : .glamsterdam ≤ fork}
    {capella : .shapella ≤ fork} {expected : ExpectedWithdrawals}
    (holds : BuilderDebtSettled state gloas)
    (validatorsFit : state.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (state.builders gloas).data.size ≤ 2 ^ 40)
    (expectedOk : getExpectedWithdrawals state capella = .ok expected) {index : BuilderIndex}
    (member : index.toNat < (state.builders gloas).data.size) :
    withdrawnFrom expected.withdrawals (convertBuilderIndexToValidatorIndex index) ≤
      builderBalance state gloas index := by
  obtain ⟨builder, read⟩ : ∃ builder, (state.builders gloas).data[index.toNat]? = some builder :=
    ⟨_, Array.getElem?_eq_getElem member⟩
  have found : getBuilder state gloas index = .ok builder := by simp [getBuilder, read]
  have balance : builderBalance state gloas index = builder.balance.toNat := by
    simp [builderBalance, read]
  obtain ⟨before, swept, _, _, _, sweptOk, prior, total⟩ :=
    getExpectedWithdrawals_builder gloas holds validatorsFit buildersFit expectedOk member
  rw [total, balance]
  refine getBuildersSweepWithdrawals_withdrawnFrom_le sweptOk buildersFit found ?_
  -- Before the sweep, the builder withdraws part of what it owes.
  have covered := holds.covered index
  unfold pendingBuilderTotal at covered
  have parts := owedBy_append (index := index)
    ((state.builderPendingWithdrawals gloas).data.toList.take
      expected.processedBuilderWithdrawalsCount)
    ((state.builderPendingWithdrawals gloas).data.toList.drop
      expected.processedBuilderWithdrawalsCount)
  rw [List.take_append_drop] at parts
  omega

/-- From Gloas, after a full parent, the withdrawals lower a builder's balance by what they take.

This holds for each builder of the registry, when the debt of each builder is covered.

So no builder withdrawal is cut short at zero.

This assumes that each registry holds at most 2^40 entries. -/
theorem BuilderDebtSettled.processWithdrawals_builderBalance {gloas : .glamsterdam ≤ fork}
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    {expected : ExpectedWithdrawals} (holds : BuilderDebtSettled state gloas)
    (validatorsFit : state.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (state.builders gloas).data.size ≤ 2 ^ 40)
    (full : isParentBlockFull state gloas = true)
    (expectedOk : getExpectedWithdrawals state capella = .ok expected)
    (computed : Consensus.processWithdrawals state capella payload = .ok after)
    {index : BuilderIndex} (member : index.toNat < (state.builders gloas).data.size) :
    builderBalance after gloas index +
        withdrawnFrom expected.withdrawals (convertBuilderIndexToValidatorIndex index) =
      builderBalance state gloas index := by
  have bounded := holds.withdrawnFrom_le validatorsFit buildersFit expectedOk member
  have lowered := processWithdrawals_builder gloas full computed expectedOk
    (index := index) (by omega)
  rw [Array.getElem?_eq_getElem member, Option.map_some] at lowered
  have balance : builderBalance state gloas index =
      ((state.builders gloas).data[index.toNat]'member).balance.toNat := by
    simp [builderBalance, Array.getElem?_eq_getElem member]
  rw [balance] at bounded ⊢
  unfold builderBalance
  cases readAfter : (after.builders gloas).data[index.toNat]? with
  | none => rw [readAfter] at lowered; cases lowered
  | some kept =>
    rw [readAfter, Option.map_some, Option.some.injEq] at lowered
    dsimp only
    omega

end EthLib.Consensus
