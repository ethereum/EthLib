module

public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.Totality.Bound

/-!
# Proofs: a genesis state is within its budget

A candidate genesis state starts from an empty state, applies each deposit, then activates.

Each deposit adds at most its amount to the balances, and an invalid one adds nothing.

The activation sets each effective balance from its balance, so it is at most that balance.

It is also at most the largest effective balance, which is the cap before Electra.

So the genesis state is within any budget that covers the sum of the amounts of the deposits.

This candidate genesis comes before Altair.

So there are no inactivity scores and no pending deposits.

There are no balances left to consume either, as those start at Electra.

The slashed balances all start at zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- A fold that adds a weight for each input to a bound keeps a property of the state and bound.

The end then has the property with the start bound plus the sum of the weights. -/
private theorem foldlM_ok_weighted {α β ε : Type} {g : β → α → Except ε β} (P : β → Nat → Prop)
    (weight : α → Nat) (step : ∀ b x b' c, P b c → g b x = .ok b' → P b' (c + weight x)) :
    ∀ {xs : List α} {b b' : β} {c : Nat}, P b c → xs.foldlM g b = .ok b' →
      P b' (c + (xs.map weight).sum)
  | [], _, _, _, holds, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simpa using holds
  | x :: _, b, _, c, holds, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    have := foldlM_ok_weighted P weight step (step b x middle c holds first) rest
    simpa [Nat.add_assoc] using this

/-- A deposit credited at once keeps the slashed balances. -/
private theorem applyPendingDeposit_slashings {state after : BeaconState preset fork}
    {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    after.slashings = state.slashings := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      rfl
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · unfold addValidatorToRegistry at computed
      split at computed
      · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at computed
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
        rfl
      · split at computed
        · cases computed
          rfl
        · cases computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    obtain ⟨_, set⟩ := increaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rfl

/-- A fork before Altair is not at least Electra. -/
private theorem not_pectra_of_lt_altair {fork : Base.Fork} (before : fork < .altair) :
    ¬Fork.pectra ≤ fork := fun le =>
  Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans before (by decide)) le)

/-- A deposit at genesis keeps one balance for each validator and the slashed balances.

It raises the sum of the balances by at most its amount. -/
private theorem balanceSum_genesisDeposit_le {state after : BeaconState preset fork}
    (before : fork < .altair) {leaves : Array DepositData} {entry : Deposit × Nat}
    (holds : BalancesMatch state)
    (computed : genesisDeposit config checks (Nat.lt_trans before (by decide)) leaves state entry =
      .ok after) :
    BalancesMatch after ∧ after.slashings = state.slashings ∧
      balanceSum after ≤ balanceSum state + entry.1.data.amount.toNat := by
  refine ⟨(frame_genesisDeposit computed).balancesMatch holds, ?_⟩
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨_, _, deposited⟩ := computed
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok deposited
  simp only [applyDeposit, not_pectra_of_lt_altair before, ↓reduceDIte] at applied
  have copy : ∀ (middle : BeaconState preset fork) (deposit : PendingDeposit),
      middle.balances = state.balances → middle.slashings = state.slashings →
      applyPendingDeposit config checks middle deposit = .ok after →
      after.slashings = state.slashings ∧
        balanceSum after ≤ balanceSum state + deposit.amount.toNat := by
    intro middle deposit balances slashings applied
    have same : balanceSum middle = balanceSum state := by unfold balanceSum; rw [balances]
    have := balanceSum_applyPendingDeposit_le applied
    exact ⟨(applyPendingDeposit_slashings applied).trans slashings, by omega⟩
  exact copy _ _ (by rfl) (by rfl) applied

/-- Activation at genesis replaces one validator, keeping the other fields.

Its effective balance is the balance rounded down to an increment, capped at the largest one. -/
private theorem activateAtGenesis_eq {state after : BeaconState preset fork} {index : Nat}
    (computed : activateAtGenesis state index = .ok after) :
    ∃ inside validator balance, after = state.putValidator index.toUInt64.toNat inside validator ∧
      state.balances.data[index.toUInt64.toNat]? = some balance ∧
      validator.effectiveBalance =
        min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
          preset.MAX_EFFECTIVE_BALANCE := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, balance, read, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  exact ⟨inside, _, balance, rfl, getBalance_eq_ok_iff.mp read, by split <;> rfl⟩

/-- A sum read in step over two lists is at most a sum over the second list.

Each term must be at most the term of the second list at the same index. -/
private theorem sum_zipWith_le {α β : Type} (f : α → β → Nat) (g : β → Nat) :
    ∀ (first : List α) (second : List β),
      (∀ i (inFirst : i < first.length) (inSecond : i < second.length),
        f first[i] second[i] ≤ g second[i]) →
      (first.zipWith f second).sum ≤ (second.map g).sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: first, b :: second, bounded => by
    simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
    have head := bounded 0 (by simp) (by simp)
    have tail := sum_zipWith_le f g first second fun i inFirst inSecond =>
      bounded (i + 1) (by simpa using inFirst) (by simpa using inSecond)
    simp only [List.getElem_cons_zero] at head
    omega

/-- A value rounded down to a step and capped is at most the cap and at most the value. -/
private theorem min_sub_mod_le (value step cap : UInt64) :
    min (value - value % step) cap ≤ cap ∧ min (value - value % step) cap ≤ value := by
  have kept : value % step ≤ value := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  have lowered := UInt64.sub_le kept
  rw [UInt64.min_def]
  split
  · exact ⟨by assumption, lowered⟩
  · rename_i above
    rw [UInt64.le_iff_toNat_le] at above lowered ⊢
    exact ⟨Nat.le_refl _, by rw [UInt64.le_iff_toNat_le]; omega⟩

/-- Before Gloas, the activation at genesis keeps the balances, the slashed balances and the size.

Each effective balance is then its balance rounded down to an increment, capped at the largest. -/
private theorem foldlM_activateAtGenesis {state after : BeaconState preset fork}
    (before : fork < .glamsterdam)
    (computed : (List.range state.validators.data.size).foldlM activateAtGenesis state =
      .ok after) :
    after.balances = state.balances ∧ after.slashings = state.slashings ∧
      after.validators.data.size = state.validators.data.size ∧
      ∀ i < state.validators.data.size, (after.validators.data[i]?).map (·.effectiveBalance) =
        (state.balances.data[i]?).map fun balance =>
          min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
            preset.MAX_EFFECTIVE_BALANCE := by
  have step : ∀ (current next : BeaconState preset fork) (j : Nat),
      (inside : j < current.validators.data.size) → activateAtGenesis current j = .ok next →
      next.balances = current.balances ∧ next.slashings = current.slashings ∧
        ∃ validator, next.validators.data = current.validators.data.set j validator inside ∧
          ∃ balance, current.balances.data[j]? = some balance ∧ validator.effectiveBalance =
            min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
              preset.MAX_EFFECTIVE_BALANCE := by
    intro current next j inside activated
    obtain ⟨_, validator, balance, rfl, read, effective⟩ := activateAtGenesis_eq activated
    have same := toNat_toUInt64_of_lt (current.validators.bound before) inside
    rw [same] at read
    exact ⟨rfl, rfl, validator, by simp [BeaconState.putValidator, same], balance, read, effective⟩
  let P := fun current : BeaconState preset fork => current.balances = state.balances ∧
    current.slashings = state.slashings ∧ current.validators.data.size = state.validators.data.size
  have keeps : ∀ j ∈ List.range state.validators.data.size, ∀ current next, P current →
      activateAtGenesis current j = .ok next → P next := by
    intro j member current next ⟨balances, slashings, size⟩ activated
    obtain ⟨balances', slashings', _, data, -⟩ :=
      step current next j (by rw [size]; exact List.mem_range.mp member) activated
    exact ⟨balances'.trans balances, slashings'.trans slashings, by rw [data, Array.size_set, size]⟩
  have start : P state := ⟨rfl, rfl, rfl⟩
  let view := fun (i : Nat) (current : BeaconState preset fork) =>
    (current.validators.data[i]?).map (·.effectiveBalance)
  let H := fun (i : Nat) (_ : Nat) (_ : Option Gwei) => (state.balances.data[i]?).map
    fun balance =>
      min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) preset.MAX_EFFECTIVE_BALANCE
  have run := fun i => foldlM_ok_pointwise P (view i) id i (H i)
    (by simpa using List.nodup_range) keeps
    (fun j member current next ⟨_, _, size⟩ activated other => by
      obtain ⟨-, -, _, data, -⟩ :=
        step current next j (by rw [size]; exact List.mem_range.mp member) activated
      simp [view, data, show j ≠ i from other])
    (fun j member current next ⟨balances, _, size⟩ activated same => by
      obtain ⟨-, -, validator, data, balance, read, effective⟩ :=
        step current next j (by rw [size]; exact List.mem_range.mp member) activated
      rw [id] at same
      subst same
      rw [balances] at read
      simp [view, H, data, read, effective])
    start computed
  obtain ⟨⟨balances, slashings, size⟩, -, -⟩ := run 0
  refine ⟨balances, slashings, size, fun i inside => ?_⟩
  exact (run i).2.2 i (List.mem_range.mpr inside) rfl

/-- A candidate genesis state is within every budget that covers the amounts of its deposits.

The bound on the inactivity scores can be any number, as this genesis comes before Altair.

The candidate genesis fails from Altair, so the theorem says something only at Phase 0. -/
theorem initializeBeaconStateFromEth1_withinBudget {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {after : BeaconState preset fork}
    {budget : Nat} (scoreBound : Nat)
    (funded : (deposits.toList.map (·.data.amount.toNat)).sum ≤ budget)
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    WithinBudget budget scoreBound after := by
  have matched := (initializeBeaconStateFromEth1_invariant computed).2.balancesMatch
  obtain ⟨before, genesisTime, bodyRoot, deposited, activated, root, depositedOk, activatedOk,
    rfl⟩ := initializeBeaconStateFromEth1_ok computed
  clear computed
  have notGloas : fork < .glamsterdam := Nat.lt_trans before (by decide)
  have notElectra := not_pectra_of_lt_altair before
  -- The deposits keep one balance for each validator and the slashed balances.
  obtain ⟨depositedMatch, depositedSlashings, depositedSum⟩ := foldlM_ok_weighted
    (fun current bound => BalancesMatch current ∧
      current.slashings = (emptyGenesisState (preset := preset) config before genesisTime
        eth1BlockHash deposits.size.toUInt64 bodyRoot).slashings ∧ balanceSum current ≤ bound)
    (fun entry : Deposit × Nat => entry.1.data.amount.toNat)
    (fun current entry next bound ⟨holds, slashings, summed⟩ step => by
      obtain ⟨holds', slashings', summed'⟩ := balanceSum_genesisDeposit_le before holds step
      exact ⟨holds', slashings'.trans slashings, by omega⟩)
    (c := 0)
    ⟨(emptyGenesisState_invariant before genesisTime eth1BlockHash _ bodyRoot).balancesMatch, rfl,
      by simp [balanceSum, emptyGenesisState]⟩ depositedOk
  have amounts : (deposits.toList.zipIdx.map fun entry : Deposit × Nat =>
      entry.1.data.amount.toNat) = deposits.toList.map (·.data.amount.toNat) := by
    conv => rhs; rw [← List.zipIdx_map_fst 0 deposits.toList]
    rw [List.map_map]
    rfl
  -- The activation keeps the balances, and sets each effective balance from its balance.
  obtain ⟨balances, slashings, size, effective⟩ := foldlM_activateAtGenesis notGloas activatedOk
  have bounded : ∀ i (inside : i < activated.validators.data.size) balance,
      activated.balances.data[i]? = some balance →
      activated.validators.data[i].effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
        activated.validators.data[i].effectiveBalance ≤ balance := by
    intro i inside balance read
    rw [balances] at read
    have := effective i (by omega)
    rw [Array.getElem?_eq_getElem inside, read] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this]
    exact min_sub_mod_le _ _ _
  refine ⟨activated.validators.bound notGloas, matched, ?_, ?_, ?_,
    fun altair => absurd (Nat.lt_of_lt_of_le before altair) (Nat.lt_irrefl _),
    fun electra => absurd electra notElectra⟩
  · intro validator member
    obtain ⟨i, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    change i < activated.validators.data.size at inside
    have balanceInside : i < activated.balances.data.size := by
      unfold BalancesMatch at depositedMatch
      rw [balances]
      omega
    simp only [withdrawalMaxEffectiveBalance, notElectra, ↓reduceIte]
    exact (bounded i inside _ (Array.getElem?_eq_getElem balanceInside)).1
  · change stakeSum activated + pendingDepositSum activated ≤ budget
    have zero : pendingDepositSum activated = 0 := by
      simp only [pendingDepositSum, notElectra, ↓reduceDIte]
    have stake : stakeSum activated ≤ balanceSum activated := by
      unfold stakeSum balanceSum
      apply sum_zipWith_le
      intro i first second
      rw [Array.length_toList] at first second
      simp only [Array.getElem_toList]
      exact Nat.max_le.mpr ⟨UInt64.le_iff_toNat_le.mp
        (bounded i first _ (Array.getElem?_eq_getElem second)).2, Nat.le_refl _⟩
    have same : balanceSum activated = balanceSum deposited := by
      unfold balanceSum
      rw [balances]
    rw [amounts] at depositedSum
    omega
  · change slashedBalanceSum activated ≤ budget
    unfold slashedBalanceSum
    rw [slashings, depositedSlashings]
    simp [emptyGenesisState]

end EthLib.Consensus
