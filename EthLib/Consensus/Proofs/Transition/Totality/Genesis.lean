module

public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.Totality.Bound

/-!
# Proofs: a genesis state is within its budget

A candidate genesis state is within any budget that covers the sum of the amounts of its deposits.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

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
      balanceSum after ≤ balanceSum state + entry.1.data.amount.toNat ∧
      ((∀ v ∈ state.validators.data,
          v.activationEligibilityEpoch = FAR_FUTURE_EPOCH ∧ v.slashed = false ∧
            v.activationEpoch = FAR_FUTURE_EPOCH) →
        ∀ v ∈ after.validators.data,
          v.activationEligibilityEpoch = FAR_FUTURE_EPOCH ∧ v.slashed = false ∧
            v.activationEpoch = FAR_FUTURE_EPOCH) := by
  refine ⟨(frame_genesisDeposit computed).balancesMatch holds, ?_⟩
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨_, _, deposited⟩ := computed
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok deposited
  simp only [applyDeposit, not_pectra_of_lt_altair before, ↓reduceDIte] at applied
  have copy : ∀ (middle : BeaconState preset fork) (deposit : PendingDeposit),
      middle.balances = state.balances → middle.slashings = state.slashings →
      applyPendingDeposit config checks middle deposit = .ok after →
      after.slashings = state.slashings ∧
        balanceSum after ≤ balanceSum state + deposit.amount.toNat ∧
        ((∀ v ∈ middle.validators.data,
            v.activationEligibilityEpoch = FAR_FUTURE_EPOCH ∧ v.slashed = false ∧
              v.activationEpoch = FAR_FUTURE_EPOCH) →
          ∀ v ∈ after.validators.data,
            v.activationEligibilityEpoch = FAR_FUTURE_EPOCH ∧ v.slashed = false ∧
              v.activationEpoch = FAR_FUTURE_EPOCH) := by
    intro middle deposit balances slashings applied
    have same : balanceSum middle = balanceSum state := by unfold balanceSum; rw [balances]
    have := balanceSum_applyPendingDeposit_le applied
    refine ⟨(applyPendingDeposit_slashings applied).trans slashings, by omega, ?_⟩
    intro pending
    rcases applyPendingDeposit_cases applied with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact pending
    · simpa only [increaseBalance_validators raised] using pending
    · intro v member
      rw [addValidatorToRegistry_validators_eq_push added, Array.mem_push] at member
      rcases member with old | rfl
      · exact pending v old
      · exact ⟨rfl, rfl, rfl⟩
  exact copy _ _ (by rfl) (by rfl) applied

/-- Activation at genesis replaces one validator, keeping the other fields.

Its effective balance is the balance rounded down to an increment, capped at the largest one. -/
private theorem activateAtGenesis_eq {state after : BeaconState preset fork} {index : Nat}
    (computed : activateAtGenesis state index = .ok after) :
    ∃ inside validator balance, after = state.putValidator index inside validator ∧
      state.balances.data[index]? = some balance ∧
      validator.effectiveBalance =
        min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
          preset.MAX_EFFECTIVE_BALANCE ∧
      (validator.activationEpoch = FAR_FUTURE_EPOCH →
        ∃ original, state.validators.data[index]? = some original ∧
          original.activationEpoch = FAR_FUTURE_EPOCH ∧
          validator.activationEligibilityEpoch = original.activationEligibilityEpoch ∧
          validator.slashed = original.slashed) ∧
      (∀ original, state.validators.data[index]? = some original →
        original.activationEpoch = FAR_FUTURE_EPOCH ∨ original.activationEpoch = GENESIS_EPOCH →
        validator.activationEpoch = FAR_FUTURE_EPOCH ∨
          validator.activationEpoch = GENESIS_EPOCH) ∧
      (∀ original, state.validators.data[index]? = some original →
        validator.slashed = original.slashed) := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, balance, read, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  refine ⟨inside, _, balance, rfl, getBalanceAt_eq_ok_iff.mp read, ?_, ?_, ?_, ?_⟩
  · split <;> rfl
  · split
    · intro unassigned
      exact False.elim ((by decide : GENESIS_EPOCH ≠ FAR_FUTURE_EPOCH) unassigned)
    · intro unassigned
      exact ⟨validator, getValidatorAt_eq_ok_iff.mp found, unassigned, rfl, rfl⟩
  · intro original located classified
    have equal := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans located)
    subst original
    split
    · exact Or.inr rfl
    · exact classified
  · intro original located
    obtain rfl := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans located)
    split <;> rfl

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
  exact ⟨Std.min_le_right, UInt64.le_trans Std.min_le_left (UInt64.sub_le kept)⟩

/-- Before Gloas, the activation at genesis keeps the balances, the slashed balances and the size.

Each effective balance is then its balance rounded down to an increment, capped at the largest. -/
private theorem foldlM_activateAtGenesis_decomposition {state after : BeaconState preset fork}
    (_before : fork < .glamsterdam)
    (computed : (List.range state.validators.data.size).foldlM activateAtGenesis state =
      .ok after) :
    after.balances = state.balances ∧ after.slashings = state.slashings ∧
      after.validators.data.size = state.validators.data.size ∧
      (∀ i < state.validators.data.size, (after.validators.data[i]?).map (·.effectiveBalance) =
        (state.balances.data[i]?).map fun balance =>
          min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
            preset.MAX_EFFECTIVE_BALANCE) ∧
      (∀ (i : Nat) (v : Validator), after.validators.data[i]? = some v →
        v.activationEpoch = FAR_FUTURE_EPOCH →
        ∃ original, state.validators.data[i]? = some original ∧
          original.activationEpoch = FAR_FUTURE_EPOCH ∧
          v.activationEligibilityEpoch = original.activationEligibilityEpoch ∧
          v.slashed = original.slashed) ∧
      ((∀ v ∈ state.validators.data,
          v.activationEpoch = FAR_FUTURE_EPOCH ∨ v.activationEpoch = GENESIS_EPOCH) →
        ∀ v ∈ after.validators.data,
          v.activationEpoch = FAR_FUTURE_EPOCH ∨ v.activationEpoch = GENESIS_EPOCH) ∧
      (∀ (i : Nat) (v : Validator), after.validators.data[i]? = some v →
        ∃ original, state.validators.data[i]? = some original ∧
          v.slashed = original.slashed) := by
  have step : ∀ (current next : BeaconState preset fork) (j : Nat),
      (inside : j < current.validators.data.size) → activateAtGenesis current j = .ok next →
      next.balances = current.balances ∧ next.slashings = current.slashings ∧
        ∃ validator, next.validators.data = current.validators.data.set j validator inside ∧
          ∃ balance, current.balances.data[j]? = some balance ∧ validator.effectiveBalance =
            min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
              preset.MAX_EFFECTIVE_BALANCE ∧
            (validator.activationEpoch = FAR_FUTURE_EPOCH →
              ∃ original, current.validators.data[j]? = some original ∧
                original.activationEpoch = FAR_FUTURE_EPOCH ∧
                validator.activationEligibilityEpoch = original.activationEligibilityEpoch ∧
                validator.slashed = original.slashed) ∧
            (∀ original, current.validators.data[j]? = some original →
              original.activationEpoch = FAR_FUTURE_EPOCH ∨
                original.activationEpoch = GENESIS_EPOCH →
              validator.activationEpoch = FAR_FUTURE_EPOCH ∨
                validator.activationEpoch = GENESIS_EPOCH) ∧
            (∀ original, current.validators.data[j]? = some original →
              validator.slashed = original.slashed) := by
    intro current next j inside activated
    obtain ⟨_, validator, balance, rfl, read, effective, metadata, classified, flags⟩ :=
      activateAtGenesis_eq activated
    exact ⟨rfl, rfl, validator, by simp [BeaconState.putValidator], balance, read, effective,
      metadata, classified, flags⟩
  let P := fun current : BeaconState preset fork => current.balances = state.balances ∧
    current.slashings = state.slashings ∧
    current.validators.data.size = state.validators.data.size ∧
      (∀ (i : Nat) (v : Validator), current.validators.data[i]? = some v →
        v.activationEpoch = FAR_FUTURE_EPOCH →
        ∃ original, state.validators.data[i]? = some original ∧
          original.activationEpoch = FAR_FUTURE_EPOCH ∧
          v.activationEligibilityEpoch = original.activationEligibilityEpoch ∧
          v.slashed = original.slashed) ∧
      ((∀ v ∈ state.validators.data,
          v.activationEpoch = FAR_FUTURE_EPOCH ∨ v.activationEpoch = GENESIS_EPOCH) →
        ∀ v ∈ current.validators.data,
          v.activationEpoch = FAR_FUTURE_EPOCH ∨ v.activationEpoch = GENESIS_EPOCH) ∧
      (∀ (i : Nat) (v : Validator), current.validators.data[i]? = some v →
        ∃ original, state.validators.data[i]? = some original ∧
          v.slashed = original.slashed)
  have keeps : ∀ j ∈ List.range state.validators.data.size, ∀ current next, P current →
      activateAtGenesis current j = .ok next → P next := by
    intro j member current next ⟨balances, slashings, size, metadata, classified, flags⟩ activated
    obtain ⟨balances', slashings', validator, data, _, _, _, transferred, classify, flag⟩ :=
      step current next j (by rw [size]; exact List.mem_range.mp member) activated
    refine ⟨balances'.trans balances, slashings'.trans slashings,
      by rw [data, Array.size_set, size], ?_, ?_, ?_⟩
    · intro i v found unassigned
      rw [data, Array.getElem?_set] at found
      split at found
      · subst i
        cases found
        obtain ⟨old, read, pending, eligibility⟩ := transferred unassigned
        obtain ⟨original, originalRead, originalPending, originalEligibility⟩ :=
          metadata j old read pending
        exact ⟨original, originalRead, originalPending,
          eligibility.1.trans originalEligibility.1, eligibility.2.trans originalEligibility.2⟩
      · exact metadata i v found unassigned
    · intro initial v belongs
      rw [data] at belongs
      rcases Array.mem_or_eq_of_mem_set belongs with old | rfl
      · exact classified initial v old
      · have inside : j < current.validators.data.size := by
          rw [size]; exact List.mem_range.mp member
        exact classify _ (Array.getElem?_eq_getElem inside)
          (classified initial _ (Array.getElem_mem inside))
    · intro i v found
      rw [data, Array.getElem?_set] at found
      split at found
      · subst i
        cases found
        have inside : j < current.validators.data.size := by
          rw [size]; exact List.mem_range.mp member
        have read := Array.getElem?_eq_getElem inside
        obtain ⟨original, originalRead, same⟩ := flags j _ read
        exact ⟨original, originalRead, (flag _ read).trans same⟩
      · exact flags i v found
  have start : P state := ⟨rfl, rfl, rfl,
    (fun _ v found pending => ⟨v, found, pending, rfl, rfl⟩), id,
    (fun _ v found => ⟨v, found, rfl⟩)⟩
  let view := fun (i : Nat) (current : BeaconState preset fork) =>
    (current.validators.data[i]?).map (·.effectiveBalance)
  let H := fun (i : Nat) (_ : Nat) (_ : Option Gwei) => (state.balances.data[i]?).map
    fun balance =>
      min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) preset.MAX_EFFECTIVE_BALANCE
  have run := fun i => foldlM_ok_pointwise P (view i) id i (H i)
    (by simpa using List.nodup_range) keeps
    (fun j member current next ⟨_, _, size, _⟩ activated other => by
      obtain ⟨-, -, _, data, -⟩ :=
        step current next j (by rw [size]; exact List.mem_range.mp member) activated
      simp [view, data, show j ≠ i from other])
    (fun j member current next ⟨balances, _, size, _⟩ activated same => by
      obtain ⟨-, -, validator, data, balance, read, effective, _⟩ :=
        step current next j (by rw [size]; exact List.mem_range.mp member) activated
      rw [id] at same
      subst same
      rw [balances] at read
      simp [view, H, data, read, effective])
    start computed
  obtain ⟨⟨balances, slashings, size, metadata, classified, flags⟩, -, -⟩ := run 0
  exact ⟨balances, slashings, size,
    (fun i inside => (run i).2.2 i (List.mem_range.mpr inside) rfl), metadata, classified, flags⟩

/-- Before Gloas, genesis activation keeps balances, slashings and registry size.

Each effective balance is its balance rounded down to an increment and capped. -/
private theorem foldlM_activateAtGenesis {state after : BeaconState preset fork}
    (_before : fork < .glamsterdam)
    (computed : (List.range state.validators.data.size).foldlM activateAtGenesis state =
      .ok after) :
    after.balances = state.balances ∧ after.slashings = state.slashings ∧
      after.validators.data.size = state.validators.data.size ∧
      ∀ i < state.validators.data.size, (after.validators.data[i]?).map (·.effectiveBalance) =
        (state.balances.data[i]?).map fun balance =>
          min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
            preset.MAX_EFFECTIVE_BALANCE := by
  obtain ⟨balances, slashings, size, effective, _⟩ :=
    foldlM_activateAtGenesis_decomposition _before computed
  exact ⟨balances, slashings, size, effective⟩

/-- A validator left unassigned by genesis activation keeps its input eligibility epoch. -/
private theorem foldlM_activateAtGenesis_unassigned {state after : BeaconState preset fork}
    (before : fork < .glamsterdam)
    (computed : (List.range state.validators.data.size).foldlM activateAtGenesis state =
      .ok after) (i : Nat) (v : Validator) (found : after.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) :
    ∃ original, state.validators.data[i]? = some original ∧
      original.activationEpoch = FAR_FUTURE_EPOCH ∧
      v.activationEligibilityEpoch = original.activationEligibilityEpoch ∧
      v.slashed = original.slashed :=
  (foldlM_activateAtGenesis_decomposition before computed).2.2.2.2.1 i v found unassigned

private theorem genesisDeposits_summary (before : fork < .altair)
    (genesisTime : UInt64) (eth1BlockHash : Hash32) (deposits : Array Deposit)
    (bodyRoot : Root) (leaves : Array DepositData) {deposited : BeaconState preset fork}
    (computed : deposits.toList.zipIdx.foldlM
      (genesisDeposit config checks (Nat.lt_trans before (by decide)) leaves)
      (emptyGenesisState config before genesisTime eth1BlockHash deposits.size.toUInt64 bodyRoot) =
        .ok deposited) :
    BalancesMatch deposited ∧
      deposited.slashings = (emptyGenesisState (preset := preset) config before genesisTime
        eth1BlockHash deposits.size.toUInt64 bodyRoot).slashings ∧
      balanceSum deposited ≤
        (deposits.toList.zipIdx.map fun entry : Deposit × Nat => entry.1.data.amount.toNat).sum ∧
      ∀ v ∈ deposited.validators.data,
        v.activationEligibilityEpoch = FAR_FUTURE_EPOCH ∧ v.slashed = false ∧
          v.activationEpoch = FAR_FUTURE_EPOCH := by
  simpa only [Nat.zero_add] using foldlM_ok_weighted
    (fun current bound => BalancesMatch current ∧
      current.slashings = (emptyGenesisState (preset := preset) config before genesisTime
        eth1BlockHash deposits.size.toUInt64 bodyRoot).slashings ∧ balanceSum current ≤ bound ∧
      ∀ v ∈ current.validators.data,
        v.activationEligibilityEpoch = FAR_FUTURE_EPOCH ∧ v.slashed = false ∧
          v.activationEpoch = FAR_FUTURE_EPOCH)
    (fun entry : Deposit × Nat => entry.1.data.amount.toNat)
    (fun current entry next bound ⟨holds, slashings, summed, eligibility⟩ step => by
      obtain ⟨holds', slashings', summed', eligibility'⟩ :=
        balanceSum_genesisDeposit_le before holds step
      exact ⟨holds', slashings'.trans slashings, by omega, eligibility' eligibility⟩)
    (c := 0)
    ⟨(emptyGenesisState_invariant before genesisTime eth1BlockHash _ bodyRoot).balancesMatch, rfl,
      by simp [balanceSum, emptyGenesisState], by simp [emptyGenesisState]⟩ computed

/-- An unassigned validator at genesis is funded and not yet eligible for activation. -/
theorem initializeBeaconStateFromEth1_unassigned_eligibility {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {after : BeaconState preset fork}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok after) (i : Nat) (v : Validator) (found : after.validators.data[i]? = some v)
    (unassigned : v.activationEpoch = FAR_FUTURE_EPOCH) :
    (∃ balance, after.balances.data[i]? = some balance ∧ v.effectiveBalance ≤ balance) ∧
      v.activationEligibilityEpoch = FAR_FUTURE_EPOCH ∧ v.slashed = false := by
  obtain ⟨time, root, deposited, activated, _, depositedOk, activatedOk, stateEq⟩ :=
    initializeBeaconStateFromEth1_ok computed
  rw [stateEq] at found ⊢
  obtain ⟨balances, _, size, effective⟩ :=
    foldlM_activateAtGenesis (Nat.lt_trans before (by decide)) activatedOk
  have inside : i < deposited.validators.data.size := by
    have bound := (Array.getElem?_eq_some_iff.mp found).1
    change i < activated.validators.data.size at bound
    omega
  have value := effective i inside
  change activated.validators.data[i]? = some v at found
  rw [found] at value
  have funded : ∃ balance, activated.balances.data[i]? = some balance ∧
      v.effectiveBalance ≤ balance := by
    cases read : deposited.balances.data[i]? with
    | none => simp [read] at value
    | some balance =>
      refine ⟨balance, ?_, ?_⟩
      · rw [balances, read]
      · simp only [read, Option.map_some, Option.some.injEq] at value
        rw [value]
        exact (min_sub_mod_le balance preset.EFFECTIVE_BALANCE_INCREMENT
          preset.MAX_EFFECTIVE_BALANCE).2
  refine ⟨funded, ?_⟩
  obtain ⟨original, read, _, same⟩ := foldlM_activateAtGenesis_unassigned
    (Nat.lt_trans before (by decide)) activatedOk i v found unassigned
  obtain ⟨eligibility, unslashed⟩ := (genesisDeposits_summary before time eth1BlockHash
    deposits root _ depositedOk).2.2.2 original (Array.mem_of_getElem? read)
  exact ⟨same.1.trans eligibility, same.2.trans unslashed.1⟩

/-- Genesis assigns only the genesis activation epoch; all other keys remain unassigned. -/
theorem initializeBeaconStateFromEth1_activation_epochs {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {after : BeaconState preset fork}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok after) :
    ∀ v ∈ after.validators.data,
      v.activationEpoch = FAR_FUTURE_EPOCH ∨ v.activationEpoch = GENESIS_EPOCH := by
  obtain ⟨time, root, deposited, activated, _, depositedOk, activatedOk, equal⟩ :=
    initializeBeaconStateFromEth1_ok computed
  rw [equal]
  exact (foldlM_activateAtGenesis_decomposition (Nat.lt_trans before (by decide))
    activatedOk).2.2.2.2.2.1 (fun v member => Or.inl
      ((genesisDeposits_summary before time eth1BlockHash deposits root _ depositedOk).2.2.2
        v member).2.2)

/-- Every validator starts unslashed after successful genesis initialization. -/
theorem initializeBeaconStateFromEth1_unslashed {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {after : BeaconState preset fork}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok after) :
    ∀ v ∈ after.validators.data, v.slashed = false := by
  obtain ⟨time, root, deposited, activated, _, depositedOk, activatedOk, equal⟩ :=
    initializeBeaconStateFromEth1_ok computed
  rw [equal]
  intro v member
  obtain ⟨i, found⟩ := Array.mem_iff_getElem?.mp member
  obtain ⟨original, read, flag⟩ :=
    (foldlM_activateAtGenesis_decomposition (Nat.lt_trans before (by decide))
      activatedOk).2.2.2.2.2.2 i v found
  exact flag.trans
    ((genesisDeposits_summary before time eth1BlockHash deposits root _ depositedOk).2.2.2
      original (Array.mem_of_getElem? read)).2.1

/-- A candidate genesis state is within every budget that covers the amounts of its deposits.

The bound on the inactivity scores can be any number, as this genesis comes before Altair.

The candidate genesis fails from Altair, so the theorem says something only at Phase 0. -/
theorem initializeBeaconStateFromEth1_withinBudget {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit} {after : BeaconState preset fork}
    {budget : Nat} (scoreBound : Nat)
    (funded : (deposits.toList.map (·.data.amount.toNat)).sum ≤ budget)
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok after) :
    WithinBudget budget scoreBound after := by
  have matched := (initializeBeaconStateFromEth1_invariant computed).balancesMatch
  -- A candidate genesis starts from an empty state, applies each deposit, then activates.
  obtain ⟨genesisTime, bodyRoot, deposited, activated, root, depositedOk, activatedOk,
    rfl⟩ := initializeBeaconStateFromEth1_ok computed
  clear computed
  have notGloas : fork < .glamsterdam := Nat.lt_trans before (by decide)
  have notElectra := not_pectra_of_lt_altair before
  -- The deposits keep one balance for each validator and the slashed balances.
  --
  -- Each deposit adds at most its amount to the balances, and an invalid one adds nothing.
  obtain ⟨depositedMatch, depositedSlashings, depositedSum, _⟩ :=
    genesisDeposits_summary before genesisTime eth1BlockHash deposits bodyRoot _ depositedOk
  have amounts : (deposits.toList.zipIdx.map fun entry : Deposit × Nat =>
      entry.1.data.amount.toNat) = deposits.toList.map (·.data.amount.toNat) := by
    conv => rhs; rw [← List.zipIdx_map_fst 0 deposits.toList]
    rw [List.map_map]
    rfl
  -- The activation keeps the balances, and sets each effective balance from its balance.
  --
  -- So each effective balance is at most its balance, and at most the largest effective balance.
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
  -- This candidate genesis comes before Altair, so there are no inactivity scores.
  --
  -- It comes before Electra, so there are no pending deposits and no balances left to consume.
  refine ⟨activated.validators.bound notGloas, matched, ?_, ?_, ?_,
    fun altair => absurd (Nat.lt_of_lt_of_le before altair) (Nat.lt_irrefl _),
    fun electra => absurd electra notElectra⟩
  -- The largest effective balance is the cap before Electra.
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
  -- The slashed balances all start at zero.
  · change slashedBalanceSum activated ≤ budget
    unfold slashedBalanceSum
    rw [slashings, depositedSlashings]
    simp [emptyGenesisState]

end EthLib.Consensus
