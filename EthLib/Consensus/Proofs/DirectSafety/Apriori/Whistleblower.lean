module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling

/-!
# The whistleblower allowance

From Electra, the credits other than rewards and sync credits fit an allowance of the window.

The allowance reads only the reference state and the length of the window.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-! ## Whistleblower allowance -/

/-- An event charge supported on indices occurring at most once pays each index at most once. -/
private theorem once_only_charge_le {α : Type} (events : List α) (keys : Finset Nat)
    (chosen : α → Nat → Bool) (credit : α → Nat) (charge : Nat → Nat)
    (supported : ∀ e ∈ events, credit e ≤ ∑ i ∈ keys, if chosen e i then charge i else 0)
    (once : ∀ i ∈ keys, (events.countP fun e => chosen e i) ≤ 1) :
    (events.map credit).sum ≤ ∑ i ∈ keys, charge i := by
  have exchange : (events.map fun e => ∑ i ∈ keys,
      if chosen e i then charge i else 0).sum =
      ∑ i ∈ keys, (events.countP fun e => chosen e i) * charge i := by
    clear supported once
    induction events with
    | nil => simp
    | cons e rest ih =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons, ih,
        Finset.sum_add_distrib, Nat.add_mul]
      rw [Nat.add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases chosen e i <;> simp
  calc
    (events.map credit).sum ≤ (events.map fun e =>
        ∑ i ∈ keys, if chosen e i then charge i else 0).sum :=
      List.sum_le_sum supported
    _ = ∑ i ∈ keys, (events.countP fun e => chosen e i) * charge i := exchange
    _ ≤ ∑ i ∈ keys, charge i := Finset.sum_le_sum fun i member => by
      simpa using Nat.mul_le_mul_right (charge i) (once i member)

/-- Each positive slashing credit is supported on the indices newly slashed by its event. -/
private theorem slashing_step_support {config : Config} {checks : SignatureChecks}
    {x y : ForkedBeaconState preset} (step : Step config checks x y)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (e : BalanceEvent preset) (member : e ∈ events) :
    (if e.source = .slashings then e.creditLimit else 0) ≤
      ∑ i ∈ Finset.range y.state.validators.data.size,
        if !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
            (e.after.state.validators.data[i]?.map (·.slashed)).getD false then
          effectiveAt x i /
            (EthLib.Consensus.parameters preset x.fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
        else 0 := by
  let chosen (e : BalanceEvent preset) (i : Nat) : Bool :=
    !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
      (e.after.state.validators.data[i]?.map (·.slashed)).getD false
  have sites := step.balanceEvents_sites early holds compounding replayed
  by_cases source : e.source = .slashings
  · simp only [source, ↓reduceIte]
    by_cases positive : 0 < e.creditLimit
    · obtain ⟨_, _, _, _, _, _, _, _, _, during, after, _, _, _, _, support, bridge, fork, _⟩ :=
        sites e member
      have input := bridge source positive
      apply le_trans (support source)
      apply le_trans (Finset.sum_le_sum fun i _ => ?_)
        (Finset.sum_le_sum_of_subset (Finset.range_mono (during.trans after).size_le))
      change (if chosen e i then _ else _) ≤ if chosen e i then _ else _
      split_ifs
      · rw [input i, fork source positive]
      · exact Nat.le_refl _
    · simp only [show e.creditLimit = 0 by omega]
      exact Nat.zero_le _
  · simp [source]

/-- Persistence composes the per-step single-slashing count over the replay of a run. -/
private theorem slashing_run_count_le {config : Config} {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (tail : Run config checks x y) (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (i : Nat) :
    (events.countP fun e =>
      !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
        (e.after.state.validators.data[i]?.map (·.slashed)).getD false) ≤
      if (y.state.validators.data[i]?.map (·.slashed)).getD false then 1 else 0 := by
  induction tail generalizing events with
  | nil => cases replayed; simp
  | @snoc middle last pre step ih =>
    have selected := (UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    have previous := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected priorOk
    have next := slashing_step_count_le step early
      (run_justified_separated (shared.append pre) genesis).1 compounding addedOk i
    rw [List.countP_append]
    cases flag : (middle.state.validators.data[i]?.map (·.slashed)).getD false with
    | false =>
      simp only [flag, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
        at previous next
      omega
    | true =>
      have marked : (last.state.validators.data[i]?.map (·.slashed)).getD false = true := by
        cases found : middle.state.validators.data[i]? with
        | none => simp [found] at flag
        | some v =>
          have was : v.slashed = true := by simpa [found] using flag
          obtain ⟨w, final, slashed⟩ := step.slashedPersistence i v found was
          simp [final, slashed]
      simp only [flag, marked, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte] at previous next ⊢
      omega

/-- Per-index event bounds sum once over the complete run, not once per step. -/
private theorem slashing_run_charge_le {config : Config} {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (tail : Run config checks x y) (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (keys : Finset Nat) (charge : Nat → Nat)
    (supported : ∀ e ∈ events,
      (if e.source = .slashings then e.creditLimit else 0) ≤
        ∑ i ∈ keys, if !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
            (e.after.state.validators.data[i]?.map (·.slashed)).getD false then charge i else 0) :
    (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      ∑ i ∈ keys, charge i := by
  apply once_only_charge_le events keys _ _ charge supported
  intro i _
  have counted :=
    slashing_run_count_le shared tail genesis early compounding high endEpoch replayed i
  exact counted.trans (by split <;> omega)

/-- Bounds at the inputs of the run's steps support one charge per newly slashed index. -/
private theorem slashing_run_support {config : Config} {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (tail : Run config checks x y) (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (high : Nat) (keys : Finset Nat) (charge : Nat → Nat)
    (bounded : ∀ {a b} (step : Step config checks a b), tail.Contains step →
      ∀ i ∈ Finset.range b.state.validators.data.size,
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        i ∈ keys ∧
          effectiveAt a i /
            (EthLib.Consensus.parameters preset a.fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
              charge i)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∀ e ∈ events, (if e.source = .slashings then e.creditLimit else 0) ≤
      ∑ i ∈ keys, if !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
          (e.after.state.validators.data[i]?.map (·.slashed)).getD false then charge i else 0 := by
  induction tail generalizing events with
  | nil => cases replayed; simp
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have previous := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
      (fun one member => bounded one (.earlier member step)) priorOk
    split at rest
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      intro e member
      rcases List.mem_append.mp member with old | new
      · exact previous e old
      · have support := slashing_step_support step early
          (run_justified_separated (shared.append pre) genesis).1 compounding addedOk e new
        let selected (i : Nat) : Bool :=
          !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
            (e.after.state.validators.data[i]?.map (·.slashed)).getD false
        have charged (i : Nat) (inside : i ∈ Finset.range last.state.validators.data.size)
            (chosen : selected i = true) := by
          have positive : 0 < added.countP (fun event =>
              !(event.before.state.validators.data[i]?.map (·.slashed)).getD true &&
                (event.after.state.validators.data[i]?.map (·.slashed)).getD false) :=
            List.countP_pos_iff.mpr ⟨e, new, chosen⟩
          have counted := slashing_step_count_le step early
            (run_justified_separated (shared.append pre) genesis).1 compounding addedOk i
          have active : (!(middle.state.validators.data[i]?.map (·.slashed)).getD false &&
              (last.state.validators.data[i]?.map (·.slashed)).getD false) = true := by
            split at counted
            · assumption
            · omega
          exact bounded step (.last pre step) i inside active
        change (if e.source = .slashings then e.creditLimit else 0) ≤ _ at support
        apply support.trans
        change (∑ i ∈ Finset.range last.state.validators.data.size,
          if selected i then _ else _) ≤ _
        rw [← Finset.sum_filter]
        apply le_trans (Finset.sum_le_sum fun i inside => (charged i
          (Finset.mem_filter.mp inside).1 (Finset.mem_filter.mp inside).2).2)
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset
        intro i inside
        exact Finset.mem_filter.mpr ⟨(charged i
          (Finset.mem_filter.mp inside).1 (Finset.mem_filter.mp inside).2).1,
            (Finset.mem_filter.mp inside).2⟩
    · cases rest
      exact previous

/-- Uniform per-index bounds over step inputs pay all slashing credits only once. -/
private theorem slashing_credits_le {config : Config} {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (tail : Run config checks x y) (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (keys : Finset Nat) (charge : Nat → Nat)
    (bounded : ∀ {a b} (step : Step config checks a b), tail.Contains step →
      ∀ i ∈ Finset.range b.state.validators.data.size,
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        i ∈ keys ∧
          effectiveAt a i /
            (EthLib.Consensus.parameters preset a.fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
              charge i)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      ∑ i ∈ keys, charge i :=
  slashing_run_charge_le shared tail genesis early compounding high endEpoch replayed keys charge
    (slashing_run_support shared tail genesis early compounding high keys charge bounded replayed)

/-- Within either cap regime, newly slashed indices pay the slashing credits once. -/
private theorem slashing_credits_le_newly_slashed {config : Config} {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (shared : Run config checks g x)
    (tail : Run config checks x y) (genesis : Genesis (config := config) (checks := checks) g)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (early : y.fork < .glamsterdam)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      ((Finset.range y.state.validators.data.size).filter fun i =>
        !(x.state.validators.data[i]?.map (·.slashed)).getD false &&
          (y.state.validators.data[i]?.map (·.slashed)).getD false).card *
        ((if .pectra ≤ x.fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
          else preset.MAX_EFFECTIVE_BALANCE.toNat) /
          (if .pectra ≤ x.fork then preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat
            else preset.WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) := by
  let keys := (Finset.range y.state.validators.data.size).filter fun i =>
    !(x.state.validators.data[i]?.map (·.slashed)).getD false &&
      (y.state.validators.data[i]?.map (·.slashed)).getD false
  apply le_trans (slashing_credits_le shared tail genesis early compounding high endEpoch keys
    (fun _ => (if .pectra ≤ x.fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        else preset.MAX_EFFECTIVE_BALANCE.toNat) /
      (if .pectra ≤ x.fork then preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat
        else preset.WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) ?_ replayed)
  · simp [keys]
  intro a b step contained i inside marked
  obtain ⟨pre, post, _⟩ := tail.contains_split step contained
  have aEarly := Nat.lt_of_le_of_lt
    (Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)) early
  have sameRegime : (.pectra ≤ a.fork) ↔ .pectra ≤ x.fork := by
    constructor
    · intro atSite
      rcases regime with electra | before
      · exact electra
      · exact (Nat.not_le_of_lt (Nat.lt_of_le_of_lt
          (Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps))
            before) atSite).elim
    · exact fun electra => Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have flags : (a.state.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (b.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    simpa only [Bool.and_eq_true, Bool.not_eq_true'] using marked
  have last : (y.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at flags
    | some v =>
      have was : v.slashed = true := by simpa [found] using flags.2
      obtain ⟨w, read, flag⟩ := post.slashedPersistence i v found was
      simp [read, flag]
  have first : (x.state.validators.data[i]?.map (·.slashed)).getD false = false := by
    cases found : x.state.validators.data[i]? with
    | none => simp
    | some v =>
      cases flag : v.slashed with
      | false => simp [flag]
      | true =>
        obtain ⟨w, read, kept⟩ := pre.slashedPersistence i v found flag
        simp [read, kept] at flags
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (Nat.lt_of_lt_of_le (Finset.mem_range.mp inside) post.registryLifecycle.size_le),
      by simp [first, last]⟩, ?_⟩
  have cap : effectiveAt a i ≤
      (if .pectra ≤ x.fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        else preset.MAX_EFFECTIVE_BALANCE.toNat) := by
    cases found : a.state.validators.data[i]? with
    | none => simp [effectiveAt, found]
    | some v =>
      have bounded := (shared.append pre).effectiveBalance_capped genesis activation compounding
        aEarly v (Array.mem_of_getElem? found)
      have largest : withdrawalMaxEffectiveBalance preset a.fork v ≤
          (if .pectra ≤ x.fork then preset.MAX_EFFECTIVE_BALANCE_ELECTRA
            else preset.MAX_EFFECTIVE_BALANCE) := by
        unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
        by_cases electra : .pectra ≤ x.fork
        · simp only [sameRegime.mpr electra, electra, ↓reduceIte]
          split
          · exact UInt64.le_refl _
          · exact compounding
        · simp [electra, mt sameRegime.mp electra]
      simpa [effectiveAt, found, apply_ite UInt64.toNat] using UInt64.le_iff_toNat_le.mp
        (UInt64.le_trans bounded largest)
  simpa [EthLib.Consensus.parameters, sameRegime, apply_ite UInt64.toNat] using Nat.div_le_div_right
    (c := if .pectra ≤ x.fork then preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat
      else preset.WHISTLEBLOWER_REWARD_QUOTIENT.toNat) cap

/-- A fixed window key budget pays every slashing credit at the window cap, once. -/
private theorem slashing_credits_le_allowance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (finite : getCurrentEpoch y.state < FAR_FUTURE_EPOCH)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (forks : (0 < preElectraEpochs config x high) ↔ x.fork < .pectra)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
        (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
        (driftHorizon x high) (preElectraEpochs config x high) := by
  have charged := slashing_credits_le_newly_slashed shared tail genesis regime early
    caps.activation caps.compounding high endEpoch replayed
  have classified := newly_slashed_count_le shared genesis tail caps aligned early finite
  have index : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high + 1 := by unfold driftHorizon; omega
  have count : ((Finset.range y.state.validators.data.size).filter fun i =>
      !(x.state.validators.data[i]?.map (·.slashed)).getD false &&
        (y.state.validators.data[i]?.map (·.slashed)).getD false).card ≤
      referenceCount x +
          windowActivations preset config (referenceCount x) (scheduledActivationCount x)
        (unassignedPreStake x) (fundingCarry x) (driftHorizon x high)
        (preElectraEpochs config x high) + exitedSlashableCount x := by
    by_cases electra : .pectra ≤ x.fork
    · have firstFinite := UInt64.lt_of_le_of_lt
        (currentEpoch_le_of_chainSteps tail.chainSteps) finite
      have budget := windowAssignments_le_budget shared genesis tail caps aligned electra early
        firstFinite positive
      have deposit := Nat.mul_le_mul_left
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (Nat.add_le_add_right index 1)
      have divided := Nat.div_le_div_right (c := preset.MAX_EFFECTIVE_BALANCE.toNat)
        (Nat.add_le_add_left deposit (unassignedPreStake x + fundingCarry x))
      have notBefore : ¬ 0 < preElectraEpochs config x high :=
          mt forks.mp (Nat.not_lt_of_ge electra)
      simp only [windowActivations, notBefore, ↓reduceIte]
      have total := classified.trans (Nat.add_le_add_right
        (budget.trans (Nat.add_le_add_left divided _)) _)
      simpa only [Nat.add_assoc] using total
    · have before := regime.resolve_left electra
      have budget := windowActivations_le_countPath shared genesis tail before
      have mono : Monotone
          (activeCountPath config (referenceCount x + scheduledActivationCount x)) :=
        countPath_monotone _ _
      have path := mono index
      have starts : referenceCount x ≤
          activeCountPath config (referenceCount x + scheduledActivationCount x)
              (driftHorizon x high + 1) :=
        (Nat.le_add_right _ _).trans (by simpa only [activeCountPath] using mono (Nat.zero_le
          (driftHorizon x high + 1)))
      simp only [windowActivations, forks.mpr (Nat.lt_of_not_ge electra), ↓reduceIte]
      omega
  apply charged.trans
  apply (Nat.mul_le_mul_right _ count).trans
  unfold whistleblowerAllowance whistleblowerQuotient
  by_cases electra : .pectra ≤ x.fork
  · have notBefore : ¬ 0 < preElectraEpochs config x high := mt forks.mp (Nat.not_lt_of_ge electra)
    simp only [electra, notBefore, ↓reduceIte]
    exact Nat.mul_div_le_mul_div_assoc _ _ _
  · simp only [electra, forks.mpr (Nat.lt_of_not_ge electra), ↓reduceIte]
    exact Nat.mul_div_le_mul_div_assoc _ _ _

/-- The numeric guard supplies the fixed slashing allowance at every bounded early endpoint. -/
private theorem slashing_credits_le_allowance_of_guard {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
        (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
        (driftHorizon x high) (preElectraEpochs config x high) := by
  obtain ⟨forks, regime⟩ :=
    guarded_fork_regime (shared.append tail) genesis high endEpoch guard
  obtain ⟨-, -, -, positive, -, -, -, -, -, -, -, -, -, -⟩ := guard
  have finite : getCurrentEpoch y.state < FAR_FUTURE_EPOCH := by
    rw [UInt64.lt_iff_toNat_lt, getCurrentEpoch_toNat]
    have bounded := y.state.slot.toNat_lt
    have divided := Nat.div_mul_le_self y.state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have twice := (Nat.mul_le_mul_left
      (y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) twoSlots).trans divided
    change y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat < 18446744073709551615
    omega
  exact slashing_credits_le_allowance shared genesis tail caps aligned early regime finite
    positive high endEpoch forks replayed

/-- From Electra, the guarded whistleblower allowance pays every other funding credit. -/
theorem otherCredit_le_allowance_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map otherCredit).sum ≤
      whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
        (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
        (driftHorizon x high) (preElectraEpochs config x high) := by
  have allowance := slashing_credits_le_allowance_of_guard shared genesis tail caps aligned
    early twoSlots high endEpoch guard replayed
  obtain ⟨-, -, -, -, -, -, -, -, -, delay, -, -, -, -⟩ := guard
  rw [otherCredit_sum_electra shared tail genesis electra early (by omega) replayed]
  exact allowance

/-- The count path grows by at most the final count churn at each epoch. -/
private theorem countPath_growth_le (config : Config) (start horizon : Nat) :
    activeCountPath config start horizon ≤
      start + horizon * cohortCap config (activeCountPath config start horizon) := by
  have mono : Monotone (activeCountPath config start) :=
    countPath_monotone _ _
  induction horizon with
  | zero => simp [activeCountPath]
  | succ horizon ih =>
    have churn : cohortCap config (activeCountPath config start horizon) ≤
        cohortCap config (activeCountPath config start (horizon + 1)) :=
      max_le_max_left _ (Nat.div_le_div_right (mono (Nat.le_succ horizon)))
    calc
      activeCountPath config start (horizon + 1) =
          activeCountPath config start horizon +
            cohortCap config (activeCountPath config start horizon) := rfl
      _ ≤ start + horizon * cohortCap config (activeCountPath config start (horizon + 1)) +
          cohortCap config (activeCountPath config start (horizon + 1)) :=
        Nat.add_le_add (ih.trans (Nat.add_le_add_left (Nat.mul_le_mul_left horizon churn) _))
          churn
      _ = _ := by rw [Nat.succ_mul]; omega

/-- The pre-fork count path pays its growth using the churn at the window endpoint. -/
private theorem countPath_growth_window (config : Config) (start elapsed horizon : Nat)
    (within : elapsed ≤ horizon) :
    activeCountPath config start elapsed - start ≤
      horizon * cohortCap config (activeCountPath config start horizon) := by
  have mono : Monotone (activeCountPath config start) :=
    countPath_monotone _ _
  have bound := (mono within).trans (countPath_growth_le config start horizon)
  omega

/-- The scheduled cohort is already funded by the initial pre-active reserve. -/
private theorem scheduled_reserve_le_pre {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (early : x.fork < .pectra) :
    preset.MAX_EFFECTIVE_BALANCE.toNat * scheduledActivationCount x ≤ preActiveStake x := by
  let p := fun v : Validator =>
    decide (getCurrentEpoch x.state < v.activationEpoch) && v.activationEpoch != FAR_FUTURE_EPOCH
  have counted (l : List Validator) : preset.MAX_EFFECTIVE_BALANCE.toNat * l.countP p =
      (l.map fun v => if p v then preset.MAX_EFFECTIVE_BALANCE.toNat else 0).sum := by
    induction l with
    | nil => simp
    | cons v rest ih => cases chosen : p v <;>
        simp [chosen, Nat.mul_add, ih, Nat.add_comm]
  have mapped : (x.state.validators.data.toList.zipIdx.map fun (v, _i) =>
      if p v then preset.MAX_EFFECTIVE_BALANCE.toNat else 0) =
      x.state.validators.data.toList.map
        (fun v => if p v then preset.MAX_EFFECTIVE_BALANCE.toNat else 0) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map fun v => if p v then preset.MAX_EFFECTIVE_BALANCE.toNat else 0)
        (List.zipIdx_map_fst 0 x.state.validators.data.toList)
  change preset.MAX_EFFECTIVE_BALANCE.toNat * x.state.validators.data.toList.countP p ≤ _
  rw [counted, ← mapped]
  unfold preActiveStake
  apply List.sum_le_sum
  intro entry member
  obtain ⟨v, i⟩ := entry
  have found := List.mem_zipIdx_iff_getElem?.mp member
  rw [Array.getElem?_toList] at found
  by_cases selected : p v = true
  · have chosen := selected
    simp only [p, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at chosen
    have ordered := shared.activationExitOrder genesis v (Array.mem_of_getElem? found)
    have live := UInt64.lt_of_lt_of_le chosen.1 ordered
    have inactive : isActiveValidator v (getCurrentEpoch x.state) = false := by
      simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl (UInt64.not_le.mpr chosen.1)
    have reserve := UInt64.le_iff_toNat_le.mp
      (shared.scheduled_activation_reserve genesis caps.activation caps.compounding aligned
        early i v found chosen.1 chosen.2)
    simpa only [selected, ↓reduceIte, inactive, Bool.not_false, live, decide_true,
      Bool.true_and, effectiveAt, actualBalanceAt, found, Option.map_some, Option.getD_some] using
      reserve.trans (Nat.le_max_left v.effectiveBalance.toNat
        (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat))
  · simp [selected]

private theorem key_gain_envelope {α : Type} [DecidableEq α]
    (initial recent : Finset α) (before after : α → Nat) (cap : Nat)
    (first : ∀ k ∈ initial, before k ≤ cap)
    (last : ∀ k ∈ recent, after k ≤ cap) :
    (∑ k ∈ recent, (after k - (if k ∈ initial then before k else 0) : Nat)) ≤
      cap * (initial ∪ recent).card - ∑ k ∈ initial, before k := by
  have upper : (∑ k ∈ recent, (after k - (if k ∈ initial then before k else 0))) ≤
      ∑ k ∈ initial ∪ recent, (cap - (if k ∈ initial then before k else 0)) := by
    apply (Finset.sum_le_sum (fun k member =>
      Nat.sub_le_sub_right (last k member) _)).trans
    exact Finset.sum_le_sum_of_subset Finset.subset_union_right
  have small : ∀ k ∈ initial ∪ recent, (if k ∈ initial then before k else 0) ≤ cap := by
    intro k _
    split
    · exact first k ‹_›
    · exact Nat.zero_le _
  have sum : (∑ k ∈ initial ∪ recent, if k ∈ initial then before k else 0) =
      ∑ k ∈ initial, before k := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp
  rw [Finset.sum_tsub_distrib _ small, sum] at upper
  simpa [Nat.mul_comm] using upper

private theorem active_recent_window_keys {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .pectra) :
    (activeKeys x.state ∪ (recentKeys y.state \
      (keysAt x.state (getActiveValidatorIndices x.state (getPreviousEpoch x.state)) \
        activeKeys x.state))).card ≤
      activeCountPath config (referenceCount x + scheduledActivationCount x)
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) := by
  classical
  let indices := (Finset.range y.state.validators.data.size).filter fun i =>
    (y.state.validators.data[i]?).any (·.activationEpoch != FAR_FUTURE_EPOCH) &&
      (x.state.validators.data[i]?).all fun w => w.activationEpoch == FAR_FUTURE_EPOCH ||
        decide (getCurrentEpoch x.state < w.exitEpoch)
  let key := keyAt y.state
  have xEarly : x.fork < .glamsterdam := Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps tail.chainSteps) (Nat.lt_trans early (by decide))
  have finiteX := getCurrentEpoch_ne_farFuture twoSlots x.state
  have finiteY := getCurrentEpoch_ne_farFuture twoSlots y.state
  have finiteBelow {epoch current : Epoch} (finite : current ≠ FAR_FUTURE_EPOCH)
      (lower : epoch ≤ current) : epoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    have bound := UInt64.le_iff_toNat_le.mp lower
    have maximum := current.toNat_lt
    have different := mt UInt64.toNat_inj.mp finite
    rw [far] at bound
    change 18446744073709551615 ≤ _ at bound
    change current.toNat ≠ 18446744073709551615 at different
    omega
  have later := currentEpoch_le_of_chainSteps tail.chainSteps
  have life := tail.registryLifecycle
  have subset : activeKeys x.state ∪ (recentKeys y.state \
      (keysAt x.state (getActiveValidatorIndices x.state (getPreviousEpoch x.state)) \
        activeKeys x.state)) ⊆ indices.image key := by
    intro k member
    rcases Finset.mem_union.mp member with active | recent
    · obtain ⟨i, v, before, same, active⟩ := (mem_keysAt_epoch xEarly _ k).mp active
      obtain ⟨w, after, kept⟩ := life.validators i v before
      obtain ⟨z, zFound, zKey⟩ := validators_getElem?_of_validatorKeys_prefix
        (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 before
      have equal : z = w := Option.some.inj (zFound.symm.trans after)
      have assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
        exact finiteBelow finiteX active.1
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Array.getElem?_eq_some_iff.mp after).1, ?_⟩, ?_⟩
      · simp only [after, Option.any_some, before, Option.all_some, kept.activationEpoch assigned,
          bne_iff_ne, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
        have live : getCurrentEpoch x.state < v.exitEpoch := by
          simpa only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] using
            (show v.activationEpoch ≤ getCurrentEpoch x.state ∧
              getCurrentEpoch x.state < v.exitEpoch from by simpa [isActiveValidator] using active)
            |>.2
        exact ⟨assigned, Or.inr live⟩
      · simp only [key, keyAt, after, Option.map_some, Option.getD_some]
        exact (equal ▸ zKey).trans same
    · obtain ⟨recent, notPrevious⟩ := Finset.mem_sdiff.mp recent
      have support := (Finset.mem_filter.mp recent).1
      obtain ⟨i, w, after, same, active⟩ : ∃ i w, y.state.validators.data[i]? = some w ∧
          w.pubkey = k ∧ (isActiveValidator w (getCurrentEpoch y.state) = true ∨
            isActiveValidator w (getPreviousEpoch y.state) = true) := by
        rcases Finset.mem_union.mp support with now | prev
        · obtain ⟨i, w, found, same, active⟩ :=
            (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ k).mp now
          exact ⟨i, w, found, same, Or.inl active⟩
        · obtain ⟨i, w, found, same, active⟩ :=
            (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ k).mp prev
          exact ⟨i, w, found, same, Or.inr active⟩
      have assigned : w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
        have prev := getPreviousEpoch_le y.state
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
        have lower : w.activationEpoch ≤ getCurrentEpoch y.state :=
          active.elim And.left (fun h => UInt64.le_trans h.1 prev)
        exact finiteBelow finiteY lower
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Array.getElem?_eq_some_iff.mp after).1, ?_⟩, by simp [key, keyAt, after, same]⟩
      simp only [after, Option.any_some, Bool.and_eq_true, bne_iff_ne]
      refine ⟨assigned, ?_⟩
      cases before : x.state.validators.data[i]? with
      | none => rfl
      | some v =>
        by_cases pending : v.activationEpoch = FAR_FUTURE_EPOCH
        · simp [pending]
        · obtain ⟨z, zFound, kept⟩ := life.validators i v before
          have equal : z = w := Option.some.inj (zFound.symm.trans after)
          subst z
          simp only [Option.all_some, Bool.or_eq_true, beq_iff_eq, pending, false_or,
            decide_eq_true_eq]
          by_contra exited
          have exitLe := UInt64.not_lt.mp exited
          have exitAssigned := finiteBelow finiteX exitLe
          have exitSame := kept.exitEpoch exitAssigned
          have epochSame : getCurrentEpoch y.state = getCurrentEpoch x.state := by
            have prevX := getPreviousEpoch_toNat x.state
            have prevY := getPreviousEpoch_toNat y.state
            have le := UInt64.le_iff_toNat_le.mp later
            have exitNat := UInt64.le_iff_toNat_le.mp exitLe
            simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
              exitSame, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at active
            apply UInt64.toNat_inj.mp
            rcases active with now | prev <;> omega
          have oldActive : isActiveValidator v (getPreviousEpoch x.state) = true := by
            have activationSame := kept.activationEpoch pending
            have previousSame : getPreviousEpoch y.state = getPreviousEpoch x.state := by
              apply UInt64.toNat_inj.mp
              simp only [getPreviousEpoch_toNat, epochSame]
            simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
              epochSame, previousSame, activationSame, exitSame] at active
            exact active.elim (fun h => (UInt64.not_lt.mpr exitLe h.2).elim)
              (fun h => by simp [isActiveValidator, h.1, h.2])
          have keyEq := validators_getElem?_of_validatorKeys_prefix
            (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 before
          obtain ⟨z, zFound, zKey⟩ := keyEq
          have equal : z = w := Option.some.inj (zFound.symm.trans after)
          have vKey : v.pubkey = k := (equal ▸ zKey).symm.trans same
          apply notPrevious
          refine Finset.mem_sdiff.mpr ⟨(mem_keysAt_epoch xEarly _ k).mpr
            ⟨i, v, before, vKey, oldActive⟩, ?_⟩
          intro activeKey
          obtain ⟨j, u, uFound, uKey, uActive⟩ := (mem_keysAt_epoch xEarly _ k).mp activeKey
          have unique := shared.pubkeysDistinct genesis
          have eq : u = v := List.inj_on_of_nodup_map unique
            (by simpa using Array.mem_of_getElem? uFound)
            (by simpa using Array.mem_of_getElem? before) (uKey.trans vKey.symm)
          subst u
          have live : getCurrentEpoch x.state < v.exitEpoch := by
            have both : v.activationEpoch ≤ getCurrentEpoch x.state ∧
                getCurrentEpoch x.state < v.exitEpoch := by
              simpa only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] using uActive
            exact both.2
          exact UInt64.not_lt.mpr exitLe live
  exact (Finset.card_le_card subset).trans
    ((Finset.card_image_le).trans (windowActivations_le_countPath shared genesis tail early))

private theorem gain_without_previous_le_count {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (early : y.fork < .pectra) :
    (∑ k ∈ (recentKeys y.state \
        (keysAt x.state (getActiveValidatorIndices x.state (getPreviousEpoch x.state)) \
          activeKeys x.state)),
      (effectiveWeight y.state k -
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k)) ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat *
        activeCountPath config (referenceCount x + scheduledActivationCount x)
          ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) -
              referenceStake x := by
  classical
  have support : ∀ k ∈ (recentKeys y.state \
      (keysAt x.state (getActiveValidatorIndices x.state (getPreviousEpoch x.state)) \
        activeKeys x.state)),
      Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k =
        (if k ∈ activeKeys x.state then effectiveWeight x.state k else 0) := by
    intro k member
    have recent := (Finset.mem_sdiff.mp member).1
    have unslashedX : ¬ SlashedAt x.state k := fun slashed =>
      (Finset.mem_filter.mp recent).2 (slashedAt_forward tail slashed)
    simp [Models.supported, unslashedKeys, unslashedX]
  rw [Finset.sum_congr rfl (fun k member => by rw [support k member])]
  have xEarly : x.fork < .pectra :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have envelope := key_gain_envelope (activeKeys x.state)
    (recentKeys y.state \
      (keysAt x.state (getActiveValidatorIndices x.state (getPreviousEpoch x.state)) \
        activeKeys x.state))
    (effectiveWeight x.state) (effectiveWeight y.state) preset.MAX_EFFECTIVE_BALANCE.toNat
    (fun k _ => effectiveWeight_le_cap shared genesis caps xEarly k)
    (fun k _ => effectiveWeight_le_cap (shared.append tail) genesis caps early k)
  exact envelope.trans (Nat.sub_le_sub_right
    (Nat.mul_le_mul_left _ (active_recent_window_keys shared tail genesis twoSlots early)) _)

private theorem pre_count_headroom (cap activation initial scheduled final stake reserve flow : Nat)
    (ordered : cap ≤ activation) (stakeCap : stake ≤ cap * initial)
    (scheduledPaid : cap * scheduled ≤ reserve)
    (grown : cap * (final - (initial + scheduled)) ≤ flow) :
    cap * final - stake ≤ reserve + flow + (activation * initial - stake) := by
  have initialCap := Nat.mul_le_mul_right initial ordered
  have split : cap * final ≤ cap * initial + cap * scheduled +
      cap * (final - (initial + scheduled)) := by
    have partition : final ≤ initial + scheduled + (final - (initial + scheduled)) := by omega
    exact (Nat.mul_le_mul_left cap partition).trans_eq (by simp only [Nat.mul_add])
  omega

theorem refStake_le_cap_count {g x : ForkedBeaconState preset}
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (early : x.fork < .pectra) :
    referenceStake x ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * referenceCount x := by
  unfold referenceStake Models.stake referenceCount
  exact (Finset.sum_le_sum fun k _ =>
    effectiveWeight_le_cap shared genesis caps early k).trans_eq
    (by simp [Nat.mul_comm])

theorem pre_gain_budget {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .pectra)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) :
    (∑ k ∈ (recentKeys y.state \
        (keysAt x.state (getActiveValidatorIndices x.state (getPreviousEpoch x.state)) \
          activeKeys x.state)),
      (effectiveWeight y.state k -
        Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k)) ≤
      preActiveStake x + fundingCarry x +
        ((List.range (driftHorizon x high + 1)).map fun t =>
          exitFlow preset config (referenceCount x) (scheduledActivationCount x)
              (driftHorizon x high)
            (preElectraEpochs config x high) (stakeCeilingAt config x high) t).sum +
        (if 0 < preElectraEpochs config x high then
          preset.MIN_ACTIVATION_BALANCE.toNat * referenceCount x - referenceStake x else 0) := by
  classical
  have xEarly : x.fork < .pectra :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have forks := (guarded_fork_regime (shared.append tail) genesis high endEpoch guard).1
  have positive := forks.mpr xEarly
  have noCrossing : driftHorizon x high + 2 ≤ preElectraEpochs config x high := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, crossing⟩ := guard
    exact crossing.resolve_left (Nat.ne_of_gt positive)
  let churn := cohortCap config
    (activeCountPath config (referenceCount x + scheduledActivationCount x)
          (driftHorizon x high + 1))
  have flow : ((List.range (driftHorizon x high + 1)).map fun t =>
      exitFlow preset config (referenceCount x) (scheduledActivationCount x) (driftHorizon x high)
        (preElectraEpochs config x high) (stakeCeilingAt config x high) t).sum =
      (driftHorizon x high + 1) * (preset.MIN_ACTIVATION_BALANCE.toNat * churn) := by
    have mapped : ((List.range (driftHorizon x high + 1)).map fun t =>
        exitFlow preset config (referenceCount x) (scheduledActivationCount x) (driftHorizon x high)
          (preElectraEpochs config x high) (stakeCeilingAt config x high) t) =
        (List.range (driftHorizon x high + 1)).map
          (fun _ => preset.MIN_ACTIVATION_BALANCE.toNat * churn) := by
      apply List.map_congr_left
      intro t member
      have within := List.mem_range.mp member
      simp only [exitFlow, show t < preElectraEpochs config x high by omega, ↓reduceIte, churn]
    rw [mapped]
    simp
  have within : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high + 1 := by unfold driftHorizon; omega
  have growth := countPath_growth_window config (referenceCount x + scheduledActivationCount x)
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat)
    (driftHorizon x high + 1) within
  have ordered := UInt64.le_iff_toNat_le.mp caps.activation
  have grown : preset.MAX_EFFECTIVE_BALANCE.toNat *
      (activeCountPath config (referenceCount x + scheduledActivationCount x)
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) -
          (referenceCount x + scheduledActivationCount x)) ≤
      (driftHorizon x high + 1) * (preset.MIN_ACTIVATION_BALANCE.toNat * churn) := by
    exact (Nat.mul_le_mul_left _ growth).trans
      ((Nat.mul_le_mul_right _ ordered).trans_eq (by dsimp [churn]; ac_rfl))
  have stakeCap := refStake_le_cap_count shared genesis caps xEarly
  have paid := pre_count_headroom _ _ _ _ _ _ _ _ ordered stakeCap
    (scheduled_reserve_le_pre shared genesis caps aligned xEarly) grown
  have gain := (gain_without_previous_le_count shared tail genesis caps twoSlots early).trans paid
  rw [flow, ite_eq_left positive]
  omega

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
