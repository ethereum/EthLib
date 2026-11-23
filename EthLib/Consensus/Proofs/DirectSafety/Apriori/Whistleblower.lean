module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling
import EthLib.Consensus.Proofs.Transition.ActiveKept

/-!
# The whistleblower allowance

From Electra, the credits other than rewards and sync credits fit an allowance of the window.

For a branch from `x` to `y`, let `SC` be its slashing credits and `B` the slashable base.

Let `R`, `S` and `D` be the reward, sync and deposit funding credits of the branch.

Then `WQ * SC + B y ≤ B x + R + S + D + SC`, so `(WQ - 1) * SC ≤ B x + R + S + D`.

The allowance reads only the reference state and the length of the window.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-! ## Whistleblower allowance -/

/-- An event charge pays each index its charge once per event that selects it. -/
private theorem countP_charge_le {α : Type} (events : List α) (keys : Finset Nat)
    (chosen : α → Nat → Bool) (credit : α → Nat) (charge : Nat → Nat)
    (supported : ∀ e ∈ events, credit e ≤ ∑ i ∈ keys, if chosen e i then charge i else 0) :
    (events.map credit).sum ≤ ∑ i ∈ keys, (events.countP fun e => chosen e i) * charge i := by
  have exchange : (events.map fun e => ∑ i ∈ keys,
      if chosen e i then charge i else 0).sum =
      ∑ i ∈ keys, (events.countP fun e => chosen e i) * charge i := by
    clear supported
    induction events with
    | nil => simp
    | cons e rest ih =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons, ih,
        Finset.sum_add_distrib, Nat.add_mul]
      rw [Nat.add_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases chosen e i <;> simp
  exact (List.sum_le_sum supported).trans exchange.le

/-- An event charge supported on indices occurring at most once pays each index at most once. -/
private theorem once_only_charge_le {α : Type} (events : List α) (keys : Finset Nat)
    (chosen : α → Nat → Bool) (credit : α → Nat) (charge : Nat → Nat)
    (supported : ∀ e ∈ events, credit e ≤ ∑ i ∈ keys, if chosen e i then charge i else 0)
    (once : ∀ i ∈ keys, (events.countP fun e => chosen e i) ≤ 1) :
    (events.map credit).sum ≤ ∑ i ∈ keys, charge i :=
  (countP_charge_le events keys chosen credit charge supported).trans
    (Finset.sum_le_sum fun i member => by
      simpa using Nat.mul_le_mul_right (charge i) (once i member))

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
theorem slashing_credits_le {config : Config} {checks : SignatureChecks}
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
        v (Array.mem_of_getElem? found)
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

/-! ## The slashable base along a branch -/

/-- A registry position that is unslashed, with its withdrawable epoch after the current epoch. -/
private def pooled (u : ForkedBeaconState preset) (i : Nat) : Bool :=
  (u.state.validators.data[i]?.map fun v =>
    !v.slashed && decide (getCurrentEpoch u.state < v.withdrawableEpoch)).getD false

/-- The larger of the effective and the actual balance at a registry position. -/
private abbrev weight (u : ForkedBeaconState preset) (i : Nat) : Nat :=
  max (effectiveAt u i) (actualBalanceAt u i)

/-- The balance increases of some events at one position. -/
private def creditOf (events : List (BalanceEvent preset)) (i : Nat) : Nat :=
  (events.map fun e => actualBalanceAt e.after i - actualBalanceAt e.before i).sum

/-- The increases of an event at the keys of the slashable base of `v`. -/
private def poolCredit (v : ForkedBeaconState preset) (e : BalanceEvent preset) : Nat :=
  ∑ i ∈ Finset.range v.state.validators.data.size,
    if pooled v i then actualBalanceAt e.after i - actualBalanceAt e.before i else 0

/-- The slashing credit limits of some events. -/
private def slashCredits (events : List (BalanceEvent preset)) : Nat :=
  (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum

/-- The slashable base sums the weights of the keys in it. -/
private theorem slashableBase_eq (u : ForkedBeaconState preset) :
    slashableBase u = ∑ i ∈ Finset.range u.state.validators.data.size,
      if pooled u i then weight u i else 0 := by
  unfold slashableBase
  apply Finset.sum_congr rfl
  intro i _
  cases found : u.state.validators.data[i]? with
  | none => simp [pooled, found]
  | some v =>
    simp only [pooled, found, Option.map_some, Option.getD_some]

/-- The balance at the end of a path is at most the balance at its start and its increases. -/
theorem balance_le_pathCredits (i : Nat) :
    ∀ (path : List (ForkedBeaconState preset)) (a b : ForkedBeaconState preset),
      path.head? = some a → path.getLast? = some b →
        actualBalanceAt b i ≤ actualBalanceAt a i + pathCredits i path
  | [], _, _, first, _ => by simp at first
  | [c], a, b, first, last => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at first last
    subst first last
    omega
  | c :: d :: rest, a, b, first, last => by
    simp only [List.head?_cons, Option.some.injEq] at first
    subst first
    have tail := balance_le_pathCredits i (d :: rest) d b rfl
      (by simpa [List.getLast?_cons_cons] using last)
    simp only [pathCredits]
    omega

/-- The events of one step, read as the events of the one-step run. -/
theorem single_balanceEvents {u v : ForkedBeaconState preset}
    (step : Step config checks u v) {events : List (BalanceEvent preset)}
    (replayed : step.balanceEvents = .ok events) :
    (Run.nil.snoc step).balanceEvents (getCurrentEpoch v.state).toNat = .ok events := by
  have within := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
  simp only [Run.balanceEvents, pure, Except.pure, bind, Except.bind,
    show (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch v.state).toNat + 1 by omega,
    ↓reduceIte, replayed, List.nil_append]

/-- Over one step, the weight of a position rises by at most its credits.

A position new in the step starts from nothing. -/
private theorem step_weight {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v) (early : v.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) (i : Nat) :
    weight v i ≤
      (if i < u.state.validators.data.size then weight u i else 0) + creditOf events i := by
  let run : Run config checks u v := Run.nil.snoc step
  have covered := coverage_run run early _ (Nat.le_succ _) (single_balanceEvents step replayed)
    false i
  simp only [coveragePath, coverageDelta, Bool.false_eq_true, ↓reduceIte] at covered
  change pathCredits i run.balancePath ≤ creditOf events i at covered
  obtain ⟨first, last⟩ := Run.balancePath_ends run
  have balance := balance_le_pathCredits i run.balancePath u v first last
  unfold weight
  split
  · rename_i present
    have gain := effective_gain_from_balance run early i present
    omega
  · rename_i absent
    have join := joining_growth_from_admission shared run genesis early delay i (by omega)
    have matched := (run_justified_separated shared genesis).1.balancesMatch
    have none : actualBalanceAt u i = 0 := by
      have outside : u.state.balances.data[i]? = none :=
        Array.getElem?_eq_none (by unfold BalancesMatch at matched; omega)
      simp [actualBalanceAt, outside]
    omega

/-- A position unslashed before a step is in the slashable base before it.

This holds when it is in the base after the step, or slashed after it. -/
private theorem pooled_of_step {u v : ForkedBeaconState preset}
    (step : Step config checks u v) (caps : CapOrder preset)
    (holds : Invariant u.state) (i : Nat) (w : Validator)
    (found : u.state.validators.data[i]? = some w) (unslashed : w.slashed = false)
    (later : pooled v i = true ∨ (v.state.validators.data[i]?.map (·.slashed)).getD false = true) :
    pooled u i = true := by
  simp only [pooled, found, Option.map_some, Option.getD_some, unslashed, Bool.not_false,
    Bool.true_and, decide_eq_true_eq]
  by_contra withdrawn
  have kept := (EthLib.Consensus.Internal.CapStep.run (Run.nil.snoc step) caps.activation
    caps.compounding).1
  obtain ⟨z, read, _⟩ := kept.monotone i w found
  have exited : w.exitEpoch ≤ getCurrentEpoch u.state :=
    UInt64.le_trans (holds.exitsOrdered w (Array.mem_of_getElem? found))
      (UInt64.not_lt.mp withdrawn)
  obtain ⟨flag, _, same⟩ := kept.retired i w z found read exited unslashed
    (UInt64.not_lt.mp withdrawn)
  have forward := kept.forward
  rcases later with inPool | slashed
  · simp only [pooled, read, Option.map_some, Option.getD_some, flag, Bool.not_false,
      Bool.true_and, decide_eq_true_eq, same] at inPool
    exact withdrawn (UInt64.lt_of_le_of_lt forward inPool)
  · simp [read, flag] at slashed

/-- The credits of some positions, summed event by event. -/
private theorem creditOf_exchange (events : List (BalanceEvent preset)) (s : Finset Nat)
    (keep : Nat → Bool) :
    (∑ i ∈ s, if keep i then creditOf events i else 0) =
      (events.map fun e => ∑ i ∈ s,
        if keep i then actualBalanceAt e.after i - actualBalanceAt e.before i else 0).sum := by
  induction events with
  | nil => simp [creditOf]
  | cons e rest ih =>
    simp only [creditOf, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp

/-- Over one step, the slashable base falls by its keys that leave and rises by its credits. -/
private theorem step_base_split {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v) (caps : CapOrder preset) (early : v.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    slashableBase v + (∑ i ∈ Finset.range u.state.validators.data.size,
        if pooled u i && !pooled v i then weight u i else 0) ≤
      slashableBase u + ∑ i ∈ Finset.range v.state.validators.data.size,
        if pooled v i then creditOf events i else 0 := by
  have holds := (run_justified_separated shared genesis).1
  have grows := (RegistryLifecycle.chainStep step.chainStep).size_le
  let kept (i : Nat) := if pooled u i && pooled v i then weight u i else 0
  have pointwise : ∀ i ∈ Finset.range v.state.validators.data.size,
      (if pooled v i then weight v i else 0) ≤
        (if i < u.state.validators.data.size then kept i else 0) +
          if pooled v i then creditOf events i else 0 := by
    intro i _
    cases member : pooled v i
    · simp
    · have bound := step_weight shared genesis step early delay replayed i
      simp only [↓reduceIte]
      split
      · rename_i present
        have found : u.state.validators.data[i]? = some u.state.validators.data[i] := by
          simp [present]
        have unslashed : u.state.validators.data[i].slashed = false := by
          cases flag : u.state.validators.data[i].slashed with
          | false => rfl
          | true =>
            obtain ⟨z, read, marked⟩ := step.slashedPersistence i _ found flag
            simp [pooled, read, marked] at member
        have before := pooled_of_step step caps holds i _ found unslashed (.inl member)
        simpa [kept, before, member, present] using bound
      · rename_i absent
        simpa [absent] using bound
  have summed := Finset.sum_le_sum pointwise
  rw [Finset.sum_add_distrib] at summed
  have restrict : (∑ i ∈ Finset.range v.state.validators.data.size,
      if i < u.state.validators.data.size then kept i else 0) =
      ∑ i ∈ Finset.range u.state.validators.data.size, kept i := by
    rw [← Finset.sum_subset (Finset.range_mono grows) (fun i _ outside => by
      simp [Nat.not_lt.mp (fun h => outside (Finset.mem_range.mpr h))])]
    exact Finset.sum_congr rfl fun i member => by simp [Finset.mem_range.mp member]
  have whole : slashableBase u = (∑ i ∈ Finset.range u.state.validators.data.size, kept i) +
      ∑ i ∈ Finset.range u.state.validators.data.size,
        if pooled u i && !pooled v i then weight u i else 0 := by
    rw [slashableBase_eq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hu : pooled u i <;> cases hv : pooled v i <;> simp [kept, hu, hv]
  rw [slashableBase_eq v, whole]
  rw [restrict] at summed
  omega

/-- From Electra, `WQ` times the slashing credits of one step is at most a weight.

That weight is the weight of the keys that leave the slashable base in the step. -/
private theorem step_slashing_le {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v) (caps : CapOrder preset) (electra : .pectra ≤ u.fork)
    (early : v.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat * slashCredits events ≤
      ∑ i ∈ Finset.range u.state.validators.data.size,
        if pooled u i && !pooled v i then weight u i else 0 := by
  have holds := (run_justified_separated shared genesis).1
  have quotient : (EthLib.Consensus.parameters preset u.fork).WHISTLEBLOWER_REWARD_QUOTIENT =
      preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA := by
    simp [EthLib.Consensus.parameters, electra]
  let quotientN := preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat
  have charged := countP_charge_le events _ _ _ _
    (slashing_step_support step early holds caps.compounding replayed)
  rw [quotient] at charged
  unfold slashCredits
  apply (Nat.mul_le_mul_left quotientN charged).trans
  rw [Finset.mul_sum]
  let freed (i : Nat) : Nat := if pooled u i && !pooled v i then weight u i else 0
  have pointwise : ∀ i ∈ Finset.range v.state.validators.data.size,
      quotientN * ((events.countP fun e =>
        !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
          (e.after.state.validators.data[i]?.map (·.slashed)).getD false) *
        (effectiveAt u i / quotientN)) ≤ freed i := by
    intro i _
    have count := slashing_step_count_le step early holds caps.compounding replayed i
    split at count
    · rename_i newly
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at newly
      by_cases present : i < u.state.validators.data.size
      · have found : u.state.validators.data[i]? = some u.state.validators.data[i] := by
          simp [present]
        have flag : u.state.validators.data[i].slashed = false := by
          simpa [found] using newly.1
        have before := pooled_of_step step caps holds i _ found flag (.inr newly.2)
        have after : pooled v i = false := by
          cases read : v.state.validators.data[i]? with
          | none => simp [read] at newly
          | some z =>
            have marked : z.slashed = true := by simpa [read] using newly.2
            simp [pooled, read, marked]
        simp only [freed, before, after, Bool.not_false, Bool.and_self, ↓reduceIte]
        calc
          _ ≤ quotientN * (1 * (effectiveAt u i / quotientN)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ count)
          _ ≤ effectiveAt u i := by rw [Nat.one_mul]; exact Nat.mul_div_le _ _
          _ ≤ weight u i := Nat.le_max_left _ _
      · have zero : effectiveAt u i = 0 := by
          simp [effectiveAt, Array.getElem?_eq_none (Nat.le_of_not_lt present)]
        simp [zero]
    · simp [Nat.le_zero.mp count]
  apply (Finset.sum_le_sum pointwise).trans
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : u.state.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
  simp [freed, pooled, absent] at nonzero

/-- The reward, sync and slashing credit limit of an event. -/
private def fundCredit (e : BalanceEvent preset) : Nat :=
  if e.source = .rewards ∨ e.source = .sync ∨ e.source = .slashings then e.creditLimit else 0

/-- The fund credits are the reward, sync and slashing credit limits. -/
private theorem fundCredit_sum (events : List (BalanceEvent preset)) :
    (events.map fundCredit).sum = sourceCredits .rewards events + sourceCredits .sync events +
      slashCredits events := by
  induction events with
  | nil => simp [sourceCredits, slashCredits]
  | cons e rest ih =>
    simp only [sourceCredits, slashCredits, List.map_cons, List.sum_cons] at ih ⊢
    have single : fundCredit e = (if e.source = .rewards then e.creditLimit else 0) +
        (if e.source = .sync then e.creditLimit else 0) +
          (if e.source = .slashings then e.creditLimit else 0) := by
      obtain ⟨source, _, _, _, _⟩ := e
      cases source <;> simp [fundCredit]
    omega

/-- The increases of an event at some positions, within its credit limit. -/
private theorem kept_credits_le (e : BalanceEvent preset) (n : Nat) (keep : Nat → Bool)
    (bounded : e.credits ≤ e.creditLimit) :
    (∑ i ∈ Finset.range n,
      if keep i then actualBalanceAt e.after i - actualBalanceAt e.before i else 0) ≤
        e.creditLimit :=
  le_trans (Finset.sum_le_sum fun i _ => by split <;> simp [coverageDelta])
    ((coverage_event_sum e n false).trans bounded)

/-- An event that is neither a deposit nor a pending consolidation credits its fund credit. -/
private theorem kept_credits_le_fund (e : BalanceEvent preset) (n : Nat)
    (keep : Nat → Bool) (bounded : e.credits ≤ e.creditLimit)
    (sources : 0 < e.creditLimit → e.source = .rewards ∨ e.source = .sync ∨
      e.source = .slashings ∨ e.source = .deposits ∨ e.source = .consolidations)
    (deposit : e.source ≠ .deposits ∨ e.creditLimit = 0)
    (transfer : e.source ≠ .consolidations ∨ e.creditLimit = 0) :
    (∑ i ∈ Finset.range n,
      if keep i then actualBalanceAt e.after i - actualBalanceAt e.before i else 0) ≤
        fundCredit e := by
  have within := kept_credits_le e n keep bounded
  by_cases positive : 0 < e.creditLimit
  · have funded : fundCredit e = e.creditLimit := by
      rcases sources positive with h | h | h | h | h
      · simp [fundCredit, h]
      · simp [fundCredit, h]
      · simp [fundCredit, h]
      · rcases deposit with d | d
        · exact absurd h d
        · omega
      · rcases transfer with d | d
        · exact absurd h d
        · omega
    omega
  · omega

/-- The events of one step are within their limits, and their credits have five sources. -/
private theorem step_event_limits {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v) (early : v.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    ∀ e ∈ events, e.credits ≤ e.creditLimit ∧ u.fork ≤ e.before.fork ∧
      (0 < e.creditLimit → e.source = .rewards ∨ e.source = .sync ∨
        e.source = .slashings ∨ e.source = .deposits ∨ e.source = .consolidations) := by
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared (Run.nil.snoc step)
    genesis early (getCurrentEpoch v.state).toNat
  rw [single_balanceEvents step replayed, Except.ok.injEq] at foundOk
  subst foundOk
  intro e member
  have sources := step.balanceEvents_credit_sources early
    (run_justified_separated shared genesis).1 replayed e member
  exact ⟨(bounded e member).1, sources.1, sources.2⟩

/-- From Electra, a block credits the slashable base at most its fund credits.

A block records no pending consolidation, and its deposit events credit nothing. -/
private theorem block_credits_le {g : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨fork, s⟩)
    (genesis : Genesis (config := config) (checks := checks) g)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (n : Nat) (keep : Nat → Bool) :
    ∀ e ∈ events, (∑ i ∈ Finset.range n,
      if keep i then actualBalanceAt e.after i - actualBalanceAt e.before i else 0) ≤
        fundCredit e := by
  let step : Step config checks ⟨fork, s⟩ ⟨fork, t⟩ := .block engine signed due ok
  have limits := step_event_limits shared genesis step early replayed
  have noDeposits := funding_block_events early engine signed.message
    (Step.balanceEvents_block early replayed)
  have sites := step.balanceEvents_sites early (run_justified_separated shared genesis).1
    compounding replayed
  have slot : t.slot = s.slot := (frame_processBlock (applySignedBlock_ok ok).2.1).slot
  intro e member
  obtain ⟨bounded, forkLe, sources⟩ := limits e member
  refine kept_credits_le_fund e n keep bounded sources ?_ ?_
  · by_cases source : e.source = .deposits
    · exact .inr (noDeposits e member source (Nat.le_trans electra forkLe))
    · exact .inl source
  · left
    intro source
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, passEpoch, -⟩ :=
      sites e member
    have later := passEpoch source
    obtain ⟨-, -, -, -, -, lower, -⟩ := replay_event_provenance shared (Run.nil.snoc step)
      genesis early _ (Nat.le_succ _) events (single_balanceEvents step replayed) e member
    have same : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
    change (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch t).toNat at later
    change (getCurrentEpoch s).toNat ≤ (getCurrentEpoch e.before.state).toNat at lower
    rw [same] at later
    omega

/-- From Electra, the slot cache and the epoch stages before the deposits keep the registry size.

They also keep the epoch, and keep each withdrawable epoch that is after the epoch. -/
private theorem prefix_withdrawable {fork : Fork}
    {s cached justified scored rewarded registered slashed reset : BeaconState preset fork}
    (electra : .pectra ≤ fork) (cachedOk : processSlot s = .ok cached)
    (justifiedOk : EpochStage.Edge config checks .justification cached justified)
    (scoredOk : EpochStage.Edge config checks .inactivity justified scored)
    (rewardedOk : processRewardsAndPenalties config scored = .ok rewarded)
    (registeredOk : processRegistryUpdates config rewarded = .ok registered)
    (slashedOk : processSlashings registered = .ok slashed)
    (resetOk : EpochStage.Edge config checks .eth1Reset slashed reset) :
    reset.validators.data.size = s.validators.data.size ∧
      getCurrentEpoch reset = getCurrentEpoch s ∧
      ∀ (i : Nat) (v : Validator), s.validators.data[i]? = some v →
        getCurrentEpoch s < v.withdrawableEpoch →
          ∃ w, reset.validators.data[i]? = some w ∧
            getCurrentEpoch reset < w.withdrawableEpoch := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  have one := justifiedOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have two := scoredOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have three := EpochStage.Edge.validators_eq (stage := .rewards) (config := config)
    (checks := checks) rewardedOk ⟨nofun, nofun, nofun⟩
  have threeSlot := (frame_processRewardsAndPenalties rewardedOk).slot
  have fourSlot := (frame_processRegistryUpdates registeredOk).slot
  have fourSize := (sameSizes_processRegistryUpdates registeredOk).1
  have five := EpochStage.Edge.validators_eq (stage := .slashings) (config := config)
    (checks := checks) slashedOk ⟨nofun, nofun, nofun⟩
  have fiveSlot := (frame_processSlashings slashedOk).slot
  have six := resetOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
  have epoch : getCurrentEpoch reset = getCurrentEpoch s := by
    simp only [getCurrentEpoch, six.2.2.2.2, fiveSlot, fourSlot, threeSlot, two.2.2.2.2,
      one.2.2.2.2]
  have rewardedEpoch : getCurrentEpoch rewarded = getCurrentEpoch s := by
    simp only [getCurrentEpoch, threeSlot, two.2.2.2.2, one.2.2.2.2]
  refine ⟨?_, epoch, fun i v found late => ?_⟩
  · rw [six.1, five, fourSize, three, two.1, one.1]
  · have atRewarded : rewarded.validators.data[i]? = some v := by
      rw [three, two.1, one.1]; exact found
    have atReset (w : Validator) (read : registered.validators.data[i]? = some w) :
        reset.validators.data[i]? = some w := by
      rw [six.1, five]; exact read
    rw [epoch]
    by_cases assigned : v.exitEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨w, read, same | after⟩ := processRegistryUpdates_withdrawableEpoch_of_unassigned
        electra registeredOk i v atRewarded assigned
      · exact ⟨w, atReset w read, same ▸ late⟩
      · exact ⟨w, atReset w read, rewardedEpoch ▸ after⟩
    · obtain ⟨w, read, same⟩ := processRegistryUpdates_withdrawableEpoch_of_assigned
        electra registeredOk i v atRewarded assigned
      exact ⟨w, atReset w read, same ▸ late⟩

/-- A key of the slashable base after a step, present before it, was in the base before it. -/
private theorem pooled_before {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v) (caps : CapOrder preset)
    (i : Nat) (present : i < u.state.validators.data.size) (member : pooled v i = true) :
    pooled u i = true := by
  have found : u.state.validators.data[i]? = some u.state.validators.data[i] := by
    simp [present]
  have unslashed : u.state.validators.data[i].slashed = false := by
    cases flag : u.state.validators.data[i].slashed with
    | false => rfl
    | true =>
      obtain ⟨z, read, marked⟩ := step.slashedPersistence i _ found flag
      simp [pooled, read, marked] at member
  exact pooled_of_step step caps (run_justified_separated shared genesis).1 i _ found
    unslashed (.inl member)

/-- From Electra, the pending deposits credit the slashable base at most their funding credit.

That credit counts the deposits to keys that are not withdrawable at the epoch.

The base is read at the end of the slot, and each of its keys is not withdrawable then. -/
private theorem deposit_le_funding {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v) (caps : CapOrder preset) (electra : .pectra ≤ u.fork)
    (early : v.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    {cached justified scored rewarded registered slashed reset deposited :
      BeaconState preset u.fork}
    (cachedOk : processSlot u.state = .ok cached)
    (justifiedOk : EpochStage.Edge config checks .justification cached justified)
    (scoredOk : EpochStage.Edge config checks .inactivity justified scored)
    (rewardedOk : processRewardsAndPenalties config scored = .ok rewarded)
    (registeredOk : processRegistryUpdates config rewarded = .ok registered)
    (slashedOk : processSlashings registered = .ok slashed)
    (resetOk : EpochStage.Edge config checks .eth1Reset slashed reset)
    (member : (⟨.deposits, ⟨u.fork, reset⟩, ⟨u.fork, deposited⟩,
      consumedDeposits reset deposited electra, 0⟩ : BalanceEvent preset) ∈ events) :
    (∑ i ∈ Finset.range v.state.validators.data.size, if pooled v i then
        actualBalanceAt ⟨u.fork, deposited⟩ i - actualBalanceAt ⟨u.fork, reset⟩ i else 0) ≤
      funding_deposit_credit (⟨.deposits, ⟨u.fork, reset⟩, ⟨u.fork, deposited⟩,
        consumedDeposits reset deposited electra, 0⟩ : BalanceEvent preset) := by
  obtain ⟨size, epoch, kept⟩ := prefix_withdrawable electra cachedOk justifiedOk scoredOk
    rewardedOk registeredOk slashedOk resetOk
  obtain ⟨-, -, -, -, matched, -, -⟩ := replay_event_provenance shared (Run.nil.snoc step)
    genesis early _ (Nat.le_succ _) events (single_balanceEvents step replayed) _ member
  simp only [funding_deposit_credit, electra, and_self, ↓reduceIte]
  let credit (i : Nat) : Nat :=
    if (reset.validators.data[i]?.map fun w =>
        decide (w.withdrawableEpoch.toNat ≤ (getCurrentEpoch reset).toNat)).getD false then 0
    else actualBalanceAt ⟨u.fork, deposited⟩ i - actualBalanceAt ⟨u.fork, reset⟩ i
  have pointwise : ∀ i ∈ Finset.range v.state.validators.data.size,
      (if pooled v i then
        actualBalanceAt ⟨u.fork, deposited⟩ i - actualBalanceAt ⟨u.fork, reset⟩ i else 0) ≤
        credit i := by
    intro i _
    cases member : pooled v i
    · exact Nat.zero_le _
    · have waiting : (reset.validators.data[i]?.map fun w =>
          decide (w.withdrawableEpoch.toNat ≤ (getCurrentEpoch reset).toNat)).getD false =
            false := by
        by_cases present : i < u.state.validators.data.size
        · have before := pooled_before shared genesis step caps i present member
          have found : u.state.validators.data[i]? = some u.state.validators.data[i] := by
            simp [present]
          simp only [pooled, found, Option.map_some, Option.getD_some, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_true_eq] at before
          obtain ⟨w, read, late⟩ := kept i _ found before.2
          simp only [read, Option.map_some, Option.getD_some, decide_eq_false_iff_not,
            Nat.not_le]
          exact UInt64.lt_iff_toNat_lt.mp late
        · have absent : reset.validators.data[i]? = none :=
            Array.getElem?_eq_none (by omega)
          simp [absent]
      simp [credit, waiting]
  apply (Finset.sum_le_sum pointwise).trans
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : deposited.balances.data[i]? = none :=
    Array.getElem?_eq_none (by unfold BalancesMatch at matched; simp at matched; omega)
  simp [credit, actualBalanceAt, absent] at nonzero

/-- From Electra, the pending consolidations of an epoch move at most a weight.

That weight is the weight of their sources at the start of the slot.

The sources that move a positive amount leave the slashable base in the slot.

Skipped slashed sources move nothing, and are not in the base at the start of the slot.

A source that is a target earlier in the same pass moves at most its prior effective balance. -/
private theorem pass_le_freed {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (electra : .pectra ≤ u.fork) (early : v.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    {deposited middle updated : BeaconState preset u.fork}
    (passOk : processPendingConsolidations deposited electra = .ok middle)
    (member : (⟨.consolidations, ⟨u.fork, deposited⟩, ⟨u.fork, middle⟩,
      consumedConsolidations deposited middle electra,
      consumedConsolidations deposited middle electra⟩ : BalanceEvent preset) ∈ events)
    (queue : deposited.pendingConsolidations electra = u.state.pendingConsolidations electra)
    (effective : ∀ i, i < u.state.validators.data.size →
      effectiveAt ⟨u.fork, deposited⟩ i = effectiveAt u i)
    (epochEq : getCurrentEpoch deposited = getCurrentEpoch u.state)
    (updatedOk : processEffectiveBalanceUpdates middle = .ok updated)
    (final : v.state.validators.data = updated.validators.data)
    (nextEpoch : (getCurrentEpoch v.state).toNat = (getCurrentEpoch u.state).toNat + 1) :
    consumedConsolidations deposited middle electra ≤
      ∑ i ∈ Finset.range u.state.validators.data.size,
        if pooled u i && !pooled v i then weight u i else 0 := by
  have uEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  have invariant := Run.pendingConsolidation_invariant shared genesis electra delay
  have ordered := ((Run.pendingConsolidationsOrdered shared genesis delay).2 electra).2
  have sites := step.balanceEvents_sites early (run_justified_separated shared genesis).1
    compounding replayed
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, slashedInto, -⟩ := sites _ member
  obtain ⟨-, -, -, -, matched, -, -⟩ := replay_event_provenance shared (Run.nil.snoc step)
    genesis early _ (Nat.le_succ _) events (single_balanceEvents step replayed) _ member
  have passedValidators := (processPendingConsolidations_kept passOk).1
  let freed (i : Nat) : Nat := if pooled u i && !pooled v i then weight u i else 0
  let p := fun c : PendingConsolidation =>
    deposited.validators.data[c.sourceIndex.toNat]?.any fun source =>
      source.slashed || source.withdrawableEpoch ≤ getCurrentEpoch deposited + 1
  let front := (deposited.pendingConsolidations electra).data.toList.takeWhile p
  have sub : front.Sublist (u.state.pendingConsolidations electra).data.toList := by
    rw [← queue]; exact List.takeWhile_sublist p
  have noOverflow : (getCurrentEpoch deposited + 1).toNat =
      (getCurrentEpoch deposited).toNat + 1 := by
    have bound := (getCurrentEpoch v.state).toNat_lt
    rw [epochEq]
    exact toNat_add_of_lt (by simp; omega)
  have pointwise : ∀ c ∈ front,
      (match deposited.validators.data[c.sourceIndex.toNat]? with
        | none => 0
        | some v => if v.slashed then 0 else v.effectiveBalance.toNat) ≤
        freed c.sourceIndex.toNat := by
    intro c inFront
    have inQueue := sub.subset inFront
    have consumed : p c = true := List.all_eq_true.mp List.all_takeWhile c inFront
    obtain ⟨initial, initialFound, -, -, -⟩ := invariant.2 c inQueue
    have late := (ordered c inQueue initial initialFound).2.2
    cases depositedFound : deposited.validators.data[c.sourceIndex.toNat]? with
    | none => exact Nat.zero_le _
    | some w =>
      simp only
      split
      · exact Nat.zero_le _
      · rename_i unslashed
        have unslashedW : w.slashed = false := by simpa using unslashed
        have present : c.sourceIndex.toNat < u.state.validators.data.size :=
          (Array.getElem?_eq_some_iff.mp initialFound).1
        have initialUnslashed : initial.slashed = false := by
          cases flag : initial.slashed with
          | false => rfl
          | true =>
            obtain ⟨z, read, marked⟩ := slashedInto _ initial initialFound flag
            rw [depositedFound, Option.some.injEq] at read
            subst read
            simp [unslashedW] at marked
        have before : pooled u c.sourceIndex.toNat = true := by
          simp only [pooled, initialFound, Option.map_some, Option.getD_some, initialUnslashed,
            Bool.not_false, Bool.true_and, decide_eq_true_eq]
          exact UInt64.lt_iff_toNat_lt.mpr late
        have due : w.withdrawableEpoch.toNat ≤ (getCurrentEpoch deposited).toNat + 1 := by
          have := consumed
          simp only [p, depositedFound, Option.any_some, unslashedW, Bool.false_or,
            decide_eq_true_eq] at this
          rw [← noOverflow]
          exact UInt64.le_iff_toNat_le.mp this
        have middleFound : middle.validators.data[c.sourceIndex.toNat]? = some w := by
          rw [passedValidators]; exact depositedFound
        obtain ⟨_, owned⟩ : ∃ b, middle.balances.data[c.sourceIndex.toNat]? = some b := by
          have inside := (Array.getElem?_eq_some_iff.mp middleFound).1
          unfold BalancesMatch at matched
          simp only at matched
          exact ⟨_, Array.getElem?_eq_getElem (by omega)⟩
        obtain ⟨_, updatedFound, -⟩ :=
          processEffectiveBalanceUpdates_effectiveBalance_eq updatedOk middleFound owned
        have after : pooled v c.sourceIndex.toNat = false := by
          simp only [pooled, final, updatedFound, Option.map_some, Option.getD_some,
            unslashedW, Bool.not_false, Bool.true_and, decide_eq_false_iff_not,
            UInt64.lt_iff_toNat_lt]
          rw [epochEq] at due
          omega
        simp only [freed, before, after, Bool.not_false, Bool.and_self, ↓reduceIte]
        have value : w.effectiveBalance.toNat = effectiveAt u c.sourceIndex.toNat := by
          rw [← effective _ present]
          simp [effectiveAt, depositedFound]
        rw [value]
        exact Nat.le_max_left _ _
  -- The pass consumes the front of sources that are slashed or can withdraw next.
  have consumedEq : consumedConsolidations deposited middle electra = (front.map
      fun c => match deposited.validators.data[c.sourceIndex.toNat]? with
        | none => 0
        | some v => if v.slashed then 0 else v.effectiveBalance.toNat).sum := by
    have remaining := processPendingConsolidations_queue passOk
    unfold consumedConsolidations
    congr 2
    have whole := List.takeWhile_append_dropWhile
      (l := (deposited.pendingConsolidations electra).data.toList) (p := p)
    have sizes : (middle.pendingConsolidations electra).data.size =
        ((deposited.pendingConsolidations electra).data.toList.dropWhile p).length := by
      rw [← remaining, Array.length_toList]
    rw [sizes, ← Array.length_toList]
    simp only [front]
    generalize (deposited.pendingConsolidations electra).data.toList = l at whole ⊢
    have length := congrArg List.length whole
    rw [List.length_append] at length
    rw [← length, Nat.add_sub_cancel]
    conv => lhs; arg 2; rw [← whole]
    exact List.take_left' rfl
  rw [consumedEq]
  change (front.map _).sum ≤ ∑ i ∈ Finset.range u.state.validators.data.size, freed i
  apply (List.sum_le_sum pointwise).trans
  have nodup : (front.map fun c => c.sourceIndex.toNat).Nodup := by
    have base := List.Nodup.map (f := UInt64.toNat) (fun _ _ eq => UInt64.toNat_inj.mp eq)
      (invariant.1.sublist (sub.map (·.sourceIndex)))
    simpa [List.map_map, Function.comp_def] using base
  have reorder : front.map (fun c => freed c.sourceIndex.toNat) =
      (front.map fun c => c.sourceIndex.toNat).map freed := by
    simp [List.map_map, Function.comp_def]
  rw [reorder, ← List.sum_toFinset _ nodup]
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : u.state.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
  simp [pooled, absent] at nonzero

/-- From Electra, a slot pays no slashing credit.

Its credits to the slashable base at its end are at most a sum.

The sum is its fund credits, its deposit funding credits and the weight of the keys that leave. -/
private theorem slot_credits_le {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (ok : advanceSlotAcross config checks u = .ok v) (caps : CapOrder preset)
    (electra : .pectra ≤ u.fork) (early : v.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events) :
    slashCredits events = 0 ∧ (events.map (poolCredit v)).sum ≤
      (∑ i ∈ Finset.range u.state.validators.data.size,
        if pooled u i && !pooled v i then weight u i else 0) +
        (events.map fundCredit).sum + (events.map funding_deposit_credit).sum := by
  let step : Step config checks u v := .slot ok
  have limits := step_event_limits shared genesis step early replayed
  have ordinary (e : BalanceEvent preset) (member : e ∈ events)
      (notDeposit : e.source ≠ .deposits) (notTransfer : e.source ≠ .consolidations) :
      poolCredit v e ≤ fundCredit e :=
    kept_credits_le_fund e _ _ (limits e member).1 (limits e member).2.2 (.inl notDeposit)
      (.inl notTransfer)
  have noSlash (e : BalanceEvent preset) (notSlash : e.source ≠ .slashings) :
      (if e.source = .slashings then e.creditLimit else 0) = 0 := by simp [notSlash]
  obtain ⟨advanced, cached, crossings, advanceOk, upgrades, cachedOk, crossed, shape⟩ :=
    Step.balanceEvents_slot ok early replayed
  have crossing := upgradeBalanceReplay_crossing crossed
  rcases shape with ⟨_, rfl⟩ | ⟨middle, updated, recorded, replay, updatedOk, advancedValidators,
    -, rfl, next, sum, advancedSlot, last, beforeOk⟩
  · refine ⟨List.sum_eq_zero fun n member => ?_, ?_⟩
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      exact noSlash e (by rw [crossing e inside]; decide)
    · refine (List.sum_le_sum fun e member => ordinary e member
        (by rw [crossing e member]; decide) (by rw [crossing e member]; decide)).trans ?_
      omega
  obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, rewardEvents, limit,
    -, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk, depositedOk,
    consolidatedOk, rewardReplay, shapeEq⟩ := funding_epoch_site beforeOk replay
  simp only [electra, ↓reduceDIte] at shapeEq
  subst shapeEq
  simp only [EpochStage.Edge, electra, ↓reduceDIte] at depositedOk consolidatedOk
  have rewardSources : ∀ e ∈ rewardEvents,
      e.source = .rewards ∨ e.source = .penalties ∨ e.source = .inactivity :=
    replayRewards_sources (by simp) rewardReplay
  have depMember : (⟨.deposits, ⟨u.fork, reset⟩, ⟨u.fork, deposited⟩,
      consumedDeposits reset deposited electra, 0⟩ : BalanceEvent preset) ∈
      rewardEvents ++ [⟨.slashings, ⟨u.fork, registered⟩, ⟨u.fork, slashed⟩, 0, limit⟩] ++
        [⟨.deposits, ⟨u.fork, reset⟩, ⟨u.fork, deposited⟩,
          consumedDeposits reset deposited electra, 0⟩,
        ⟨.consolidations, ⟨u.fork, deposited⟩, ⟨u.fork, middle⟩,
          consumedConsolidations deposited middle electra,
          consumedConsolidations deposited middle electra⟩] ++ crossings := by simp
  have consMember : (⟨.consolidations, ⟨u.fork, deposited⟩, ⟨u.fork, middle⟩,
      consumedConsolidations deposited middle electra,
      consumedConsolidations deposited middle electra⟩ : BalanceEvent preset) ∈
      rewardEvents ++ [⟨.slashings, ⟨u.fork, registered⟩, ⟨u.fork, slashed⟩, 0, limit⟩] ++
        [⟨.deposits, ⟨u.fork, reset⟩, ⟨u.fork, deposited⟩,
          consumedDeposits reset deposited electra, 0⟩,
        ⟨.consolidations, ⟨u.fork, deposited⟩, ⟨u.fork, middle⟩,
          consumedConsolidations deposited middle electra,
          consumedConsolidations deposited middle electra⟩] ++ crossings := by simp
  have deposit := deposit_le_funding shared genesis step caps electra early replayed cachedOk
    justifiedOk scoredOk rewardedOk registeredOk slashedOk resetOk depMember
  -- The pass reads the queue, the effective balances and the epoch at the start of the slot.
  obtain ⟨_, epochReset, _⟩ := prefix_withdrawable electra cachedOk justifiedOk scoredOk
    rewardedOk registeredOk slashedOk resetOk
  have cachedSame : cached.validators = u.state.validators ∧
      cached.pendingConsolidations = u.state.pendingConsolidations := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl⟩
  have queue : deposited.pendingConsolidations electra = u.state.pendingConsolidations electra := by
    have one := justifiedOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    have two := scoredOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    have three : rewarded.pendingConsolidations = scored.pendingConsolidations :=
      EpochStage.Edge.samePendingQueue (stage := .rewards) (config := config) (checks := checks)
        rewardedOk nofun
    have four := (processRegistryUpdates_kept registeredOk).2
    have five : slashed.pendingConsolidations = registered.pendingConsolidations :=
      EpochStage.Edge.samePendingQueue (stage := .slashings) (config := config)
        (checks := checks) slashedOk nofun
    have six := resetOk.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
    have seven : deposited.pendingConsolidations = reset.pendingConsolidations :=
      EpochStage.Edge.samePendingQueue (stage := .pendingDeposits) (config := config)
        (checks := checks) (by simpa only [EpochStage.Edge, electra, ↓reduceDIte] using depositedOk)
        nofun
    rw [seven, six.2.2.1, five, four, three, two.2.2.1, one.2.2.1, cachedSame.2]
  have effective : ∀ i, i < u.state.validators.data.size →
      effectiveAt ⟨u.fork, deposited⟩ i = effectiveAt u i := by
    intro i present
    have kept := effectiveKept_epochBeforePayments beforeOk i
      (by rw [cachedSame.1]; exact present)
    have passed := (processPendingConsolidations_kept consolidatedOk).1
    have sameDeposited : effectiveAt ⟨u.fork, deposited⟩ i = effectiveAt ⟨u.fork, middle⟩ i := by
      simp [effectiveAt, passed]
    have sameCached : effectiveAt ⟨u.fork, cached⟩ i = effectiveAt u i := by
      simp [effectiveAt, cachedSame.1]
    rw [sameDeposited, kept, sameCached]
  have epochDeposited : getCurrentEpoch deposited = getCurrentEpoch u.state := by
    rw [← epochReset]
    simp [getCurrentEpoch, (frame_processPendingDeposits depositedOk).slot]
  have final : v.state.validators.data = updated.validators.data := by
    rw [processUpgrades_validators_of_electra (s := ⟨u.fork, advanced⟩) electra early upgrades,
      advancedValidators]
  have nextEpoch : (getCurrentEpoch v.state).toNat = (getCurrentEpoch u.state).toNat + 1 := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat,
      show v.state.slot = next from (processUpgrades_slot upgrades).trans advancedSlot]
    exact nextSlot_epoch_of_boundary sum last
  have transfer := pass_le_freed shared genesis step caps.compounding electra early delay replayed
    consolidatedOk consMember queue effective epochDeposited updatedOk final nextEpoch
  have consKeep := (kept_credits_le _ v.state.validators.data.size (pooled v)
    (limits _ consMember).1).trans transfer
  constructor
  · simp only [slashCredits, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have rewardsZero : (rewardEvents.map fun e =>
        if e.source = .slashings then e.creditLimit else 0).sum = 0 :=
      List.sum_eq_zero fun n member => by
        obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
        exact noSlash e (by rcases rewardSources e inside with h | h | h <;> rw [h] <;> decide)
    have crossingsZero : (crossings.map fun e =>
        if e.source = .slashings then e.creditLimit else 0).sum = 0 :=
      List.sum_eq_zero fun n member => by
        obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
        exact noSlash e (by rw [crossing e inside]; decide)
    simp only [rewardsZero, crossingsZero]
    simp
  · have rewardsBound := List.sum_le_sum fun e (member : e ∈ rewardEvents) =>
      ordinary e (by simp [member])
        (by rcases rewardSources e member with h | h | h <;> rw [h] <;> decide)
        (by rcases rewardSources e member with h | h | h <;> rw [h] <;> decide)
    have crossingsBound := List.sum_le_sum fun e (member : e ∈ crossings) =>
      ordinary e (by simp [member]) (by rw [crossing e member]; decide)
        (by rw [crossing e member]; decide)
    have slashBound := ordinary ⟨.slashings, ⟨u.fork, registered⟩, ⟨u.fork, slashed⟩, 0, limit⟩
      (by simp) nofun nofun
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at rewardsBound crossingsBound ⊢
    simp only [poolCredit] at rewardsBound crossingsBound slashBound consKeep ⊢
    omega

/-- From Electra, one step raises the slashable base by at most its credits.

The credits are its fund and deposit funding credits, less `WQ` times its slashing credits. -/
private theorem step_base_bound {g u v : ForkedBeaconState preset}
    (shared : Run config checks g u) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks u v) (caps : CapOrder preset) (electra : .pectra ≤ u.fork)
    (early : v.fork < .glamsterdam) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat * slashCredits events + slashableBase v ≤
      slashableBase u + (events.map fundCredit).sum + (events.map funding_deposit_credit).sum := by
  have split := step_base_split shared genesis step caps early delay replayed
  rw [creditOf_exchange] at split
  change _ ≤ _ + (events.map (poolCredit v)).sum at split
  cases step with
  | @block fork s t engine signed due ok =>
    have slashing := step_slashing_le shared genesis (.block engine signed due ok) caps electra
      early replayed
    have credits := List.sum_le_sum fun e member =>
      block_credits_le shared genesis caps.compounding electra early replayed
        t.validators.data.size (pooled ⟨fork, t⟩) e member
    change (events.map (poolCredit ⟨fork, t⟩)).sum ≤ _ at credits
    omega
  | slot ok =>
    obtain ⟨zero, credits⟩ := slot_credits_le shared genesis ok caps electra early delay replayed
    rw [zero, Nat.mul_zero]
    omega

/-- From Electra, a branch raises the slashable base by at most its credits.

The credits are its fund and deposit funding credits, less `WQ` times its slashing credits. -/
private theorem run_base_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat * slashCredits events + slashableBase y ≤
      slashableBase x + (events.map fundCredit).sum + (events.map funding_deposit_credit).sum := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    simp [slashCredits]
  | @snoc middle last pre step ih =>
    have selected := (UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    have previous := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected priorOk
    have current := step_base_bound (shared.append pre) genesis step caps
      (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) early delay addedOk
    simp only [slashCredits, List.map_append, List.sum_append] at previous current ⊢
    rw [Nat.mul_add]
    omega

/-- From Electra, `WQ - 1` times the slashing credits of a branch is at most a sum.

The sum is the slashable base at `x`, plus the reward, sync and deposit funding credits. -/
private theorem slashingCredits_le_base {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat - 1) *
        (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      slashableBase x + sourceCredits .rewards events + sourceCredits .sync events +
        (events.map funding_deposit_credit).sum := by
  have bound := run_base_bound shared genesis tail caps electra early delay high endEpoch replayed
  rw [fundCredit_sum] at bound
  change _ * slashCredits events ≤ _
  generalize slashCredits events = paid at bound ⊢
  cases quotient : preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA.toNat with
  | zero => simp
  | succ k =>
    rw [quotient, Nat.succ_mul] at bound
    simp only [Nat.add_sub_cancel]
    omega

/-- From Electra, the whistleblower allowance read at `x` pays every other funding credit.

The reward and sync credits must fit the issuance envelope.

The deposit funding credits must fit the deposit carry and the exit flow of the window. -/
theorem otherCredit_le_allowanceAt_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (issued : sourceCredits .rewards events + sourceCredits .sync events ≤
      windowIssuance (config := config) x high)
    (deposited : (events.map funding_deposit_credit).sum ≤ fundingCarry x +
      ((List.range (driftHorizon x high + 1)).map (exitFlowAt (config := config) x high)).sum) :
    (events.map otherCredit).sum ≤ whistleblowerAllowanceAt (config := config) x high := by
  have omega := otherCredit_le_allowance_electra shared genesis tail caps aligned electra early
    twoSlots high endEpoch guard replayed
  have notElectra : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notElectra]
  simp only [whistleblowerAllowanceAt, zero, Nat.lt_irrefl, ↓reduceIte]
  rw [zero] at omega
  split
  · rename_i quotient
    refine le_min omega ?_
    obtain ⟨-, -, -, -, -, -, -, -, -, delay, -, -, -, -⟩ := guard
    have base := slashingCredits_le_base shared genesis tail caps electra early (by omega) high
      endEpoch replayed
    rw [otherCredit_sum_electra shared tail genesis electra early (by omega) replayed]
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    rw [Nat.mul_comm]
    omega
  · exact omega

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
      have assigned := Consensus.Internal.assigned_of_active active
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
      have assigned := active.elim Consensus.Internal.assigned_of_active
        Consensus.Internal.assigned_of_active
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
