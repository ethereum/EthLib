module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Ledger
import EthLib.Consensus.Proofs.Transition.ActiveKept

/-!
# The new cohorts of a branch

The keys that join or leave the cohort within the window, and the allocation of their charges.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section RunContracts
variable {g x y : ForkedBeaconState preset}

def base (x : ForkedBeaconState preset) (i : Nat) :=
  if x.fork < .pectra then min (max (effectiveAt x i) (actualBalanceAt x i))
    preset.MAX_EFFECTIVE_BALANCE.toNat else max (effectiveAt x i) (actualBalanceAt x i)
structure ScheduledAllocation (x y : ForkedBeaconState preset) (high : Nat) where
  scheduled : Finset Nat
  exactScheduled : scheduled = (Finset.range x.state.validators.data.size).filter fun i =>
    (x.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
        decide (v.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ v.exitEpoch.toNat ≤ horizonEnd x high))
  loss : Nat → Nat
  growth : Nat → Nat
  commonReserve : Nat → Nat
  exactLoss : ∀ i ∈ scheduled, ∀ v, y.state.validators.data[i]? = some v →
    loss i = if v.slashed then 0 else effectiveAt x i -
      (if v.pubkey ∈ recentKeys y.state then effectiveAt y i else 0)
  exactGrowth : ∀ i ∈ scheduled, ∀ v, y.state.validators.data[i]? = some v →
    growth i = if v.pubkey ∈ recentKeys y.state \ activeKeys y.state then
      min (effectiveAt y i - effectiveAt x i) (effectiveAt x i) else 0
  exactCommon : ∀ i ∈ scheduled, ∀ v initial,
    x.state.validators.data[i]? = some initial → y.state.validators.data[i]? = some v →
    commonReserve i = if v.slashed ∧ initial.pubkey ∉ recentKeys y.state then effectiveAt x i else 0
  endpointReads : ∀ i ∈ scheduled, ∃ initial v,
    x.state.validators.data[i]? = some initial ∧ y.state.validators.data[i]? = some v ∧
    initial.pubkey = v.pubkey ∧ (v.pubkey ∈ recentKeys y.state → v.slashed = false)
  total : (∑ i ∈ scheduled, effectiveAt x i) ≤ scheduledExitStake x (driftHorizon x high)
private theorem ScheduledAllocation.per_key
    (allocation : ScheduledAllocation x y high) (member : i ∈ allocation.scheduled) :
    allocation.loss i + allocation.growth i + allocation.commonReserve i ≤ effectiveAt x i := by
  obtain ⟨initial, v, foundInitial, found, key, unslashed⟩ := allocation.endpointReads i member
  rw [allocation.exactLoss i member v found, allocation.exactGrowth i member v found,
    allocation.exactCommon i member v initial foundInitial found, key]
  by_cases recent : v.pubkey ∈ recentKeys y.state
  · have clean := unslashed recent
    by_cases active : v.pubkey ∈ activeKeys y.state
    · simp [recent, active, clean]
    · simp [recent, active, clean]
      omega
  · simp only [recent, Finset.mem_sdiff, false_and, ↓reduceIte, not_false_eq_true, and_true]
    cases v.slashed <;> simp
theorem ScheduledAllocation.reservation_bound
    (allocation : ScheduledAllocation x y high) :
    (∑ i ∈ allocation.scheduled, allocation.loss i) +
      (∑ i ∈ allocation.scheduled, allocation.growth i) +
      (∑ i ∈ allocation.scheduled, allocation.commonReserve i) ≤
          scheduledExitStake x (driftHorizon x high) := by
  have bound := Finset.sum_le_sum (fun i member => allocation.per_key member)
  simpa only [Finset.sum_add_distrib] using bound.trans allocation.total
structure NewCohortCuts {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : Nat) (ledger : LedgerCuts tail) where
  cohort : Finset Nat
  supported : Finset Nat
  boundary : Finset Nat
  departed : Finset Nat
  exactUniverse : cohort = (Finset.range x.state.validators.data.size).filter fun i =>
    (x.state.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch x.state) &&
      !v.slashed && decide (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat))
        ∧
      (y.state.validators.data[i]?).any (fun v => !v.slashed)
  exactSupported : supported = cohort.filter fun i =>
    (y.state.validators.data[i]?).any (fun v => v.pubkey ∈ recentKeys y.state)
  exactBoundary : boundary = cohort.filter fun i =>
    (y.state.validators.data[i]?).any (fun v =>
      v.pubkey ∈ recentKeys y.state \ activeKeys y.state)
  exactDeparted : departed = cohort \ supported
  outsideWindowRetained : ∀ i ∈ cohort, ∀ initial,
    x.state.validators.data[i]? = some initial → initial.exitEpoch ≠ FAR_FUTURE_EPOCH →
      i ∈ supported ∧ i ∉ boundary
  charge : Nat → Nat
  actualCharge : ∀ i ∈ boundary ∪ departed, ∃ c,
    (ledger.stops i).charge = some c ∧ charge i = c.amount
structure NewCohortAllocation {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : Nat) (ledger : RoundLedger tail high)
    (owned : Ownership) (tokens : BLSPubkey → Finset TokenOrigin)
    extends NewCohortCuts tail high ledger.toLedgerCuts where
  debit : Nat → Nat
  slack : Nat → Nat
  penalty : Nat → Nat
  partialDebit : Nat → Nat
  exactDebit : ∀ i ∈ cohort, debit i = slack i + penalty i + partialDebit i +
    (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
  slackBudget : (∑ i ∈ cohort, slack i) ≤ startSlack x
  penaltyBudget : (∑ i ∈ cohort, penalty i) ≤
    windowPenalties (config := config) x high (driftHorizon x high + 1)
  stopped : ∀ i ∈ boundary ∪ departed,
    effectiveAt x i ≤ charge i + debit i
  retained : ∀ i ∈ cohort, i ∈ supported → i ∉ boundary →
    effectiveAt x i ≤ effectiveAt y i + debit i
  selected : ∀ i ∈ boundary, ∃ v, y.state.validators.data[i]? = some v ∧
    tokens v.pubkey ⊆ held owned i ∩ owned.endpoint ∧
      (tokens v.pubkey).card = effectiveAt y i - effectiveAt x i
  partialTotal : Nat
  partialBudget : (∑ i ∈ cohort, partialDebit i) ≤ partialTotal
  queueBudget : (∑ i ∈ boundary ∪ departed, charge i) + partialTotal ≤
    departureBudgetAt (config := config) x high + duePartialWithdrawals x (driftHorizon x high)
  debitBudget : (∑ i ∈ cohort, debit i) ≤ partialTotal + startSlack x +
    windowPenalties (config := config) x high (driftHorizon x high + 1) +
        roundingBudget (config := config) x high
theorem NewCohortCuts.exists {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (ledger : LedgerCuts tail) (high : Nat)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1) :
    Nonempty (NewCohortCuts tail high ledger) := by
  let cohort := (Finset.range x.state.validators.data.size).filter fun i =>
    (x.state.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch x.state) &&
      !v.slashed && decide (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat))
        ∧
      (y.state.validators.data[i]?).any (fun v => !v.slashed)
  let supported := cohort.filter fun i =>
    (y.state.validators.data[i]?).any (fun v => v.pubkey ∈ recentKeys y.state)
  let boundary := cohort.filter fun i =>
    (y.state.validators.data[i]?).any (fun v =>
      v.pubkey ∈ recentKeys y.state \ activeKeys y.state)
  let departed := cohort \ supported
  have reads (i : Nat) (member : i ∈ cohort) : ∃ v w,
      x.state.validators.data[i]? = some v ∧ y.state.validators.data[i]? = some w ∧
      isActiveValidator v (getCurrentEpoch x.state) = true ∧ w.slashed = false ∧
      (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat) := by
    have selected := Finset.mem_filter.mp member
    have index := Finset.mem_range.mp selected.1
    let v := x.state.validators.data[i]
    have before : x.state.validators.data[i]? = some v := by simp [v, index]
    obtain ⟨w, after, _⟩ := tail.registryLifecycle.validators i v before
    have first := selected.2.1
    simp only [before, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at first
    exact ⟨v, w, before, after, first.1.1, by simpa [after] using selected.2.2, first.2⟩
  have keyRecent (i : Nat) (w : Validator) (after : y.state.validators.data[i]? = some w)
      (clean : w.slashed = false) (active : isActiveValidator w (getCurrentEpoch y.state) = true) :
      w.pubkey ∈ recentKeys y.state := by
    unfold recentKeys
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _
      ((intervalGain_active_key y.state early unique i w after).mpr active),
      not_slashedAt unique (by simpa using Array.mem_of_getElem? after) clean⟩
  have retained (i : Nat) (member : i ∈ cohort) (v : Validator)
      (before : x.state.validators.data[i]? = some v) (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
      i ∈ supported ∧ i ∉ boundary := by
    obtain ⟨initial, w, first, after, active, clean, window⟩ := reads i member
    have same := Option.some.inj (first.symm.trans before)
    subst initial
    have outside : horizonEnd x high < v.exitEpoch.toNat := window.resolve_left assigned
    obtain ⟨last, lastFound, life⟩ := tail.registryLifecycle.validators i v before
    have same := Option.some.inj (lastFound.symm.trans after)
    subst last
    have finalActive : isActiveValidator w (getCurrentEpoch y.state) = true := by
      cases activeEnd : isActiveValidator w (getCurrentEpoch y.state) with
      | true => rfl
      | false =>
        have cutoff := initial_active_exit_cutoff tail before active after activeEnd
        rw [life.exitEpoch assigned] at cutoff
        have horizon : high + 1 ≤ horizonEnd x high := by unfold horizonEnd driftHorizon; omega
        omega
    have inActive := (intervalGain_active_key y.state early unique i w after).mpr finalActive
    constructor
    · simp only [supported, Finset.mem_filter, after, Option.any_some, decide_eq_true_eq]
      exact ⟨member, keyRecent i w after clean finalActive⟩
    · simp only [boundary, Finset.mem_filter, after, Option.any_some,
        decide_eq_true_eq, Finset.mem_sdiff]
      tauto
  have charged (i : Nat) (member : i ∈ boundary ∪ departed) :
      ∃ c, (ledger.stops i).charge = some c ∧ c.amount = effectiveAt (ledger.stops i).state i := by
    have inCohort : i ∈ cohort := by
      rcases Finset.mem_union.mp member with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_sdiff.mp h).1
    obtain ⟨v, w, before, after, active, clean, _⟩ := reads i inCohort
    have unset : v.exitEpoch = FAR_FUTURE_EPOCH := by
      by_contra assigned
      have kept := retained i inCohort v before assigned
      rcases Finset.mem_union.mp member with h | h
      · exact kept.2 h
      · exact (Finset.mem_sdiff.mp h).2 kept.1
    have inactive : isActiveValidator w (getCurrentEpoch y.state) = false := by
      apply Bool.eq_false_iff.mpr
      intro enabled
      rcases Finset.mem_union.mp member with h | h
      · have selected := (Finset.mem_filter.mp h).2
        simp only [after, Option.any_some, decide_eq_true_eq, Finset.mem_sdiff] at selected
        exact selected.2 ((intervalGain_active_key y.state early unique i w after).mpr enabled)
      · apply (Finset.mem_sdiff.mp h).2
        exact Finset.mem_filter.mpr ⟨inCohort, by
          simpa only [after, Option.any_some, decide_eq_true_eq] using
            keyRecent i w after clean enabled⟩
    have assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro far
      have cutoff := initial_active_exit_cutoff tail before active after inactive
      rw [far] at cutoff
      have epochBound : (getCurrentEpoch y.state).toNat < FAR_FUTURE_EPOCH.toNat := by
        simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
        have slotBound := y.state.slot.toNat_lt
        have quotient : y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
            y.state.slot.toNat / 2 := Nat.div_le_div_left twoSlots (by omega)
        change y.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 - 1
        omega
      omega
    exact (ledger.stops i).charge_of_new_exit before after unset assigned
  refine ⟨⟨cohort, supported, boundary, departed, rfl, rfl, rfl, rfl, retained,
    fun i => effectiveAt (ledger.stops i).state i, ?_⟩⟩
  intro i member
  obtain ⟨c, chosen, amount⟩ := charged i member
  exact ⟨c, chosen, amount.symm⟩
theorem NewCohortCuts.charged_cohort
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : LedgerCuts tail}
    (allocation : NewCohortCuts tail high ledger)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    {i : Nat} (member : i ∈ allocation.boundary ∪ allocation.departed) :
    i < x.state.validators.data.size ∧
      ∃ v w, x.state.validators.data[i]? = some v ∧
        y.state.validators.data[i]? = some w ∧
        isActiveValidator v (getCurrentEpoch x.state) = true ∧
        v.exitEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
        isActiveValidator w (getCurrentEpoch y.state) = false := by
  have cohort : i ∈ allocation.cohort := by
    rcases Finset.mem_union.mp member with boundary | departed
    · rw [allocation.exactBoundary] at boundary
      exact (Finset.mem_filter.mp boundary).1
    · rw [allocation.exactDeparted] at departed
      exact (Finset.mem_sdiff.mp departed).1
  have initial := cohort
  rw [allocation.exactUniverse, Finset.mem_filter] at initial
  have index := Finset.mem_range.mp initial.1
  let v := x.state.validators.data[i]
  have found : x.state.validators.data[i]? = some v :=
    Array.getElem?_eq_some_iff.mpr ⟨index, rfl⟩
  have first := initial.2.1
  simp only [found, Option.any_some, Bool.and_eq_true,
    decide_eq_true_eq] at first
  obtain ⟨w, final, life⟩ := tail.registryLifecycle.validators i v found
  have clean : w.slashed = false := by
    simpa [final] using initial.2.2
  have unset : v.exitEpoch = FAR_FUTURE_EPOCH := by
    by_contra assigned
    have retained := allocation.outsideWindowRetained i cohort v found assigned
    rcases Finset.mem_union.mp member with boundary | departed
    · exact retained.2 boundary
    · rw [allocation.exactDeparted] at departed
      exact (Finset.mem_sdiff.mp departed).2 retained.1
  have inactive : isActiveValidator w (getCurrentEpoch y.state) = false := by
    apply Bool.eq_false_iff.mpr
    intro active
    have keyActive := (intervalGain_active_key y.state early unique i w final).mpr active
    rcases Finset.mem_union.mp member with boundary | departed
    · rw [allocation.exactBoundary] at boundary
      have selected := (Finset.mem_filter.mp boundary).2
      simp only [final, Option.any_some, Finset.mem_sdiff, decide_eq_true_eq] at selected
      exact selected.2 keyActive
    · rw [allocation.exactDeparted] at departed
      apply (Finset.mem_sdiff.mp departed).2
      rw [allocation.exactSupported]
      apply Finset.mem_filter.mpr ⟨cohort, ?_⟩
      simp only [final, Option.any_some, decide_eq_true_eq]
      unfold recentKeys
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ keyActive,
        not_slashedAt unique (by simpa using Array.mem_of_getElem? final) clean⟩
  have assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    obtain ⟨c, chosen, _⟩ := allocation.actualCharge i member
    have actual := (ledger.stops i).selected
    rw [chosen] at actual
    obtain ⟨next, step, rest, _, _, before, after, _, located, _, assigned, _⟩ :=
      actual.2.2.2
    obtain ⟨last, lastFound, kept⟩ := rest.registryLifecycle.validators i after located
    have same := Option.some.inj (lastFound.symm.trans final)
    subst last
    rw [kept.exitEpoch assigned]
    exact assigned
  exact ⟨index, v, w, found, final, first.1.1, unset, assigned, inactive⟩
private theorem NewCohortCuts.stopped_inputs
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : LedgerCuts tail} (cohort : NewCohortCuts tail high ledger)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (member : i ∈ cohort.boundary ∪ cohort.departed) :
    (UInt64.ofNat i).toNat = i ∧
      ∃ c v w u, (ledger.stops i).charge = some c ∧ cohort.charge i = c.amount ∧
        x.state.validators.data[i]? = some v ∧ y.state.validators.data[i]? = some w ∧
        (ledger.stops i).state.state.validators.data[i]? = some u ∧
        v.slashed = false ∧ w.slashed = false ∧ u.slashed = false ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        (getCurrentEpoch (ledger.stops i).state.state).toNat ≤ high + 1 := by
  obtain ⟨inside, v, w, before, after, active, _, _, _⟩ :=
    cohort.charged_cohort unique early member
  have numeric := toNat_toUInt64_of_lt
    (x.state.validators.bound (Nat.lt_of_le_of_lt
      (fork_le_of_chainSteps tail.chainSteps) early)) inside
  have inCohort : i ∈ cohort.cohort := by
    rcases Finset.mem_union.mp member with boundary | departed
    · rw [cohort.exactBoundary] at boundary
      exact (Finset.mem_filter.mp boundary).1
    · rw [cohort.exactDeparted] at departed
      exact (Finset.mem_sdiff.mp departed).1
  rw [cohort.exactUniverse, Finset.mem_filter] at inCohort
  have clean : w.slashed = false := by simpa [after] using inCohort.2.2
  have unslashed : v.slashed = false := by
    have selected := inCohort.2.1
    simp only [before, Option.any_some, Bool.and_eq_true] at selected
    cases flag : v.slashed <;> simp_all
  have assigned := Consensus.Internal.assigned_of_active active
  obtain ⟨c, chosen, amount⟩ := cohort.actualCharge i member
  obtain ⟨u, found, unmarked⟩ := (ledger.stops i).clean_read_of_endpoint v w before after clean
  exact ⟨numeric, c, v, w, u, chosen, amount, before, after, found, unslashed, clean,
    unmarked, assigned, (UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (ledger.stops i).post.chainSteps)).trans endpoint⟩
theorem slashing_quotient_of_electra
    (pre : Run config checks x m) (electra : .pectra ≤ x.fork) :
    minSlashingPenaltyQuotient preset (preElectraEpochs config x high) =
      (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
  have later : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  simp only [preElectraEpochs, notBefore, ↓reduceIte, minSlashingPenaltyQuotient, Nat.lt_irrefl,
    EthLib.Consensus.parameters, later]
/-- Let a step start at Electra or end before it.

Then no balance event of the step is the Electra upgrade crossing. -/
theorem no_crossing_of_regime
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (step : Step config checks m n) (early : n.fork < .glamsterdam)
    (regime : .pectra ≤ m.fork ∨ n.fork < .pectra)
    (replayed : step.balanceEvents = .ok events) :
    ∀ e ∈ events, e.source ≠ .crossing := by
  have holds := (run_justified_separated (shared.append pre) genesis).1
  intro e member crossing
  have facts := step.balanceEvents_sites early holds caps.compounding replayed e member
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, crossingWindow⟩ := facts
  have window := crossingWindow.2 crossing
  rcases regime with later | before
  · exact Nat.not_lt_of_ge later window.1
  · exact Nat.not_lt_of_ge window.2 before
/-- A guarded branch starts at Electra or ends before it. -/
theorem regime_of_supported (shared : Run config checks g x)
    (tail : Run config checks x y) (supported : Supported shared tail high) :
    .pectra ≤ x.fork ∨ y.fork < .pectra :=
  (guarded_fork_regime (shared.append tail) supported.1 high supported.2.2.2.2.2.1
    supported.2.2.2.2.2.2).2
/-- A step inside a branch that starts at Electra or ends before it does the same. -/
private theorem step_regime (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (pre : Run config checks x m) (post : Run config checks n y) :
    .pectra ≤ m.fork ∨ n.fork < .pectra := by
  rcases regime with electra | before
  · exact .inl (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps))
  · exact .inr (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) before)
/-- The guarded slashing quotient is at most the quotient of every state of the branch. -/
private theorem slashing_quotient_le_of_regime (reached : Run config checks g u)
    (genesis : Genesis (config := config) (checks := checks) g)
    (endEpoch : (getCurrentEpoch u.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) (pre : Run config checks x m)
    (regime : .pectra ≤ x.fork ∨ m.fork < .pectra) :
    minSlashingPenaltyQuotient preset (preElectraEpochs config x high) ≤
      (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
  by_cases electra : .pectra ≤ x.fork
  · exact (slashing_quotient_of_electra pre electra).le
  · have positive := (guarded_fork_regime reached genesis high endEpoch guard).1.mpr
      (Nat.lt_of_not_le electra)
    have mBefore : ¬ m.fork ≥ .pectra := Nat.not_le_of_gt (regime.resolve_left electra)
    simp only
        [minSlashingPenaltyQuotient, positive, ↓reduceIte, EthLib.Consensus.parameters, mBefore]
    split_ifs <;> omega
/-- A prefix of a branch that starts at Electra or ends before it does the same. -/
private theorem regime_prefix (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (post : Run config checks m y) : .pectra ≤ x.fork ∨ m.fork < .pectra :=
  regime.imp_right fun before => Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) before
theorem short_window_of_guard
    (guard : aprioriGuardAt config x high)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (rest : Run config checks m y) :
    (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, short, _⟩ := guard
  have order := UInt64.le_iff_toNat_le.mp
    (currentEpoch_le_of_chainSteps rest.chainSteps)
  change high + 2 - (getCurrentEpoch x.state).toNat + 2 <
    preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 at short
  simp only [UInt64.toNat_div, UInt64.reduceToNat]
  omega
private theorem prefix_account_regime
    (shared : Run config checks g x) (pre : Run config checks x outer)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (guard : aprioriGuardAt config x high) (regime : .pectra ≤ x.fork ∨ outer.fork < .pectra)
    (early : outer.fork < .glamsterdam)
    (endpoint : (getCurrentEpoch outer.state).toNat ≤ high + 1)
    (localEndpoint : (getCurrentEpoch outer.state).toNat ≤ localHigh + 1)
    (i : ValidatorIndex) (v u : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : outer.state.validators.data[i.toNat]? = some u)
    (unslashed : v.slashed = false) (clean : u.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (retained : localHigh + 1 < u.exitEpoch.toNat)
    (replayed : pre.balanceEvents high = .ok events) :
    ∃ account, FloorTrace
        (min (effectiveAt x i.toNat) (actualBalanceAt x i.toNat)) 0
        (minSlashingPenaltyQuotient preset (preElectraEpochs config x high))
        ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ account ∧
      account.balance = actualBalanceAt outer i.toNat ∧
      account.debt = (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt outer i.toNat ≤ account.high ∧ account.slashedHigh = none ∧
      max (min (effectiveAt x i.toNat) (actualBalanceAt x i.toNat)) account.high ≤
        (withdrawalMaxEffectiveBalance preset outer.fork u).toNat := by
  have parameters := guard
  obtain ⟨_, _, _, _, _, _, _, positive, _, delay, _⟩ := parameters
  have localReplay : pre.balanceEvents localHigh = .ok events := by
    rw [← balanceEvents_eq_of_endpoint_le pre endpoint localEndpoint]
    exact replayed
  have guards : ∀ {m n : ForkedBeaconState preset} (head : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n outer),
      (head.snoc step).append post = pre → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      w.slashed = false ∧ localHigh + 1 < w.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      minSlashingPenaltyQuotient preset (preElectraEpochs config x high) ≤
        (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ added, step.balanceEvents = .ok added → ∀ e ∈ added, e.source ≠ .crossing := by
    intro m n head step post _split w found
    have unmarked : w.slashed = false := by
      cases flag : w.slashed with
      | false => rfl
      | true =>
        obtain ⟨last, located, marked⟩ := post.slashedPersistence i.toNat w found flag
        have same := Option.some.inj (located.symm.trans final)
        subst last
        simp [clean] at marked
    refine ⟨unmarked, prefix_exit_gt_of_endpoint post w u found final retained,
      short_window_of_guard guard endpoint ((Run.nil.snoc step).append post),
      slashing_quotient_le_of_regime (shared.append pre) genesis endpoint guard head
        (regime_prefix regime ((Run.nil.snoc step).append post)), ?_⟩
    intro added addedOk
    exact no_crossing_of_regime shared head genesis caps step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early)
      (step_regime regime head post) addedOk
  obtain ⟨account, trace, balance, debt, covered, unmarked, cap, _path⟩ :=
    unslashed_floor_run shared pre genesis caps (by omega) early localHigh localEndpoint
      i v initial unslashed activated
      (min (effectiveAt x i.toNat) (actualBalanceAt x i.toNat)) 0
      (minSlashingPenaltyQuotient preset (preElectraEpochs config x high)) (Nat.min_le_left _ _)
          positive
      guards localReplay
  obtain ⟨last, located, capped⟩ := cap
  have same := Option.some.inj (located.symm.trans final)
  subst last
  exact ⟨account, trace, balance, debt, covered, unmarked, capped⟩
private theorem firstUpdate_of_guarded_slot_regime
    {g x outer after y : ForkedBeaconState preset} {tail : Run config checks x y}
    (shared : Run config checks g x) (pre : Run config checks x outer)
    (post : Run config checks after y)
    (ok : advanceSlotAcross config checks outer = .ok after)
    (split : (pre.snoc (.slot ok)).append post = tail)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (guard : aprioriGuardAt config x high) (regime : .pectra ≤ x.fork ∨ after.fork < .pectra)
    (early : after.fork < .glamsterdam)
    (endpoint : (getCurrentEpoch after.state).toNat ≤ high + 1)
    (localEndpoint : (getCurrentEpoch after.state).toNat ≤ localHigh + 1)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (located : outer.state.validators.data[i.toNat]? = some u)
    (final : after.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (retained : localHigh + 1 < w.exitEpoch.toNat)
    {advanced : BeaconState preset outer.fork}
    (advanceOk : advanceSlot config checks outer.state = .ok advanced)
    (decreases : effectiveAt ⟨outer.fork, advanced⟩ i.toNat < effectiveAt outer i.toNat)
    (ordered : ∀ j a b, pre.balancePath[j]? = some a →
      pre.balancePath[j + 1]? = some b → effectiveAt a i.toNat ≤ effectiveAt b i.toNat)
    {prefixEvents : List (BalanceEvent preset)}
    (prefixReplay : pre.balanceEvents high = .ok prefixEvents) :
    Nonempty (FirstUpdate tail high i.toNat) := by
  have edge : Run config checks outer after := Run.nil.snoc (.slot ok)
  have outerEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps edge.chainSteps)
  have outerEarly := Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  have unmarked : u.slashed = false := by
    cases flag : u.slashed with
    | false => rfl
    | true =>
      obtain ⟨last, found, marked⟩ := edge.slashedPersistence i.toNat u located flag
      have same := Option.some.inj (found.symm.trans final)
      subst last
      simp [clean] at marked
  obtain ⟨account, trace, balance, debt, covered, unflagged, capped⟩ :=
    prefix_account_regime shared pre genesis caps guard
      (regime_prefix regime (Run.nil.snoc (.slot ok))) outerEarly
      (outerEpoch.trans endpoint) (outerEpoch.trans localEndpoint) i v u initial located
      unslashed unmarked activated
      (prefix_exit_gt_of_endpoint edge u w located final retained) prefixReplay
  have parameters := guard
  obtain ⟨_, _, _, _, _, _, _, _, _, delay, _⟩ := parameters
  obtain ⟨first⟩ := firstUpdate_of_slot_replay shared pre post ok split genesis caps aligned
    early (by omega) i v u w initial located final unslashed clean advanceOk decreases
    ordered prefixReplay (short_window_of_guard guard endpoint edge) localEndpoint retained
    (fun found replay => no_crossing_of_regime shared pre genesis caps (.slot ok) early
      (step_regime regime pre .nil) replay) trace balance unflagged debt capped covered
  exact ⟨first⟩
private theorem firstUpdate_of_firstDown_regime
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (localEndpoint : (getCurrentEpoch y.state).toNat ≤ localHigh + 1)
    (retained : localHigh + 1 < w.exitEpoch.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (drop : FirstDown tail i.toNat) : Nonempty (FirstUpdate tail high i.toNat) := by
  obtain ⟨genesis, _parameters, caps, aligned, early, endpoint, guard⟩ := supported
  obtain ⟨j, before, after, one, two, decreases, ordered⟩ := drop
  obtain ⟨m, n, pre, step, post, k, split, offset, left, right⟩ :=
    adjacent_decrease_step tail one two decreases
  obtain ⟨u, located, _life⟩ := pre.registryLifecycle.validators i.toNat v initial
  have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  obtain ⟨ok, same, advanced, advanceOk, _zero, atBefore, atAfter⟩ :=
    step_decrease_of_regime step (step_regime regime pre post) nEarly
      (Array.getElem?_eq_some_iff.mp located).1 left right decreases
  subst step
  have lower : effectiveAt ⟨m.fork, advanced⟩ i.toNat < effectiveAt m i.toNat := by
    simpa only [atBefore, atAfter] using decreases
  obtain ⟨nextValidator, found, _⟩ :=
    (Run.nil.snoc (.slot ok)).registryLifecycle.validators i.toNat u located
  have unmarked : nextValidator.slashed = false := by
    cases flag : nextValidator.slashed with
    | false => rfl
    | true =>
      obtain ⟨last, atEnd, marked⟩ := post.slashedPersistence i.toNat nextValidator found flag
      have equal := Option.some.inj (atEnd.symm.trans final)
      subst last
      simp [clean] at marked
  have epochOrder := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have prefixOk : (pre.snoc (.slot ok)).append post = tail := split
  rw [← split] at replayed
  obtain ⟨prefixEvents, prefixReplay, _⟩ :=
    pre.balanceEvents_prefix ((Run.nil.snoc (.slot ok)).append post) high events
      (by simpa only [Run.append_assoc, Run.append] using replayed)
  exact firstUpdate_of_guarded_slot_regime shared pre post ok prefixOk genesis caps aligned guard
    (regime_prefix regime post)
    nEarly (epochOrder.trans endpoint) (epochOrder.trans localEndpoint) i v u nextValidator
    initial located found unslashed unmarked activated
    (prefix_exit_gt_of_endpoint post nextValidator w found final retained) advanceOk lower
    (noEarlier_of_localized_decrease tail pre (.slot ok) post split offset ordered) prefixReplay
private theorem Stop.firstUpdate_of_firstDown_regime
    {i : ValidatorIndex} {tail : Run config checks x y} (stop : Stop tail i.toNat)
    (chosen : stop.charge = some c)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (v u : Validator) (initial : x.state.validators.data[i.toNat]? = some v)
    (final : stop.state.state.validators.data[i.toNat]? = some u)
    (unslashed : v.slashed = false) (clean : u.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (replayed : stop.pre.balanceEvents high = .ok events)
    (drop : FirstDown stop.pre i.toNat) : Nonempty (FirstUpdate stop.pre high i.toNat) := by
  obtain ⟨genesis, parameters, caps, aligned, early, endpoint, guard⟩ := supported
  have stopEpoch := (UInt64.le_iff_toNat_le.mp
    (currentEpoch_le_of_chainSteps stop.post.chainSteps)).trans endpoint
  have stopEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps stop.post.chainSteps) early
  have localSupported : Supported shared stop.pre high :=
    ⟨genesis, parameters, caps, aligned, stopEarly, stopEpoch, guard⟩
  exact Internal.firstUpdate_of_firstDown_regime shared stop.pre localSupported
    (regime_prefix regime stop.post) i v u
    initial final unslashed clean activated
    (localHigh := (getCurrentEpoch stop.state.state).toNat) (by omega)
    (stop.selected_prefix_exit_gt chosen Run.nil u final
      (getCurrentEpoch_succ_lt_farFuture twoSlots stop.state.state)) replayed drop
private theorem effectiveAt_eq_of_epoch_zero
    (tail : Run config checks x y)
    (zero : (getCurrentEpoch y.state).toNat = 0)
    (inside : i < x.state.validators.data.size) : effectiveAt y i = effectiveAt x i := by
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have same : getCurrentEpoch y.state = getCurrentEpoch x.state :=
    UInt64.toNat_inj.mp (by omega)
  exact run_same_epoch_effective tail same i inside
private theorem firstUpdate_of_retained_firstDown_regime
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (active : (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (drop : FirstDown tail i.toNat) : Nonempty (FirstUpdate tail high i.toNat) := by
  by_cases zero : (getCurrentEpoch y.state).toNat = 0
  · obtain ⟨j, before, after, one, two, decreases, _ordered⟩ := drop
    obtain ⟨m, n, pre, step, post, k, _split, _offset, left, right⟩ :=
      adjacent_decrease_step tail one two decreases
    have early := supported.2.2.2.2.1
    have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
    obtain ⟨u, located, _life⟩ := pre.registryLifecycle.validators i.toNat v initial
    obtain ⟨ok, same, advanced, advanceOk, _zeroIndex, atBefore, atAfter⟩ :=
      step_decrease_of_regime step (step_regime regime pre post)
        nEarly (Array.getElem?_eq_some_iff.mp located).1 left right decreases
    subst step
    have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    have nZero : (getCurrentEpoch n.state).toNat = 0 := by omega
    have equal := run_same_epoch_effective (Run.nil.snoc (.slot ok))
      (UInt64.toNat_inj.mp (by
        have previous := UInt64.le_iff_toNat_le.mp
          (currentEpoch_le_of_chainSteps (Run.nil.snoc (.slot ok)).chainSteps)
        omega)) i.toNat (Array.getElem?_eq_some_iff.mp located).1
    obtain ⟨actual, actualOk, upgrades⟩ := bind_ok_iff.mp ok
    have identical := Except.ok.inj (actualOk.symm.trans advanceOk)
    subst actual
    have frame : effectiveAt n i.toNat = effectiveAt ⟨m.fork, advanced⟩ i.toNat := by
      rcases step_regime regime pre post with later | preElectra
      · have kept := processUpgrades_retained_data (s := ⟨m.fork, advanced⟩)
          later nEarly upgrades
          (Nat.le_trans later (processUpgrades_fork_le (forked := ⟨m.fork, advanced⟩) upgrades))
        simp only [effectiveAt, kept]
      · have kept := upgrades_validators upgrades preElectra
        simp only [effectiveAt, kept]
    have lower : effectiveAt ⟨m.fork, advanced⟩ i.toNat < effectiveAt m i.toNat := by
      simpa only [atBefore, atAfter] using decreases
    omega
  · have positive : 0 < (getCurrentEpoch y.state).toNat := by omega
    exact firstUpdate_of_firstDown_regime shared tail supported regime i v w
      initial final unslashed clean activated
      (localHigh := (getCurrentEpoch y.state).toNat - 1) (by omega) (by omega) replayed drop
private theorem retained_effective_loss_positive_regime
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (positiveEpoch : 0 < (getCurrentEpoch y.state).toNat)
    (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (active : (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (replayed : tail.balanceEvents high = .ok events) :
    effectiveAt x i.toNat ≤ effectiveAt y i.toNat +
      (effectiveAt x i.toNat - actualBalanceAt x i.toNat) +
      ((events.map (floorPenaltyDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum) +
      (if FirstDown tail i.toNat then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) := by
  obtain ⟨genesis, _parameters, caps, _aligned, early, endpoint, guard⟩ := supported
  obtain ⟨localReplay, exits⟩ :=
      retained_local_replay tail positiveEpoch endpoint replayed w final active
  have positive := guard
  obtain ⟨increment, _, _, _, _, _, _, quotient, _, delay, _⟩ := positive
  have guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ u,
      n.state.validators.data[i.toNat]? = some u →
      u.slashed = false ∧ (getCurrentEpoch y.state).toNat - 1 + 1 < u.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      minSlashingPenaltyQuotient preset (preElectraEpochs config x high) ≤
        (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ added, step.balanceEvents = .ok added → ∀ e ∈ added, e.source ≠ .crossing := by
    intro m n pre step post _split u found
    have unmarked : u.slashed = false := by
      cases flag : u.slashed with
      | false => rfl
      | true =>
        obtain ⟨last, located, marked⟩ := post.slashedPersistence i.toNat u found flag
        have same := Option.some.inj (located.symm.trans final)
        subst last
        simp [clean] at marked
    refine ⟨unmarked, exits post u found,
      short_window_of_guard guard endpoint ((Run.nil.snoc step).append post),
      slashing_quotient_le_of_regime (shared.append tail) genesis endpoint guard pre
        (regime_prefix regime ((Run.nil.snoc step).append post)), ?_⟩
    intro added addedOk
    exact no_crossing_of_regime shared pre genesis caps step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early)
      (step_regime regime pre post) addedOk
  obtain ⟨last, _, _, debt, _, _, _, path⟩ := unslashed_floor_run shared tail genesis caps
    (by omega) early ((getCurrentEpoch y.state).toNat - 1) (by omega)
    i v initial unslashed activated (min (effectiveAt x i.toNat) (actualBalanceAt x i.toNat))
    0 (minSlashingPenaltyQuotient preset (preElectraEpochs config x high)) (Nat.min_le_left _ _)
        quotient
    guards localReplay
  apply effective_loss_le_of_unslashed_traces shared tail genesis caps increment early
    v initial activated _ 0 (minSlashingPenaltyQuotient preset (preElectraEpochs config x high))
  simpa only [debt] using path
private theorem retained_effective_loss_regime
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (active : (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (replayed : tail.balanceEvents high = .ok events) :
    effectiveAt x i.toNat ≤ effectiveAt y i.toNat +
      (effectiveAt x i.toNat - actualBalanceAt x i.toNat) +
      ((events.map (floorPenaltyDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum) +
      (if FirstDown tail i.toNat then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) := by
  by_cases zero : (getCurrentEpoch y.state).toNat = 0
  · have early := supported.2.2.2.2.1
    have inside : i.toNat < x.state.validators.data.size :=
        (Array.getElem?_eq_some_iff.mp initial).1
    have same := effectiveAt_eq_of_epoch_zero tail zero inside
    omega
  · exact retained_effective_loss_positive_regime shared tail supported regime (by omega)
      i v w initial final unslashed clean activated active replayed
private theorem replay_and_drop_of_heq
    {a b : ForkedBeaconState preset} (one : Run config checks x a)
    (two : Run config checks x b) (endpoint : a = b) (same : HEq one two) :
    one.balanceEvents high = two.balanceEvents high ∧ (FirstDown one i ↔ FirstDown two i) := by
  subst b
  have equal := eq_of_heq same
  subst two
  exact ⟨rfl, Iff.rfl⟩
private theorem NewCohortCuts.stopped_replay
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : LedgerCuts tail} (cohort : NewCohortCuts tail high ledger)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (member : i ∈ cohort.boundary ∪ cohort.departed) :
    (ledger.headRun i).balanceEvents high = (ledger.stops i).pre.balanceEvents high ∧
      (FirstDown (ledger.headRun i) i ↔ FirstDown (ledger.stops i).pre i) := by
  obtain ⟨_, v, w, _before, after, _active, _unset, _assigned, inactive⟩ :=
    cohort.charged_cohort unique early member
  have absent : ¬ (y.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch y.state)) := by
    simpa only [after, Option.any_some, inactive] using Bool.false_ne_true
  exact replay_and_drop_of_heq (ledger.headRun i) (ledger.stops i).pre
    (ledger.stoppedCut i absent).1 (ledger.stoppedCut i absent).2
private theorem NewCohortCuts.retained_replay
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : LedgerCuts tail} (cohort : NewCohortCuts tail high ledger)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (member : i ∈ cohort.cohort) (supported : i ∈ cohort.supported)
    (notBoundary : i ∉ cohort.boundary) :
    (∃ w, y.state.validators.data[i]? = some w ∧ w.slashed = false ∧
      isActiveValidator w (getCurrentEpoch y.state) = true ∧
      (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat) ∧
    (ledger.headRun i).balanceEvents high = tail.balanceEvents high ∧
      (FirstDown (ledger.headRun i) i ↔ FirstDown tail i) := by
  have endpoint := member
  rw [cohort.exactUniverse, Finset.mem_filter] at endpoint
  obtain ⟨w, found⟩ : ∃ w, y.state.validators.data[i]? = some w := by
    cases read : y.state.validators.data[i]? with
    | none => simp [read] at endpoint
    | some w => exact ⟨w, rfl⟩
  have clean : w.slashed = false := by simpa [found] using endpoint.2.2
  have recent := supported
  rw [cohort.exactSupported, Finset.mem_filter] at recent
  have keyRecent : w.pubkey ∈ recentKeys y.state := by
    simpa only [found, Option.any_some, decide_eq_true_eq] using recent.2
  have activeKey : w.pubkey ∈ activeKeys y.state := by
    by_contra absent
    apply notBoundary
    rw [cohort.exactBoundary]
    exact Finset.mem_filter.mpr ⟨member, by simp [found, keyRecent, absent]⟩
  have active := (intervalGain_active_key y.state early unique i w found).mp activeKey
  have cutoff : (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat := by
    have enabled := active
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at enabled
    exact UInt64.lt_iff_toNat_lt.mp enabled.2
  have cut := ledger.retainedCut i (by simpa [found] using active)
  exact ⟨⟨w, found, clean, active, cutoff⟩,
    replay_and_drop_of_heq (ledger.headRun i) tail cut.1 cut.2⟩
private theorem Stop.source_firstUpdate_regime
    {i : ValidatorIndex} {tail : Run config checks x y} (stop : Stop tail i.toNat)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (v u : Validator) (initial : x.state.validators.data[i.toNat]? = some v)
    (final : stop.state.state.validators.data[i.toNat]? = some u)
    (unslashed : v.slashed = false) (clean : u.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (unset : v.exitEpoch = FAR_FUTURE_EPOCH)
    (replayed : stop.pre.balanceEvents high = .ok events)
    (drop : FirstDown stop.pre i.toNat) : Nonempty (FirstUpdate stop.pre high i.toNat) := by
  cases chosen : stop.charge with
  | some c =>
    exact stop.firstUpdate_of_firstDown_regime chosen shared supported regime twoSlots
      v u initial final unslashed clean activated replayed drop
  | none =>
    have selected := stop.selected
    rw [chosen] at selected
    have same := selected.1
    change stop.state = y at same
    have exit : u.exitEpoch = FAR_FUTURE_EPOCH := by
      by_contra assigned
      obtain ⟨c, present, index, _⟩ := tail.departure_charge_of_assigned i.toNat v u
        initial ((congrArg (fun s : ForkedBeaconState preset =>
          s.state.validators.data[i.toNat]?) same).symm.trans final) unset assigned
      exact selected.2 c present index
    have endpoint := (UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps stop.post.chainSteps)).trans supported.2.2.2.2.2.1
    have early := Nat.lt_of_le_of_lt (fork_le_of_chainSteps stop.post.chainSteps)
      supported.2.2.2.2.1
    have localSupported : Supported shared stop.pre high :=
      ⟨supported.1, supported.2.1, supported.2.2.1, supported.2.2.2.1,
        early, endpoint, supported.2.2.2.2.2.2⟩
    apply firstUpdate_of_retained_firstDown_regime shared stop.pre localSupported
      (regime_prefix regime stop.post) i v u
      initial final unslashed clean activated _ replayed drop
    rw [exit]
    exact Nat.lt_trans (Nat.lt_succ_self _)
      (getCurrentEpoch_succ_lt_farFuture twoSlots stop.state.state)
private theorem Stop.source_firstUpdate_of_reference_regime
    {tail : Run config checks x y} (stop : Stop tail i)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (inside : i < x.state.validators.data.size) (reference : NewReference x i)
    (clean : ((stop.state.state.validators.data[i]?).map (·.slashed)).getD true = false)
    (replayed : stop.pre.balanceEvents high = .ok events)
    (drop : FirstDown stop.pre i) : Nonempty (FirstUpdate stop.pre high i) := by
  obtain ⟨v, initial⟩ : ∃ v, x.state.validators.data[i]? = some v :=
    ⟨x.state.validators.data[i], Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
  obtain ⟨u, final, _life⟩ := stop.pre.registryLifecycle.validators i v initial
  unfold NewReference at reference
  simp only [initial, Option.any_some, Bool.and_eq_true, beq_iff_eq] at reference
  have unslashed : v.slashed = false := by
    cases flag : v.slashed <;> simp_all
  have activated := Consensus.Internal.assigned_of_active reference.1.1
  have cleanU : u.slashed =
      false := by simpa only [final, Option.map_some, Option.getD_some] using clean
  have early := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) supported.2.2.2.2.1
  have numeric : (UInt64.ofNat i).toNat = i :=
    toNat_toUInt64_of_lt (x.state.validators.bound early) inside
  generalize indexEq : UInt64.ofNat i = index at *
  subst i
  exact stop.source_firstUpdate_regime (i := index) shared supported regime twoSlots v u
    initial final unslashed cleanU activated reference.2 replayed drop
private theorem source_falling_resources_regime
    {tail : Run config checks x y} (stops : (i : Nat) → Stop tail i)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events) :
    let falling := (Finset.range x.state.validators.data.size).filter (fun i =>
      NewReference x i ∧
      ((stops i).state.state.validators.data[i]?.map (·.slashed)).getD true = false ∧
      FirstDown (stops i).pre i)
    ∃ (first : ∀ i, i ∈ falling → FirstUpdate (stops i).pre high i) (a p : Nat → Nat),
      (∀ i (member : i ∈ falling), a i = (effectiveAt x i - actualBalanceAt x i) +
        (((first i member).prefixEvents ++ (first i member).events).map (floorPenaltyDebit i)).sum)
          ∧
      (∀ i (member : i ∈ falling), p i =
        (((first i member).prefixEvents ++ (first i member).events).map
          (floorPartialDebit (UInt64.ofNat i))).sum) ∧
      (∀ i ∈ falling, preset.downwardBand < a i + p i) ∧
      (∀ i (member : i ∈ falling), ((first i member).prefixEvents ++ (first i member).events)
        <+: events) := by
  dsimp only
  let falling := (Finset.range x.state.validators.data.size).filter (fun i =>
    NewReference x i ∧
    ((stops i).state.state.validators.data[i]?.map (·.slashed)).getD true = false ∧
    FirstDown (stops i).pre i)
  have prefixes (i : Nat) : ∃ part, (stops i).pre.balanceEvents high = .ok part ∧
      part <+: events := by
    have replay := replayed
    rw [← (stops i).split] at replay
    exact (stops i).pre.balanceEvents_prefix (stops i).post high events replay
  choose parts reads included using prefixes
  have existsFirst (i : Nat) (member : i ∈ falling) :
      Nonempty (FirstUpdate (stops i).pre high i) := by
    obtain ⟨inside, reference, clean, drop⟩ := Finset.mem_filter.mp member
    exact (stops i).source_firstUpdate_of_reference_regime shared supported regime twoSlots
      (Finset.mem_range.mp inside) reference clean (reads i) drop
  let first := fun i member => Classical.choice (existsFirst i member)
  let a := fun i => if member : i ∈ falling then
    (effectiveAt x i - actualBalanceAt x i) +
      (((first i member).prefixEvents ++ (first i member).events).map (floorPenaltyDebit i)).sum
    else 0
  let p := fun i => if member : i ∈ falling then
    (((first i member).prefixEvents ++ (first i member).events).map
      (floorPartialDebit (UInt64.ofNat i))).sum else 0
  refine ⟨first, a, p, ?_, ?_, ?_, ?_⟩
  · intro i member
    simp only [a, falling, dite_eq_left member]
  · intro i member
    simp only [p, falling, dite_eq_left member]
  · intro i member
    simpa only [a, p, falling, dite_eq_left member] using
      (first i member).gap.trans_le (first i member).resources
  · intro i member
    exact ((first i member).events_prefix
      ((UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
        (stops i).post.chainSteps)).trans supported.2.2.2.2.2.1) (reads i)).trans (included i)
private theorem source_resource_budgets
    {tail : Run config checks x y} (shared : Run config checks g x)
    (supported : Supported shared tail high) (replayed : tail.balanceEvents high = .ok events)
    (carrier : Finset Nat) (parts : Nat → List (BalanceEvent preset)) (a p : Nat → Nat)
    (indices : ∀ i ∈ carrier, i < x.state.validators.data.size)
    (active : ∀ i ∈ carrier, ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false)
    (included : ∀ i ∈ carrier, parts i <+: events)
    (exactA : ∀ i ∈ carrier, a i = (effectiveAt x i - actualBalanceAt x i) +
      ((parts i).map (floorPenaltyDebit i)).sum)
    (exactP : ∀ i ∈ carrier, p i = ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum)
    (penaltyBound : (events.map fun e =>
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (driftHorizon x high + 1))
    (partialBound : (events.map fun e =>
      ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high) :
    (∑ i ∈ carrier, a i) ≤ startSlack x +
        windowPenalties (config := config) x high (driftHorizon x high + 1) ∧
      (∑ i ∈ carrier, p i) ≤ withdrawalBudget (config := config) x high ∧ carrier.card ≤
          referenceCount x := by
  have early := supported.2.2.2.2.1
  have startEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have activeOnly (i : Nat) (member : i ∈ carrier) : ∃ v,
      x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true := by
    obtain ⟨v, found, enabled, _⟩ := active i member
    exact ⟨v, found, enabled⟩
  have slack := initial_active_slack_le carrier startEarly activeOnly
  have prefixPenalty := prefix_resource_sum_le carrier parts events
    (fun i => floorPenaltyDebit i) included
  have allPenalty : (events.map fun e => ∑ i ∈ carrier, floorPenaltyDebit i e).sum ≤
      (events.map fun e => ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map
        fun i => if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else floorPenaltyDebit i.toNat e).sum).sum := by
    clear included prefixPenalty replayed penaltyBound partialBound
    induction events with
    | nil => simp
    | cons e events ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (initial_unslashed_debit_le carrier startEarly active
        (fun i => floorPenaltyDebit i e)) ih
  refine ⟨?_, ?_, initial_active_carrier_card_le carrier
    (shared.pubkeysDistinct supported.1) startEarly activeOnly⟩
  · calc
      (∑ i ∈ carrier, a i) = ∑ i ∈ carrier,
          ((effectiveAt x i - actualBalanceAt x i) + ((parts i).map (floorPenaltyDebit i)).sum) :=
        Finset.sum_congr rfl exactA
      _ = (∑ i ∈ carrier, (effectiveAt x i - actualBalanceAt x i)) +
          ∑ i ∈ carrier, ((parts i).map (floorPenaltyDebit i)).sum := Finset.sum_add_distrib
      _ ≤ _ := Nat.add_le_add slack (prefixPenalty.trans (allPenalty.trans penaltyBound))
  · have partials := stopped_partial_occurrences shared supported.1 tail early
      supported.2.2.2.2.2.1 replayed carrier parts indices included
    rw [Finset.sum_congr rfl exactP]
    exact partials.trans partialBound
private theorem source_rounding_of_resources
    {tail : Run config checks x y} (shared : Run config checks g x)
    (supported : Supported shared tail high) (replayed : tail.balanceEvents high = .ok events)
    (carrier : Finset Nat) (parts : Nat → List (BalanceEvent preset)) (a p : Nat → Nat)
    (indices : ∀ i ∈ carrier, i < x.state.validators.data.size)
    (active : ∀ i ∈ carrier, ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false)
    (included : ∀ i ∈ carrier, parts i <+: events)
    (exactA : ∀ i ∈ carrier, a i = (effectiveAt x i - actualBalanceAt x i) +
      ((parts i).map (floorPenaltyDebit i)).sum)
    (exactP : ∀ i ∈ carrier, p i = ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum)
    (gap : ∀ i ∈ carrier, preset.downwardBand < a i + p i)
    (penaltyBound : (events.map fun e =>
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (driftHorizon x high + 1))
    (partialBound : (events.map fun e =>
      ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high) :
    (∑ i ∈ carrier, a i) ≤ startSlack x +
        windowPenalties (config := config) x high (driftHorizon x high + 1) ∧
      (∑ i ∈ carrier, p i) ≤ withdrawalBudget (config := config) x high ∧
      carrier.card ≤
          finalKeyCount preset (referenceStake x) (referenceCount x)
          (stakeCeilingAt config x high (driftHorizon x high + 1)) ∧
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * carrier.card ≤
          roundingBudget (config := config) x high := by
  obtain ⟨aBound, pBound, count⟩ := source_resource_budgets shared supported replayed
    carrier parts a p indices active included exactA exactP penaltyBound partialBound
  have guard := supported.2.2.2.2.2.2
  have positive : 0 < preset.downwardBand := by
    unfold aprioriGuardAt aprioriGuard at guard
    exact guard.2.2.2.2.2.1
  have resource := carrier_resource_count_le carrier a p _ _ _ positive gap aBound pBound
  have finalCountBound : carrier.card ≤
      finalKeyCount preset (referenceStake x) (referenceCount x)
          (stakeCeilingAt config x high (driftHorizon x high + 1)) :=
    count.trans (by unfold finalKeyCount; exact Nat.le_add_right _ _)
  refine ⟨aBound, pBound, finalCountBound, ?_⟩
  apply Nat.mul_le_mul_left
  exact le_min finalCountBound (le_min resource (count.trans (Nat.le_add_left _ _)))
private theorem source_numeric_ledger_regime
    {tail : Run config checks x y} (stops : (i : Nat) → Stop tail i)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (penaltyBound : (events.map fun e =>
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (driftHorizon x high + 1))
    (partialBound : (events.map fun e =>
      ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high) :
    let falling := (Finset.range x.state.validators.data.size).filter (fun i =>
      NewReference x i ∧
      ((stops i).state.state.validators.data[i]?.map (·.slashed)).getD true = false ∧
      FirstDown (stops i).pre i)
    ∃ (first : ∀ i, i ∈ falling → FirstUpdate (stops i).pre high i) (a p : Nat → Nat),
      (∀ i (member : i ∈ falling), a i = (effectiveAt x i - actualBalanceAt x i) +
        (((first i member).prefixEvents ++ (first i member).events).map (floorPenaltyDebit i)).sum)
          ∧
      (∀ i (member : i ∈ falling), p i =
        (((first i member).prefixEvents ++ (first i member).events).map
          (floorPartialDebit (UInt64.ofNat i))).sum) ∧
      (∑ i ∈ falling, a i) ≤ startSlack x +
          windowPenalties (config := config) x high (driftHorizon x high + 1) ∧
      (∑ i ∈ falling, p i) ≤ withdrawalBudget (config := config) x high ∧
      falling.card ≤
          finalKeyCount preset (referenceStake x) (referenceCount x)
          (stakeCeilingAt config x high (driftHorizon x high + 1)) ∧
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * falling.card ≤
          roundingBudget (config := config) x high := by
  dsimp only
  let falling := (Finset.range x.state.validators.data.size).filter (fun i =>
    NewReference x i ∧
    ((stops i).state.state.validators.data[i]?.map (·.slashed)).getD true = false ∧
    FirstDown (stops i).pre i)
  obtain ⟨first, a, p, exactA, exactP, gap, included⟩ :=
    source_falling_resources_regime stops shared supported regime twoSlots replayed
  let parts := fun i => if member : i ∈ falling then
    (first i member).prefixEvents ++ (first i member).events else []
  have bounds := source_rounding_of_resources shared supported replayed falling parts a p
    (fun i member => Finset.mem_range.mp (Finset.mem_filter.mp member).1)
    (fun i member => by
      have selected := (Finset.mem_filter.mp member).2.1
      unfold NewReference at selected
      cases found : x.state.validators.data[i]? with
      | none => simp [found] at selected
      | some v =>
        refine ⟨v, rfl, ?_⟩
        simp only [found, Option.any_some, Bool.and_eq_true] at selected
        exact ⟨selected.1.1, by cases clean : v.slashed <;> simp_all⟩)
    (fun i member => by simpa only [parts, dite_eq_left member] using included i member)
    (fun i member => by simpa only [parts, dite_eq_left member] using exactA i member)
    (fun i member => by simpa only [parts, dite_eq_left member] using exactP i member)
    gap penaltyBound partialBound
  exact ⟨first, a, p, exactA, exactP, bounds⟩
private theorem firstUpdate_of_heq
    {a b : ForkedBeaconState preset} (one : Run config checks x a)
    (two : Run config checks x b) (endpoint : a = b) (same : HEq one two)
    (first : Nonempty (FirstUpdate two high i)) : Nonempty (FirstUpdate one high i) := by
  subst b
  have equal := eq_of_heq same
  subst two
  exact first
private theorem LedgerCuts.firstUpdate_regime
    {tail : Run config checks x y} (ledger : LedgerCuts tail)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (inside : i < x.state.validators.data.size)
    (reference : (x.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
      decide (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat)))
    (clean : ((ledger.cut i).state.validators.data[i]?.map (·.slashed)).getD true = false)
    (replayed : (ledger.headRun i).balanceEvents high = .ok events)
    (drop : FirstDown (ledger.headRun i) i) :
    Nonempty (FirstUpdate (ledger.headRun i) high i) := by
  obtain ⟨v, initial⟩ : ∃ v, x.state.validators.data[i]? = some v :=
    ⟨x.state.validators.data[i], Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
  obtain ⟨w, final, life⟩ := tail.registryLifecycle.validators i v initial
  simp only [initial, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at reference
  have unslashed : v.slashed = false := by cases flag : v.slashed <;> simp_all
  by_cases enabled : (y.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch y.state))
  · have cut := (ledger.retainedCut i enabled).1
    obtain ⟨u, located, _⟩ := (ledger.headRun i).registryLifecycle.validators i v initial
    have sameRead : (ledger.cut i).state.validators.data[i]? = some w := by
      rw [cut]
      exact final
    have identical := Option.some.inj (located.symm.trans sameRead)
    subst u
    have cleanW : w.slashed =
        false := by simpa only [sameRead, Option.map_some, Option.getD_some] using clean
    have activeW : isActiveValidator w (getCurrentEpoch y.state) = true := by
      simpa only [final, Option.any_some] using enabled
    have cutoff : (getCurrentEpoch (ledger.cut i).state).toNat < w.exitEpoch.toNat := by
      rw [cut]
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeW
      exact UInt64.lt_iff_toNat_lt.mp activeW.2
    have activated := Consensus.Internal.assigned_of_active reference.1.1
    have localSupported : Supported shared (ledger.headRun i) high :=
      ⟨supported.1, supported.2.1, supported.2.2.1, supported.2.2.2.1,
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps (ledger.suffix i).chainSteps) supported.2.2.2.2.1,
        (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
          (ledger.suffix i).chainSteps)).trans supported.2.2.2.2.2.1, supported.2.2.2.2.2.2⟩
    have numeric : (UInt64.ofNat i).toNat = i := toNat_toUInt64_of_lt
      (x.state.validators.bound (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps)
        supported.2.2.2.2.1)) inside
    generalize indexEq : UInt64.ofNat i = index at *
    subst i
    exact firstUpdate_of_retained_firstDown_regime shared (ledger.headRun index.toNat)
      localSupported (regime_prefix regime (ledger.suffix index.toNat)) index v w initial located
      unslashed cleanW activated cutoff replayed drop
  · have inactive : isActiveValidator w (getCurrentEpoch y.state) = false := by
      cases active : isActiveValidator w (getCurrentEpoch y.state) <;> simp_all
    have unset : v.exitEpoch = FAR_FUTURE_EPOCH := by
      by_contra assigned
      have outside := reference.2.resolve_left assigned
      have cutoff := initial_active_exit_cutoff tail initial reference.1.1 final inactive
      rw [life.exitEpoch assigned] at cutoff
      have horizon : high + 1 ≤ horizonEnd x high := by unfold horizonEnd driftHorizon; omega
      have endpoint := supported.2.2.2.2.2.1
      omega
    have source : NewReference x i := by
      unfold NewReference
      simp only [initial, Option.any_some, Bool.and_eq_true, beq_iff_eq]
      exact ⟨reference.1, unset⟩
    have cut := ledger.stoppedCut i enabled
    have reads := replay_and_drop_of_heq (high := high) (i := i)
      (ledger.headRun i) (ledger.stops i).pre cut.1 cut.2
    have stopClean : ((ledger.stops i).state.state.validators.data[i]?.map (·.slashed)).getD true =
        false := by
      rw [← cut.1]
      exact clean
    exact firstUpdate_of_heq _ _ cut.1 cut.2
      ((ledger.stops i).source_firstUpdate_of_reference_regime shared supported regime twoSlots
        inside source stopClean (reads.1 ▸ replayed) (reads.2.mp drop))
private theorem LedgerCuts.falling_resources_regime
    {tail : Run config checks x y} (ledger : LedgerCuts tail)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events) :
    let falling := (Finset.range x.state.validators.data.size).filter (fun i =>
      (x.state.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch x.state) &&
        !v.slashed && decide
            (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat)) ∧
      ((ledger.cut i).state.validators.data[i]?.map (·.slashed)).getD true = false ∧
      FirstDown (ledger.headRun i) i)
    ∃ (first : ∀ i, i ∈ falling → FirstUpdate (ledger.headRun i) high i) (a p : Nat → Nat),
      (∀ i (member : i ∈ falling), a i = (effectiveAt x i - actualBalanceAt x i) +
        (((first i member).prefixEvents ++ (first i member).events).map (floorPenaltyDebit i)).sum)
          ∧
      (∀ i (member : i ∈ falling), p i =
        (((first i member).prefixEvents ++ (first i member).events).map
          (floorPartialDebit (UInt64.ofNat i))).sum) ∧
      (∀ i ∈ falling, preset.downwardBand < a i + p i) ∧
      (∀ i (member : i ∈ falling), ((first i member).prefixEvents ++ (first i member).events)
        <+: events) := by
  dsimp only
  let falling := (Finset.range x.state.validators.data.size).filter (fun i =>
    (x.state.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch x.state) &&
      !v.slashed && decide (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat))
        ∧
    ((ledger.cut i).state.validators.data[i]?.map (·.slashed)).getD true = false ∧
    FirstDown (ledger.headRun i) i)
  have prefixes (i : Nat) : ∃ part, (ledger.headRun i).balanceEvents high = .ok part ∧
      part <+: events := by
    have replay := replayed
    rw [← ledger.split i] at replay
    exact (ledger.headRun i).balanceEvents_prefix (ledger.suffix i) high events replay
  choose parts reads included using prefixes
  have existsFirst (i : Nat) (member : i ∈ falling) :
      Nonempty (FirstUpdate (ledger.headRun i) high i) := by
    obtain ⟨inside, reference, clean, drop⟩ := Finset.mem_filter.mp member
    exact ledger.firstUpdate_regime shared supported regime twoSlots
      (Finset.mem_range.mp inside) reference clean (reads i) drop
  let first := fun i member => Classical.choice (existsFirst i member)
  let a := fun i => if member : i ∈ falling then
    (effectiveAt x i - actualBalanceAt x i) +
      (((first i member).prefixEvents ++ (first i member).events).map (floorPenaltyDebit i)).sum
    else 0
  let p := fun i => if member : i ∈ falling then
    (((first i member).prefixEvents ++ (first i member).events).map
      (floorPartialDebit (UInt64.ofNat i))).sum else 0
  refine ⟨first, a, p, ?_, ?_, ?_, ?_⟩
  · intro i member
    simp only [a, falling, dite_eq_left member]
  · intro i member
    simp only [p, falling, dite_eq_left member]
  · intro i member
    simpa only [a, p, falling, dite_eq_left member] using
      (first i member).gap.trans_le (first i member).resources
  · intro i member
    exact ((first i member).events_prefix
      ((UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
        (ledger.suffix i).chainSteps)).trans supported.2.2.2.2.2.1) (reads i)).trans (included i)
theorem LedgerCuts.roundLedger_regime
    {tail : Run config checks x y} (ledger : LedgerCuts tail)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (regime : .pectra ≤ x.fork ∨ y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (penaltyBound : (events.map fun e =>
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (driftHorizon x high + 1))
    (partialBound : (events.map fun e =>
      ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high) :
    ∃ result : RoundLedger tail high, result.toLedgerCuts = ledger := by
  let falling := (Finset.range x.state.validators.data.size).filter (fun i =>
    (x.state.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch x.state) &&
      !v.slashed && decide (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat))
        ∧
    ((ledger.cut i).state.validators.data[i]?.map (·.slashed)).getD true = false ∧
    FirstDown (ledger.headRun i) i)
  obtain ⟨first, a, p, exactA, exactP, gap, included⟩ :=
    ledger.falling_resources_regime shared supported regime twoSlots replayed
  let parts := fun i => if member : i ∈ falling then
    (first i member).prefixEvents ++ (first i member).events else []
  have bounds := source_rounding_of_resources shared supported replayed falling parts a p
    (fun i member => Finset.mem_range.mp (Finset.mem_filter.mp member).1)
    (fun i member => by
      have selected := (Finset.mem_filter.mp member).2.1
      cases found : x.state.validators.data[i]? with
      | none => simp [found] at selected
      | some v =>
        refine ⟨v, rfl, ?_⟩
        simp only [found, Option.any_some, Bool.and_eq_true] at selected
        exact ⟨selected.1.1, by cases clean : v.slashed <;> simp_all⟩)
    (fun i member => by simpa only [parts, dite_eq_left member] using included i member)
    (fun i member => by simpa only [parts, dite_eq_left member] using exactA i member)
    (fun i member => by simpa only [parts, dite_eq_left member] using exactP i member)
    gap penaltyBound partialBound
  let sourceFalling := (Finset.range x.state.validators.data.size).filter (fun i =>
    NewReference x i ∧
    ((ledger.stops i).state.state.validators.data[i]?.map (·.slashed)).getD true = false ∧
    FirstDown (ledger.stops i).pre i)
  obtain ⟨sourceFirst, sourceA, sourceP, exactSourceA, exactSourceP,
    sourceABound, sourcePBound, sourceCountBound, sourceRoundBound⟩ :=
    source_numeric_ledger_regime ledger.stops shared supported regime twoSlots
      replayed penaltyBound partialBound
  refine ⟨{
    toLedgerCuts := ledger
    falling := falling
    exactCarrier := ?_
    first := first
    a := a
    p := p
    exactA := exactA
    exactP := exactP
    aBound := bounds.1
    pBound := bounds.2.1
    countBound := bounds.2.2.1
    roundBound := bounds.2.2.2
    sourceFalling := sourceFalling
    exactSourceCarrier := ?_
    sourceFirst := sourceFirst
    sourceA := sourceA
    sourceP := sourceP
    exactSourceA := exactSourceA
    exactSourceP := exactSourceP
    sourceABound := sourceABound
    sourcePBound := sourcePBound
    sourceCountBound := sourceCountBound
    sourceRoundBound := sourceRoundBound }, rfl⟩
  · intro i
    simp only [falling, Finset.mem_filter, Finset.mem_range]
  · intro i
    simp only [sourceFalling, Finset.mem_filter, Finset.mem_range]
theorem LedgerCuts.roundLedger_electra
    {tail : Run config checks x y} (ledger : LedgerCuts tail)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (penaltyBound : (events.map fun e =>
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (driftHorizon x high + 1))
    (partialBound : (events.map fun e =>
      ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high) :
    ∃ result : RoundLedger tail high, result.toLedgerCuts = ledger := by
  exact ledger.roundLedger_regime shared supported (.inl electra) twoSlots replayed penaltyBound
    partialBound
private theorem NewCohortCuts.retained_falling_iff
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high} (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (member : i ∈ cohort.cohort) (supported : i ∈ cohort.supported)
    (notBoundary : i ∉ cohort.boundary) :
    i ∈ ledger.falling ↔ FirstDown (ledger.headRun i) i := by
  obtain ⟨⟨w, found, clean, active, _cutoff⟩, _replay, _drop⟩ :=
    cohort.retained_replay unique early member supported notBoundary
  have cut := (ledger.retainedCut i (by simpa [found] using active)).1
  have inCohort := member
  rw [cohort.exactUniverse, Finset.mem_filter] at inCohort
  have unmarked : ((ledger.cut i).state.validators.data[i]?.map (·.slashed)).getD true = false := by
    rw [cut, found]
    exact clean
  rw [ledger.exactCarrier]
  exact ⟨fun falling => falling.2.2.2,
    fun drop => ⟨Finset.mem_range.mp inCohort.1, inCohort.2.1, unmarked, drop⟩⟩
theorem NewCohortCuts.retained_debit_regime
    {g x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high} (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (unique : PubkeysDistinct y.state) (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (member : i ∈ cohort.cohort) (retained : i ∈ cohort.supported)
    (notBoundary : i ∉ cohort.boundary)
    (replayed : (ledger.headRun i).balanceEvents high = .ok events) :
    effectiveAt x i ≤ effectiveAt y i +
      ((effectiveAt x i - actualBalanceAt x i) + (events.map (floorPenaltyDebit i)).sum +
        (events.map (floorPartialDebit (UInt64.ofNat i))).sum +
        (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) := by
  have early := supported.2.2.2.2.1
  obtain ⟨⟨w, final, clean, _active, cutoff⟩, replayEq, dropEq⟩ :=
    cohort.retained_replay unique early member retained notBoundary
  have selected := member
  rw [cohort.exactUniverse, Finset.mem_filter] at selected
  have inside := Finset.mem_range.mp selected.1
  obtain ⟨v, initial⟩ : ∃ v, x.state.validators.data[i]? = some v := by
    exact ⟨x.state.validators.data[i], Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩⟩
  have active := selected.2.1
  simp only [initial, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at active
  have unmarked : v.slashed = false := by
    cases flag : v.slashed <;> simp_all
  have activated := Consensus.Internal.assigned_of_active active.1.1
  have numeric := toNat_toUInt64_of_lt
    (x.state.validators.bound (Nat.lt_of_le_of_lt
      (fork_le_of_chainSteps tail.chainSteps) early)) inside
  have fullReplay : tail.balanceEvents high = .ok events := replayEq ▸ replayed
  have bound := retained_effective_loss_regime shared tail supported regime
    (UInt64.ofNat i) v w (by simpa only [numeric] using initial)
    (by simpa only [numeric] using final) unmarked clean activated cutoff fullReplay
  simp only [numeric] at bound
  have falling := cohort.retained_falling_iff unique early member retained notBoundary
  rw [← dropEq, ← falling] at bound
  by_cases drop : i ∈ ledger.falling
  · simpa only [drop, ↓reduceIte, Nat.add_assoc] using bound
  · simpa only [drop, ↓reduceIte, Nat.add_assoc] using bound
theorem NewCohortCuts.retained_debit_electra
    {g x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high} (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (unique : PubkeysDistinct y.state) (electra : .pectra ≤ x.fork)
    (member : i ∈ cohort.cohort) (retained : i ∈ cohort.supported)
    (notBoundary : i ∉ cohort.boundary)
    (replayed : (ledger.headRun i).balanceEvents high = .ok events) :
    effectiveAt x i ≤ effectiveAt y i +
      ((effectiveAt x i - actualBalanceAt x i) + (events.map (floorPenaltyDebit i)).sum +
        (events.map (floorPartialDebit (UInt64.ofNat i))).sum +
        (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) := by
  exact cohort.retained_debit_regime shared supported unique (.inl electra) member retained
    notBoundary replayed
private theorem NewCohortCuts.stopped_falling_iff
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high} (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (member : i ∈ cohort.boundary ∪ cohort.departed) :
    i ∈ ledger.falling ↔ FirstDown (ledger.headRun i) i := by
  obtain ⟨_, v, w, before, after, _active, _unset, _assigned, inactive⟩ :=
    cohort.charged_cohort unique early member
  obtain ⟨_numeric, c, a, b, u, _chosen, _amount, _one, _two, found,
    _cleanA, _cleanB, clean, _activated, _stopEpoch⟩ :=
    cohort.stopped_inputs unique early endpoint member
  have absent : ¬ (y.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch y.state)) := by
    simpa only [after, Option.any_some, inactive] using Bool.false_ne_true
  have cut := (ledger.stoppedCut i absent).1
  have inCohort : i ∈ cohort.cohort := by
    rcases Finset.mem_union.mp member with boundary | departed
    · rw [cohort.exactBoundary] at boundary
      exact (Finset.mem_filter.mp boundary).1
    · rw [cohort.exactDeparted] at departed
      exact (Finset.mem_sdiff.mp departed).1
  rw [cohort.exactUniverse, Finset.mem_filter] at inCohort
  rw [ledger.exactCarrier]
  have unmarked : ((ledger.cut i).state.validators.data[i]?.map (·.slashed)).getD true = false := by
    change ledger.cut i = (ledger.stops i).state at cut
    rw [cut, found]
    exact clean
  exact ⟨fun falling => falling.2.2.2,
    fun drop => ⟨Finset.mem_range.mp inCohort.1, inCohort.2.1, unmarked, drop⟩⟩
private theorem NewCohortCuts.stopped_loss_of_replay
    {g x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : LedgerCuts tail} (cohort : NewCohortCuts tail high ledger)
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (guard : aprioriGuardAt config x high)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (member : i ∈ cohort.boundary ∪ cohort.departed)
    (replayed : (ledger.headRun i).balanceEvents high = .ok events)
    (base quotient : Nat) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n (ledger.stops i).state),
      (pre.snoc step).append post = (ledger.stops i).pre →
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing) :
    effectiveAt x i ≤ cohort.charge i + (effectiveAt x i - actualBalanceAt x i) +
      ((events.map (floorPenaltyDebit i)).sum +
        (events.map (floorPartialDebit (UInt64.ofNat i))).sum) +
      (if FirstDown (ledger.headRun i) i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) := by
  obtain ⟨sameReplay, sameDrop⟩ := cohort.stopped_replay unique early member
  rw [sameReplay] at replayed
  rw [sameDrop]
  obtain ⟨numeric, c, v, w, u, chosen, amount, before, after, _found, unslashed,
    clean, _unmarked, activated, stopEpoch⟩ := cohort.stopped_inputs unique early endpoint member
  generalize indexEq : UInt64.ofNat i = index at *
  subst i
  have bound := Stop.selected_charge_loss (i := index) (ledger.stops index.toNat)
    chosen shared genesis caps increment twoSlots delay
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps (ledger.stops index.toNat).post.chainSteps) early)
    v w before after unslashed clean activated stopEpoch replayed base quotient positive
    (by
      intro m n pre step post split
      exact ⟨short_window_of_guard guard endpoint
        ((Run.nil.snoc step).append (post.append (ledger.stops index.toNat).post)),
        guards pre step post split⟩)
  rw [amount]
  simpa only [indexEq] using bound
private theorem NewCohortCuts.stopped_debit_of_replay
    {g x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high} (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (unique : PubkeysDistinct y.state) (early : y.fork < .glamsterdam)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (guard : aprioriGuardAt config x high)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (member : i ∈ cohort.boundary ∪ cohort.departed)
    (replayed : (ledger.headRun i).balanceEvents high = .ok events)
    (base quotient : Nat) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n (ledger.stops i).state),
      (pre.snoc step).append post = (ledger.stops i).pre →
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing) :
    effectiveAt x i ≤ cohort.charge i +
      ((effectiveAt x i - actualBalanceAt x i) + (events.map (floorPenaltyDebit i)).sum +
        (events.map (floorPartialDebit (UInt64.ofNat i))).sum +
        (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) := by
  have bound := cohort.stopped_loss_of_replay shared genesis caps unique early increment
    twoSlots delay guard endpoint member replayed base quotient positive guards
  have falling := cohort.stopped_falling_iff unique early endpoint member
  rw [← falling] at bound
  by_cases drop : i ∈ ledger.falling
  · simpa only [drop, ↓reduceIte, Nat.add_assoc] using bound
  · simpa only [drop, ↓reduceIte, Nat.add_assoc] using bound
theorem NewCohortCuts.stopped_debit_regime
    {g x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high} (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (unique : PubkeysDistinct y.state) (regime : .pectra ≤ x.fork ∨ y.fork < .pectra)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (member : i ∈ cohort.boundary ∪ cohort.departed)
    (replayed : (ledger.headRun i).balanceEvents high = .ok events) :
    effectiveAt x i ≤ cohort.charge i +
      ((effectiveAt x i - actualBalanceAt x i) + (events.map (floorPenaltyDebit i)).sum +
        (events.map (floorPartialDebit (UInt64.ofNat i))).sum +
        (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) := by
  obtain ⟨genesis, _parameters, caps, _aligned, early, endpoint, guard⟩ := supported
  have positive := guard
  obtain ⟨increment, _, _, _, _, _, _, quotient, _, delay, _⟩ := positive
  apply cohort.stopped_debit_of_replay shared genesis caps unique early increment twoSlots
    (by omega) guard endpoint member replayed
    (base x i) (minSlashingPenaltyQuotient preset (preElectraEpochs config x high)) quotient
  intro m n pre step post _split
  constructor
  · exact slashing_quotient_le_of_regime (shared.append tail) genesis endpoint guard pre
      (regime_prefix regime ((Run.nil.snoc step).append (post.append (ledger.stops i).post)))
  · intro added addedOk
    have stepEarly := Nat.lt_of_le_of_lt
      (fork_le_of_chainSteps (post.append (ledger.stops i).post).chainSteps) early
    exact no_crossing_of_regime shared pre genesis caps step stepEarly
      (step_regime regime pre (post.append (ledger.stops i).post)) addedOk
theorem NewCohortCuts.stopped_debit_electra
    {g x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high} (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (unique : PubkeysDistinct y.state) (electra : .pectra ≤ x.fork)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (member : i ∈ cohort.boundary ∪ cohort.departed)
    (replayed : (ledger.headRun i).balanceEvents high = .ok events) :
    effectiveAt x i ≤ cohort.charge i +
      ((effectiveAt x i - actualBalanceAt x i) + (events.map (floorPenaltyDebit i)).sum +
        (events.map (floorPartialDebit (UInt64.ofNat i))).sum +
        (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) := by
  exact cohort.stopped_debit_regime shared supported unique (.inl electra) twoSlots member
    replayed
theorem NewCohortCuts.ledger_budget_of_ceiling
    {g x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : LedgerCuts tail}
    (allocation : NewCohortCuts tail high ledger)
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (unique : PubkeysDistinct y.state)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) (maxAligned : MaxEffectiveBalancesAligned preset)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (others : ∀ {u : ForkedBeaconState preset} (head : Run config checks x u),
      u.fork < .glamsterdam → (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ found,
        head.balanceEvents high = .ok found → (found.map otherCredit).sum ≤
          whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
            (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
            (driftHorizon x high) (preElectraEpochs config x high))
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) ≤ total.toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ parts : Nat → List (BalanceEvent preset),
      (∀ i, (ledger.headRun i).balanceEvents high = .ok (parts i)) ∧
      (∑ i ∈ allocation.boundary ∪ allocation.departed, allocation.charge i) +
        (∑ i ∈ allocation.cohort,
          ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) ≤
            departureBudgetAt (config := config) x high +
                duePartialWithdrawals x (driftHorizon x high) := by
  have prefixes (i : Nat) : ∃ part,
      (ledger.headRun i).balanceEvents high = .ok part ∧ part <+: events := by
    have replay := replayed
    rw [← ledger.split i] at replay
    exact (ledger.headRun i).balanceEvents_prefix (ledger.suffix i) high events replay
  choose parts reads included using prefixes
  have indices : ∀ i ∈ allocation.cohort, i < x.state.validators.data.size := by
    intro i member
    rw [allocation.exactUniverse, Finset.mem_filter] at member
    exact Finset.mem_range.mp member.1
  have partials := stopped_partial_occurrences shared genesis tail early endpoint replayed
    allocation.cohort parts indices (fun i _ => included i)
  refine ⟨parts, reads, ?_⟩
  apply stopped_joint_budget_of_ceiling shared genesis tail electra early high endpoint
    guard maxAligned unit others floor replayed ledger.stops
    (allocation.boundary ∪ allocation.departed) allocation.charge ?_ _ partials
  intro i member
  obtain ⟨c, chosen, amount⟩ := allocation.actualCharge i member
  obtain ⟨_, v, w, before, after, active, _, _, inactive⟩ :=
    allocation.charged_cohort unique early member
  exact ⟨c, chosen, amount, ((ledger.stops i).inactive_charge_cutoff chosen
    ⟨v, before, active⟩ (by simpa only [after, Option.any_some] using inactive)).trans endpoint⟩
theorem NewCohortCuts.slack_penalty_bounds
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : LedgerCuts tail} (cohort : NewCohortCuts tail high ledger)
    (early : x.fork < .glamsterdam)
    (parts : Nat → List (BalanceEvent preset)) (events : List (BalanceEvent preset))
    (included : ∀ i ∈ cohort.cohort, parts i <+: events) :
    (∑ i ∈ cohort.cohort, (effectiveAt x i - actualBalanceAt x i)) ≤ startSlack x ∧
      (∑ i ∈ cohort.cohort, ((parts i).map (floorPenaltyDebit i)).sum) ≤
        (events.map fun e => ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map
          fun i => if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
            else floorPenaltyDebit i.toNat e).sum).sum := by
  have active (i : Nat) (member : i ∈ cohort.cohort) : ∃ v,
      x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false := by
    rw [cohort.exactUniverse, Finset.mem_filter] at member
    have selected := member.2.1
    cases found : x.state.validators.data[i]? with
    | none => simp [found] at selected
    | some v =>
      refine ⟨v, rfl, ?_⟩
      simp only [found, Option.any_some, Bool.and_eq_true] at selected
      exact ⟨selected.1.1, by cases clean : v.slashed <;> simp_all⟩
  refine ⟨initial_active_slack_le cohort.cohort early (fun i member => by
    obtain ⟨v, found, enabled, _⟩ := active i member
    exact ⟨v, found, enabled⟩), ?_⟩
  have prefixes := prefix_resource_sum_le cohort.cohort parts events
    (fun i => floorPenaltyDebit i) included
  have total : (events.map fun e => ∑ i ∈ cohort.cohort, floorPenaltyDebit i e).sum ≤
      (events.map fun e => ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map
        fun i => if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else floorPenaltyDebit i.toNat e).sum).sum := by
    clear included prefixes
    induction events with
    | nil => simp
    | cons e events ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (initial_unslashed_debit_le cohort.cohort early active
        (fun i => floorPenaltyDebit i e)) ih
  exact prefixes.trans total
theorem NewCohortAllocation.loss_boundary_bound
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {ledger : RoundLedger tail high}
    (allocation : NewCohortAllocation tail high ledger owned tokens)
    (boundarySupported : allocation.boundary ⊆ allocation.supported) :
    (∑ i ∈ allocation.cohort,
      (effectiveAt x i - if i ∈ allocation.supported then effectiveAt y i else 0)) +
      (∑ i ∈ allocation.boundary, effectiveAt y i) ≤
    departureBudgetAt (config := config) x high + duePartialWithdrawals x (driftHorizon x high) +
        startSlack x +
      windowPenalties (config := config) x high (driftHorizon x high + 1) +
          roundingBudget (config := config) x high +
      (∑ i ∈ allocation.boundary, (effectiveAt y i - effectiveAt x i)) := by
  have boundarySubset : allocation.boundary ⊆ allocation.cohort := by
    rw [allocation.exactBoundary]
    exact Finset.filter_subset _ _
  have departedSubset : allocation.departed ⊆ allocation.cohort := by
    rw [allocation.exactDeparted]
    exact Finset.sdiff_subset
  have departedIff : ∀ i ∈ allocation.cohort,
      i ∈ allocation.departed ↔ i ∉ allocation.supported := by
    intro i member
    rw [allocation.exactDeparted, Finset.mem_sdiff]
    exact and_iff_right member
  have arithmetic := new_reference_loss_boundary_le allocation.cohort allocation.supported
    allocation.boundary allocation.departed (effectiveAt x) (effectiveAt y)
    allocation.charge allocation.debit boundarySupported boundarySubset departedSubset
    departedIff allocation.stopped allocation.retained
  have queue := allocation.queueBudget
  have debits := allocation.debitBudget
  omega

end RunContracts

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
