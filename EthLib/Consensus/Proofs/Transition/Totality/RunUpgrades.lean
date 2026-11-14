module

public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoadUpgrades
public import EthLib.Consensus.Proofs.Transition.Totality.RunBounds

/-!
# Proofs: the upgrades keep the bounds of a run of slots

An upgrade keeps the slot, so it counts no epoch, and the bounds of a run keep their parameters.

Most upgrades carry the fields that the bounds read.

The upgrade to Altair starts the inactivity scores at zero.

The upgrade to Electra moves balances into pending deposits, and zeroes some effective balances.

So the supply stays, and the sum of the effective balances can only fall.

It opens the exit queue one past the latest exit and the first activation epoch.

The exit ceiling allows that when it covers the first activation epoch.

The upgrade to Gloas can only remove pending deposits, when it funds builders from them.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Two registries that are the same sequence have the same sum of effective balances. -/
private theorem effectiveBalanceSum_eq_of_validators {fork post : Fork}
    {state : BeaconState preset fork} {other : BeaconState preset post}
    (same : other.validators.data = state.validators.data) :
    effectiveBalanceSum other = effectiveBalanceSum state := by
  unfold effectiveBalanceSum
  rw [same]

/-- Replacing a validator changes the sum of the effective balances by the difference. -/
private theorem effectiveBalanceSum_putValidator {fork : Fork} {state : BeaconState preset fork}
    {index : Nat} (inside : index < state.validators.data.size) (validator : Validator) :
    effectiveBalanceSum (state.putValidator index inside validator) +
        state.validators.data[index].effectiveBalance.toNat =
      effectiveBalanceSum state + validator.effectiveBalance.toNat := by
  unfold effectiveBalanceSum BeaconState.putValidator
  simp only [Serialization.Ssz.RootedForkList.data_set, Array.toList_set, List.map_set]
  have := sum_set_add (l := state.validators.data.toList.map (·.effectiveBalance.toNat))
    (i := index) (by simpa using inside) validator.effectiveBalance.toNat
  simpa using this

/-- Queueing a validator not yet active never raises the sum of the effective balances. -/
private theorem queuePreActivation_effectiveBalanceSum_le {fork : Fork}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    effectiveBalanceSum after ≤ effectiveBalanceSum state := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨inside, rfl⟩ := setValidator_ok set₂
  refine (effectiveBalanceSum_eq_of_validators (state := BeaconState.putValidator _ _ inside _)
    rfl).trans_le ?_
  have zeroed := effectiveBalanceSum_putValidator inside
    { validator with effectiveBalance := 0, activationEligibilityEpoch := FAR_FUTURE_EPOCH }
  have kept := effectiveBalanceSum_eq_of_validators (state := state)
    (other := state.putBalance _ ‹_› 0) rfl
  simp only [UInt64.toNat_zero, Nat.add_zero] at zeroed
  exact (Nat.le_add_right _ _).trans (zeroed.trans kept).le

/-- Queueing an excess balance keeps the registry. -/
private theorem queueCompoundingExcess_validators {fork : Fork}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    after.validators = state.validators := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok set
        rfl
      · cases queued
        rfl
    · cases computed
      rfl
  · cases computed
    rfl

/-- The upgrade to Electra never raises the sum of the effective balances. -/
private theorem upgradeToElectra_effectiveBalanceSum_le {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    effectiveBalanceSum after ≤ effectiveBalanceSum pre := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := computed
  have first := foldlM_ok_invariant
    (fun state : BeaconState preset .pectra => effectiveBalanceSum state ≤ effectiveBalanceSum pre)
    (fun _ _ _ before step => (queuePreActivation_effectiveBalanceSum_le step).trans before)
    (Nat.le_of_eq (effectiveBalanceSum_eq_of_validators rfl)) queued
  exact foldlM_ok_invariant
    (fun state : BeaconState preset .pectra => effectiveBalanceSum state ≤ effectiveBalanceSum pre)
    (fun _ _ _ before step => (effectiveBalanceSum_eq_of_validators
      (by rw [queueCompoundingExcess_validators step])).le.trans before)
    first compounded

/-- From Electra, the sum of the pending deposits reads the queue. -/
private theorem pendingDepositSum_of_electra {fork : Fork} {state : BeaconState preset fork}
    (electra : .pectra ≤ fork) :
    pendingDepositSum state = pendingAmount (state.pendingDeposits electra).data.toList := by
  simp [pendingDepositSum, electra]

/-- Replacing a balance changes the sum of the balances by the difference. -/
private theorem balanceSum_putBalance {fork : Fork} {state : BeaconState preset fork}
    {index : Nat} (inside : index < state.balances.data.size) (balance : Gwei) :
    balanceSum (state.putBalance index inside balance) + state.balances.data[index].toNat =
      balanceSum state + balance.toNat := by
  unfold balanceSum BeaconState.putBalance
  simp only [Array.toList_set, List.map_set]
  have := sum_set_add (l := state.balances.data.toList.map (·.toNat)) (i := index)
    (by simpa using inside) balance.toNat
  simpa using this

/-- What each step of the queueing at Electra keeps, and the supply it never raises. -/
private structure ElectraStep {fork : Fork} (state after : BeaconState preset fork) : Prop where
  supply : balanceSum after + pendingDepositSum after ≤ balanceSum state + pendingDepositSum state
  exits : ∀ validator ∈ after.validators.data,
    ∃ old ∈ state.validators.data, old.exitEpoch = validator.exitEpoch
  scores : after.inactivityScores = state.inactivityScores
  roots : after.historicalRoots = state.historicalRoots
  summaries : after.historicalSummaries = state.historicalSummaries
  depositChurn : after.depositBalanceToConsume = state.depositBalanceToConsume
  exitChurn : after.exitBalanceToConsume = state.exitBalanceToConsume
  queue : after.earliestExitEpoch = state.earliestExitEpoch
  consolidations : after.earliestConsolidationEpoch = state.earliestConsolidationEpoch
  slashings : after.slashings = state.slashings

private theorem ElectraStep.refl {fork : Fork} (state : BeaconState preset fork) :
    ElectraStep state state :=
  ⟨Nat.le_refl _, fun validator member => ⟨validator, member, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

private theorem ElectraStep.trans {fork : Fork} {first second third : BeaconState preset fork}
    (one : ElectraStep first second) (two : ElectraStep second third) :
    ElectraStep first third := by
  refine ⟨two.supply.trans one.supply, fun validator member => ?_, two.scores.trans one.scores,
    two.roots.trans one.roots, two.summaries.trans one.summaries,
    two.depositChurn.trans one.depositChurn, two.exitChurn.trans one.exitChurn,
    two.queue.trans one.queue, two.consolidations.trans one.consolidations,
    two.slashings.trans one.slashings⟩
  obtain ⟨middle, middleMember, same⟩ := two.exits validator member
  obtain ⟨old, oldMember, same'⟩ := one.exits middle middleMember
  exact ⟨old, oldMember, same'.trans same⟩

/-- Queueing a validator not yet active moves its balance into the queue. -/
private theorem electraStep_queuePreActivation {fork : Fork}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    ElectraStep state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, balance, gotBalance, pending, appended, _, set₁, _, set₂, shape⟩ :=
    computed
  obtain ⟨inside₁, rfl⟩ := setBalance_ok set₁
  obtain ⟨inside₂, rfl⟩ := setValidator_ok set₂
  have balances : after.balances = (state.putBalance _ inside₁ 0).balances := by
    rw [← shape]
    rfl
  have queued : after.pendingDeposits electra = pending := by
    rw [← shape]
  have validators : after.validators.data =
      state.validators.data.set index.toNat
        { validator with effectiveBalance := 0, activationEligibilityEpoch := FAR_FUTURE_EPOCH }
        inside₂ := by
    rw [← shape]
    simp [BeaconState.putValidator, BeaconState.putBalance]
  subst shape
  refine ⟨?_, fun member mem => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have moved := balanceSum_putBalance inside₁ 0
    rw [(Array.getElem?_eq_some_iff.mp (getBalance_eq_ok_iff.mp gotBalance)).2,
      UInt64.toNat_zero] at moved
    rw [balanceSum_eq_of_balances balances, pendingDepositSum_of_electra electra,
      pendingDepositSum_of_electra electra, queued]
    simp only [appendWithinLimit_data appended, Array.toList_push, pendingAmount, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · rw [validators] at mem
    rcases Array.mem_or_eq_of_mem_set mem with old | rfl
    · exact ⟨member, old, rfl⟩
    · exact ⟨validator, mem_of_getValidator found, rfl⟩

/-- Queueing an excess balance moves the excess into the queue. -/
private theorem electraStep_queueCompoundingExcess {fork : Fork}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    ElectraStep state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨balance, gotBalance, queued⟩ := queued
      split at queued
      · rename_i above
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, -, pending, appended, _, set, shape⟩ := queued
        obtain ⟨inside, rfl⟩ := setBalance_ok set
        have balances : after.balances =
            (state.putBalance _ inside preset.MIN_ACTIVATION_BALANCE).balances := by
          rw [← shape]
        have queuedDeposits : after.pendingDeposits electra = pending := by
          rw [← shape]
        subst shape
        refine ⟨?_, fun member mem => ⟨member, mem, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have moved := balanceSum_putBalance inside preset.MIN_ACTIVATION_BALANCE
        rw [(Array.getElem?_eq_some_iff.mp (getBalance_eq_ok_iff.mp gotBalance)).2] at moved
        rw [balanceSum_eq_of_balances balances, pendingDepositSum_of_electra electra,
          pendingDepositSum_of_electra electra, queuedDeposits]
        simp only [appendWithinLimit_data appended, Array.toList_push, pendingAmount,
          List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt above)]
        have := UInt64.lt_iff_toNat_lt.mp above
        omega
      · cases queued
        exact .refl _
    · cases computed
      exact .refl _
  · cases computed
    exact .refl _

/-- The total active balance is at most one increment plus the sum of the effective balances. -/
private theorem getTotalActiveBalance_le {fork : Fork} {state : BeaconState preset fork}
    {total : Gwei} (computed : getTotalActiveBalance state = .ok total) :
    total.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state := by
  obtain ⟨-, fits, rfl⟩ := getTotalBalance_ok_iff.mp (getTotalActiveBalance_ok computed)
  have marked : sumMarked state.validators.data (markIndices state.validators.data.size
      (getActiveValidatorIndices state (getCurrentEpoch state))) ≤ effectiveBalanceSum state := by
    rw [sumMarked_eq_sum, effectiveBalanceSum_eq_sum_range]
    refine sum_map_le_sum_map fun j _ => ?_
    split <;> omega
  rw [UInt64.max_def]
  split
  · rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
    omega
  · omega

/-- The activation exit churn is within the bound of one exit churn. -/
private theorem getActivationExitChurnLimit_le {fork : Fork} {state : BeaconState preset fork}
    {churn : Gwei} (computed : getActivationExitChurnLimit config state = .ok churn) :
    churn.toNat ≤ exitChurnCeiling config state := by
  simp only [getActivationExitChurnLimit, getBalanceChurnLimit, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, ⟨total, totalOk, rfl⟩, rfl⟩ := computed
  have totalLe := getTotalActiveBalance_le totalOk
  have remainder : ∀ amount : Gwei, amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ amount :=
    fun amount => by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
  have share : (total / config.CHURN_LIMIT_QUOTIENT).toNat ≤ total.toNat := by
    rw [UInt64.toNat_div]
    exact Nat.div_le_self _ _
  rw [Uint64.toNat_min, roundToIncrement, UInt64.toNat_sub_of_le _ _ (remainder _), UInt64.max_def]
  unfold exitChurnCeiling
  split <;> omega

/-- The latest exit epoch that is set stays within a bound that covers its start and each one. -/
private theorem foldl_latestExit_le {bound : Nat} :
    ∀ (validators : List Validator) (start : UInt64), start.toNat ≤ bound →
      (∀ validator ∈ validators, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch.toNat ≤ bound) →
      (validators.foldl (fun latest validator =>
        if validator.exitEpoch = FAR_FUTURE_EPOCH then latest
        else max latest validator.exitEpoch) start).toNat ≤ bound
  | [], _, startLe, _ => startLe
  | validator :: rest, start, startLe, each => by
    rw [List.foldl_cons]
    refine foldl_latestExit_le rest _ ?_ fun other member =>
      each other (List.mem_cons_of_mem _ member)
    split
    · exact startLe
    · rename_i set
      rw [Uint64.toNat_max]
      exact max_le startLe (each validator List.mem_cons_self set)

/-- What the upgrade to Electra keeps or starts, for the bounds of a run. -/
private structure ElectraBounds (config : Config) (pre : BeaconState preset .dencun)
    (after : BeaconState preset .pectra) : Prop where
  /-- The balances plus the pending deposits do not rise. -/
  supply : balanceSum after + pendingDepositSum after ≤ balanceSum pre + pendingDepositSum pre
  /-- Each exit epoch is that of a validator before. -/
  exits : ∀ validator ∈ after.validators.data,
    ∃ old ∈ pre.validators.data, old.exitEpoch = validator.exitEpoch
  /-- The inactivity scores carry over. -/
  scores : (after.inactivityScores (by decide)).data = (pre.inactivityScores (by decide)).data
  /-- The historical roots carry over. -/
  roots : after.historicalRoots = pre.historicalRoots
  /-- The historical summaries carry over. -/
  summaries :
    (after.historicalSummaries (by decide)).data = (pre.historicalSummaries (by decide)).data
  /-- The deposit churn starts at zero. -/
  depositChurn : after.depositBalanceToConsume (by decide) = 0
  /-- The exit churn starts within the bound of one exit churn. -/
  exitChurn : (after.exitBalanceToConsume (by decide)).toNat ≤ exitChurnCeiling config pre
  /-- The exit queue opens one past any bound on the first activation epoch and on each exit. -/
  queue : ∀ bound : Nat,
    (getCurrentEpoch pre).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ bound →
    (∀ validator ∈ pre.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ bound) →
    (after.earliestExitEpoch (by decide)).toNat ≤ bound + 1
  /-- The consolidation queue opens at the first activation epoch. -/
  consolidations : (after.earliestConsolidationEpoch (by decide)).toNat =
    (getCurrentEpoch pre).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat
  /-- The slashed balances carry over. -/
  slashings : after.slashings = pre.slashings

/-- The upgrade to Electra keeps or starts what the bounds of a run read. -/
private theorem upgradeToElectra_bounds {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    ElectraBounds config pre after := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨activation, activationOk, earliest, earliestOk, exitChurn, exitOk, _, -, middle, queued,
    compounded⟩ := computed
  have first := foldlM_ok_invariant (ElectraStep _)
    (fun _ _ _ before step => before.trans (electraStep_queuePreActivation step))
    (.refl _) queued
  have kept := foldlM_ok_invariant (ElectraStep _)
    (fun _ _ _ before step => before.trans (electraStep_queueCompoundingExcess step))
    first compounded
  simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at activationOk earliestOk
  have activationEq := (computeActivationExitEpoch_ok_iff.mp activationOk).2
  have earliestEq := (Uint64.addChecked_ok_iff.mp earliestOk).2
  refine ⟨?_, fun validator member => ?_, by rw [kept.scores]; rfl, kept.roots,
    by rw [kept.summaries]; rfl, by rw [kept.depositChurn]; rfl, ?_, fun bound early exits => ?_,
    ?_, kept.slashings⟩
  · refine kept.supply.trans (Nat.le_of_eq ?_)
    rw [balanceSum_eq_of_balances (state := pre) rfl]
    rfl
  · obtain ⟨old, oldMember, same⟩ := kept.exits validator member
    exact ⟨old, oldMember, same⟩
  · rw [kept.exitChurn]
    exact getActivationExitChurnLimit_le (liftAccessor_ok.mp exitOk)
  · rw [kept.queue]
    change earliest.toNat ≤ bound + 1
    have latest := foldl_latestExit_le pre.validators.data.toList activation (by omega)
      fun validator member => exits validator (Array.mem_toList_iff.mp member)
    rw [Array.foldl_toList] at latest
    rw [earliestEq]
    exact Nat.add_le_add latest (Nat.le_refl _)
  · rw [kept.consolidations]
    change activation.toNat = _
    exact activationEq

/-- An upgrade never raises the sum of the effective balances. -/
theorem upgradeNext_effectiveBalanceSum_le {pre : ForkedBeaconState preset}
    {next : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok next) :
    effectiveBalanceSum next.val.state ≤ effectiveBalanceSum pre.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (effectiveBalanceSum_eq_of_validators (upgradeToAltair_spec upgraded).1).le
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact (effectiveBalanceSum_eq_of_validators rfl).le
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact upgradeToElectra_effectiveBalanceSum_le upgraded
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (effectiveBalanceSum_eq_of_validators (upgradeToFulu_spec upgraded).1).le
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact (effectiveBalanceSum_eq_of_validators (upgradeToGloas_spec upgraded).1).le
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact (effectiveBalanceSum_eq_of_validators (upgradeHezeFields_lists state).1).le
  all_goals simp only [upgradeNext] at computed; cases computed

/-- The upgrades due at a slot never raise the sum of the effective balances. -/
theorem processUpgrades_effectiveBalanceSum_le {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    effectiveBalanceSum after.state ≤ effectiveBalanceSum forked.state :=
  processUpgrades_induction
    (property := fun state => effectiveBalanceSum state.state ≤ effectiveBalanceSum forked.state)
    (fun before stepOk => (upgradeNext_effectiveBalanceSum_le stepOk).trans before) le_rfl computed

/-- Two lists of balances that are the same sequence have the same sum. -/
private theorem balanceSum_eq_of_data {fork post : Fork} {state : BeaconState preset fork}
    {other : BeaconState preset post} (same : other.balances.data = state.balances.data) :
    balanceSum other = balanceSum state := by
  unfold balanceSum
  rw [same]

/-- Before Electra there is no pending deposit. -/
private theorem pendingDepositSum_of_lt {fork : Fork} {state : BeaconState preset fork}
    (early : fork < .pectra) : pendingDepositSum state = 0 := by
  have notElectra : ¬ Fork.pectra ≤ fork := Nat.not_le_of_lt early
  simp only [pendingDepositSum, notElectra, ↓reduceDIte]

/-- Two lists of slashed balances that are the same have the same sum. -/
private theorem slashedBalanceSum_eq {fork post : Fork} {state : BeaconState preset fork}
    {other : BeaconState preset post} (same : other.slashings = state.slashings) :
    slashedBalanceSum other = slashedBalanceSum state := by
  unfold slashedBalanceSum
  rw [same]

variable {start : RunStart} {budget elapsed : Nat}

/-- A state with no more effective balance than another keeps the bound on them. -/
private theorem RunBounded.effective_of_le {fork post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (holds : RunBounded config start budget elapsed state)
    (le : effectiveBalanceSum after ≤ effectiveBalanceSum state) :
    effectiveBalanceSum after ≤ start.effective ∨
      effectiveBalanceSum after *
          (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
        (start.supply + elapsed * preset.epochIssuanceBeforeAltair budget) *
          preset.HYSTERESIS_QUOTIENT.toNat :=
  holds.effective.imp le.trans (Nat.le_trans (Nat.mul_le_mul_right _ le))

/-- An upgrade before Electra keeps the bounds when it carries what they read.

The inactivity scores and historical summaries it starts must be within their bounds. -/
private theorem RunBounded.of_early {fork post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (holds : RunBounded config start budget elapsed state)
    (early : post < .pectra) (forward : fork ≤ post)
    (effective : effectiveBalanceSum after ≤ effectiveBalanceSum state)
    (load : registryLoadFactor post * registryLoad after ≤ start.load)
    (validators : after.validators.data = state.validators.data)
    (balances : after.balances.data = state.balances.data)
    (scores : ∀ altair : .altair ≤ post, ∀ score ∈ (after.inactivityScores altair).data,
      score.toNat ≤ start.scores + config.INACTIVITY_SCORE_BIAS.toNat * elapsed)
    (roots : after.historicalRoots = state.historicalRoots)
    (summaries : ∀ capella : .shapella ≤ post,
      (after.historicalSummaries capella).data.size ≤ start.history + elapsed)
    (slashings : after.slashings = state.slashings) :
    RunBounded config start budget elapsed after := by
  have notElectra : ¬ Fork.pectra ≤ post := Nat.not_le_of_lt early
  refine ⟨?_, holds.effective_of_le effective, load, scores, ?_,
    fun electra => absurd electra notElectra, fun electra => absurd electra notElectra,
    by rw [roots]; exact holds.roots, summaries,
    fun electra => absurd electra notElectra, fun electra => absurd electra notElectra,
    (slashedBalanceSum_eq slashings).trans_le holds.slashed⟩
  · rw [balanceSum_eq_of_data balances, pendingDepositSum_of_lt early]
    have := holds.supply
    rw [pendingDepositSum_of_lt (Nat.lt_of_le_of_lt forward early)] at this
    exact this
  · rw [validators]
    exact holds.exits

/-- An upgrade from Electra keeps the bounds when it carries what they read.

It may lower the supply. -/
private theorem RunBounded.of_carried {fork post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (holds : RunBounded config start budget elapsed state)
    (electra : .pectra ≤ fork)
    (supply : balanceSum after + pendingDepositSum after ≤
      balanceSum state + pendingDepositSum state)
    (effective : effectiveBalanceSum after ≤ effectiveBalanceSum state)
    (load : registryLoadFactor post * registryLoad after ≤ start.load)
    (validators : after.validators.data = state.validators.data)
    (scores : ∀ (later : .altair ≤ post) (earlier : .altair ≤ fork),
      (after.inactivityScores later).data = (state.inactivityScores earlier).data)
    (roots : after.historicalRoots = state.historicalRoots)
    (summaries : ∀ (later : .shapella ≤ post) (earlier : .shapella ≤ fork),
      (after.historicalSummaries later).data = (state.historicalSummaries earlier).data)
    (depositChurn : ∀ (later : .pectra ≤ post) (earlier : .pectra ≤ fork),
      after.depositBalanceToConsume later = state.depositBalanceToConsume earlier)
    (exitChurn : ∀ (later : .pectra ≤ post) (earlier : .pectra ≤ fork),
      after.exitBalanceToConsume later = state.exitBalanceToConsume earlier)
    (queue : ∀ (later : .pectra ≤ post) (earlier : .pectra ≤ fork),
      after.earliestExitEpoch later = state.earliestExitEpoch earlier)
    (consolidations : ∀ (later : .pectra ≤ post) (earlier : .pectra ≤ fork),
      after.earliestConsolidationEpoch later = state.earliestConsolidationEpoch earlier)
    (slashings : after.slashings = state.slashings) :
    RunBounded config start budget elapsed after := by
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) electra
  have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) electra
  refine ⟨supply.trans holds.supply, holds.effective_of_le effective, load,
    fun later score member => ?_, by rw [validators]; exact holds.exits,
    fun later => by rw [queue later electra]; exact holds.queue electra,
    fun later => by rw [consolidations later electra]; exact holds.consolidations electra,
    by rw [roots]; exact holds.roots,
    fun later => by rw [summaries later capella]; exact holds.summaries capella,
    fun later => by rw [depositChurn later electra]; exact holds.depositChurn electra,
    fun later => by rw [exitChurn later electra]; exact holds.exitChurn electra,
    (slashedBalanceSum_eq slashings).trans_le holds.slashed⟩
  rw [scores later altair] at member
  exact holds.scores altair score member

/-- The upgrade to Altair keeps the bounds, with its inactivity scores at zero. -/
private theorem RunBounded.of_upgradeToAltair {pre : BeaconState preset .phase0}
    {after : BeaconState preset .altair} (holds : RunBounded config start budget elapsed pre)
    (effective : effectiveBalanceSum after ≤ effectiveBalanceSum pre)
    (load : registryLoadFactor .altair * registryLoad after ≤ start.load)
    (computed : upgradeToAltair config pre = .ok after) :
    RunBounded config start budget elapsed after := by
  obtain ⟨validators, balances, -⟩ := upgradeToAltair_spec computed
  obtain ⟨middle, folded, committee, shape⟩ := upgradeToAltair_ok computed
  obtain ⟨participation, rfl, -⟩ := foldlM_translateAttestation folded
  have scores : (after.inactivityScores (by decide)).data =
      Array.replicate pre.validators.data.size 0 := by
    subst shape
    rfl
  refine holds.of_early (by decide) (by decide) effective load validators balances
    (fun _ score member => ?_) (by subst shape; rfl) (fun capella => absurd capella (by decide))
    (by subst shape; rfl)
  rw [scores, Array.mem_replicate] at member
  rw [member.2]
  exact Nat.zero_le _

/-- A carry-over before Electra keeps the bounds, with any new score at zero. -/
private theorem RunBounded.of_carryFields {fork post : Fork} {pre : BeaconState preset fork}
    (holds : RunBounded config start budget elapsed pre) (upgrade : fork < post)
    (before : post < .glamsterdam) (early : post < .pectra)
    (load : registryLoadFactor post * registryLoad (carryFields config post pre upgrade before) ≤
      start.load) :
    RunBounded config start budget elapsed (carryFields config post pre upgrade before) := by
  refine holds.of_early early (Nat.le_of_lt upgrade) (effectiveBalanceSum_eq_of_validators rfl).le
    load rfl rfl (fun later score member => ?_) rfl (fun later => ?_) rfl
  · by_cases altair : Fork.altair ≤ fork
    · simp only [carryFields, altair, ↓reduceDIte, carryList] at member
      exact holds.scores altair score member
    · simp only [carryFields, altair, ↓reduceDIte, zeroPerValidator, Array.mem_replicate] at member
      rw [member.2]
      exact Nat.zero_le _
  · by_cases capella : Fork.shapella ≤ fork
    · simp only [carryFields, capella, ↓reduceDIte]
      exact holds.summaries capella
    · simp only [carryFields, capella, ↓reduceDIte]
      exact Nat.zero_le _

/-- The upgrade to Electra keeps the bounds, under the conditions of one upgrade. -/
private theorem RunBounded.of_upgradeToElectra {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (holds : RunBounded config start budget elapsed pre)
    (budgeted : effectiveBalanceSum pre ≤ budget)
    (first : (getCurrentEpoch pre).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget elapsed)
    (effective : effectiveBalanceSum after ≤ effectiveBalanceSum pre)
    (load : registryLoadFactor .pectra * registryLoad after ≤ start.load)
    (computed : upgradeToElectra config pre = .ok after) :
    RunBounded config start budget elapsed after := by
  obtain ⟨supply, exits, scores, roots, summaries, depositChurn, exitChurn, queue, consolidations,
    slashings⟩ := upgradeToElectra_bounds computed
  refine ⟨supply.trans holds.supply, holds.effective_of_le effective, load,
    fun _ score member => ?_, fun validator member set => ?_,
    fun _ => queue _ first holds.exits, fun _ => by rw [consolidations]; omega,
    by rw [roots]; exact holds.roots,
    fun _ => by rw [summaries]; exact holds.summaries (by decide),
    fun _ => by rw [depositChurn]; exact Nat.zero_le _, fun _ => ?_,
    (slashedBalanceSum_eq slashings).trans_le holds.slashed⟩
  · rw [scores] at member
    exact holds.scores (by decide) score member
  · obtain ⟨old, oldMember, same⟩ := exits validator member
    rw [← same] at set ⊢
    exact holds.exits old oldMember set
  · refine exitChurn.trans (le_max_of_le_right ?_)
    unfold exitChurnCeiling exitChurnBound
    omega

/-- The upgrade to Fulu keeps the bounds, since it carries what they read. -/
private theorem RunBounded.of_upgradeToFulu {pre : BeaconState preset .pectra}
    {after : BeaconState preset .fusaka} (holds : RunBounded config start budget elapsed pre)
    (effective : effectiveBalanceSum after ≤ effectiveBalanceSum pre)
    (load : registryLoadFactor .fusaka * registryLoad after ≤ start.load)
    (computed : upgradeToFulu config pre = .ok after) :
    RunBounded config start budget elapsed after := by
  simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, -, rfl⟩ := computed
  exact holds.of_carried (by decide) (Nat.le_of_eq rfl) effective load rfl
    (fun _ _ => rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl

/-- The upgrade to Gloas keeps the bounds, since its onboarding only removes pending deposits. -/
private theorem RunBounded.of_upgradeToGloas {pre : BeaconState preset .fusaka}
    {after : BeaconState preset .glamsterdam} (holds : RunBounded config start budget elapsed pre)
    (effective : effectiveBalanceSum after ≤ effectiveBalanceSum pre)
    (load : registryLoadFactor .glamsterdam * registryLoad after ≤ start.load)
    (computed : upgradeToGloas config checks pre = .ok after) :
    RunBounded config start budget elapsed after := by
  unfold upgradeToGloas at computed
  obtain ⟨root, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
  obtain ⟨⟨builders, pending, rfl⟩, funded⟩ := onboardBuildersFromPendingDeposits_spec onboarded
  have empty : builderBalanceSum { upgradeFields config pre root with
      ptcWindow := fun _ => window } (by decide) = 0 := rfl
  have supply : balanceSum pre + pendingAmount (pending (by decide)).data.toList ≤
      balanceSum pre + pendingDepositSum pre := by
    rw [pendingDepositSum_of_electra (by decide)]
    have := Nat.le_trans (Nat.le_add_left _ _) funded
    rw [empty, Nat.zero_add] at this
    exact Nat.add_le_add_left this _
  exact holds.of_carried (by decide)
    (by rw [pendingDepositSum_of_electra (by decide)]; exact supply) effective load rfl
    (fun _ _ => rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl

/-- An upgrade keeps the bounds of a run, with the same number of epochs.

The budget must cover the sum of the effective balances.

The current epoch plus one plus the seed lookahead must be at most the exit ceiling.

The upgrade to Electra needs both, to bound the exit churn and the end of the exit queue. -/
theorem RunBounded.of_upgradeNext {start : RunStart} {budget elapsed : Nat}
    {pre : ForkedBeaconState preset}
    {next : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : RunBounded config start budget elapsed pre.state)
    (budgeted : effectiveBalanceSum pre.state ≤ budget)
    (first : (getCurrentEpoch pre.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget elapsed)
    (computed : upgradeNext config checks pre = .ok next) :
    RunBounded config start budget elapsed next.val.state := by
  have effective := upgradeNext_effectiveBalanceSum_le computed
  have load := (upgradeNext_weightedRegistryLoad_le computed).trans holds.load
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact holds.of_upgradeToAltair effective load upgraded
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds.of_carryFields _ (by dsimp only; decide) (by dsimp only; decide) load
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact holds.of_upgradeToElectra budgeted first effective load upgraded
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact holds.of_upgradeToFulu effective load upgraded
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact holds.of_upgradeToGloas effective load upgraded
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact holds.of_carried (by dsimp only; decide) (Nat.le_of_eq rfl) effective load rfl
      (fun _ _ => rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl
  all_goals simp only [upgradeNext] at computed; cases computed

/-- The upgrades due at a slot keep the bounds of a run, with the same number of epochs.

The conditions are those of one upgrade, on the state before the upgrades. -/
theorem RunBounded.of_processUpgrades {start : RunStart} {budget elapsed : Nat}
    {forked after : ForkedBeaconState preset}
    (holds : RunBounded config start budget elapsed forked.state)
    (budgeted : effectiveBalanceSum forked.state ≤ budget)
    (first : (getCurrentEpoch forked.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
      start.ceilingAt preset budget elapsed)
    (computed : processUpgrades config checks forked = .ok after) :
    RunBounded config start budget elapsed after.state := by
  -- Each upgrade keeps the slot and lowers the effective balances, so the conditions carry.
  refine (processUpgrades_induction
    (property := fun state => RunBounded config start budget elapsed state.state ∧
      effectiveBalanceSum state.state ≤ effectiveBalanceSum forked.state ∧
      state.state.slot = forked.state.slot)
    (fun {pre _} ⟨bounded, lower, slot⟩ stepOk => ⟨?_,
      (upgradeNext_effectiveBalanceSum_le stepOk).trans lower,
      (upgradeFrame_upgradeNext stepOk).slot.trans slot⟩)
    ⟨holds, le_rfl, rfl⟩ computed).1
  have epoch : getCurrentEpoch pre.state = getCurrentEpoch forked.state := by
    unfold getCurrentEpoch
    rw [slot]
  exact bounded.of_upgradeNext (lower.trans budgeted) (by rw [epoch]; exact first) stepOk

end EthLib.Consensus
