module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.FirstDrop

/-!
# The round ledger of a branch

The first update of each key, and the cuts that charge its departure to the window.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section RunContracts
variable {g x y : ForkedBeaconState preset}

structure FirstUpdate {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high i : Nat) where
  outer : ForkedBeaconState preset
  after : ForkedBeaconState preset
  pre : Run config checks x outer
  post : Run config checks after y
  advanced : BeaconState preset outer.fork
  cached : BeaconState preset outer.fork
  middle : BeaconState preset outer.fork
  updated : BeaconState preset outer.fork
  next : Slot
  stepOk : advanceSlotAcross config checks outer = .ok after
  split : (pre.snoc (.slot stepOk)).append post = tail
  nextOk : addChecked outer.state.slot 1 = .ok next
  last : next % preset.SLOTS_PER_EPOCH = 0
  advancedOk : advanceSlot config checks outer.state = .ok advanced
  cachedOk : processSlot outer.state = .ok cached
  events : List (BalanceEvent preset)
  replay : epochBalanceReplay (config := config) (checks := checks) cached = .ok (middle, events)
  updateOk : processEffectiveBalanceUpdates middle = .ok updated
  finalValidators : advanced.validators = updated.validators
  beforeValidator : Validator
  afterValidator : Validator
  foundBefore : middle.validators.data[i]? = some beforeValidator
  foundAfter : updated.validators.data[i]? = some afterValidator
  actualUpdate : updatedEffectiveBalance preset
    (withdrawalMaxEffectiveBalance preset outer.fork beforeValidator)
    ((middle.balances.data[i]?).getD 0) beforeValidator.effectiveBalance =
      .ok afterValidator.effectiveBalance
  decreases : afterValidator.effectiveBalance < beforeValidator.effectiveBalance
  noEarlier : ∀ j a b, pre.balancePath[j]? = some a →
    pre.balancePath[j + 1]? = some b → effectiveAt a i ≤ effectiveAt b i
  beforeFrame : beforeValidator.effectiveBalance.toNat = effectiveAt outer i
  prefixEvents : List (BalanceEvent preset)
  prefixReplay : pre.balanceEvents high = .ok prefixEvents
  gap : preset.downwardBand < beforeValidator.effectiveBalance.toNat -
    ((middle.balances.data[i]?.map UInt64.toNat).getD 0)
  resources : beforeValidator.effectiveBalance.toNat -
      ((middle.balances.data[i]?.map UInt64.toNat).getD 0) ≤
    (effectiveAt x i - actualBalanceAt x i) +
      ((prefixEvents ++ events).map (floorPenaltyDebit i)).sum +
      ((prefixEvents ++ events).map (floorPartialDebit (UInt64.ofNat i))).sum
theorem firstUpdate_of_slot_replay
    {g x outer after y : ForkedBeaconState preset} {tail : Run config checks x y}
    (shared : Run config checks g x) (pre : Run config checks x outer)
    (post : Run config checks after y)
    (ok : advanceSlotAcross config checks outer = .ok after)
    (split : (pre.snoc (.slot ok)).append post = tail)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (early : after.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (located : outer.state.validators.data[i.toNat]? = some u)
    (final : after.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    {advanced : BeaconState preset outer.fork}
    (advanceOk : advanceSlot config checks outer.state = .ok advanced)
    (decreases : effectiveAt ⟨outer.fork, advanced⟩ i.toNat < effectiveAt outer i.toNat)
    (ordered : ∀ j a b, pre.balancePath[j]? = some a →
      pre.balancePath[j + 1]? = some b → effectiveAt a i.toNat ≤ effectiveAt b i.toNat)
    {prefixEvents : List (BalanceEvent preset)}
    (prefixReplay : pre.balanceEvents replayHigh = .ok prefixEvents)
    (short : (getCurrentEpoch outer.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat)
    (endEpoch : (getCurrentEpoch after.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat)
    (noCrossing : ∀ found, (Step.slot ok).balanceEvents = .ok found →
      ∀ e ∈ found, e.source ≠ .crossing)
    {low base quotient : Nat} {account : FloorAccount}
    (trace : FloorTrace low base quotient
      ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ account)
    (balance : account.balance = actualBalanceAt outer i.toNat)
    (unmarked : account.slashedHigh = none)
    (debt : account.debt = (prefixEvents.map (floorPenaltyDebit i.toNat)).sum +
      (prefixEvents.map (floorPartialDebit i)).sum)
    (capped : max low account.high ≤ (withdrawalMaxEffectiveBalance preset outer.fork u).toNat)
    (covered : effectiveAt outer i.toNat ≤ account.high) :
    Nonempty (FirstUpdate tail replayHigh i.toNat) := by
  have outerEarly := Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  obtain ⟨next, cached, epoched, checked, last, cachedOk, epochOk, _finalSlot⟩ :=
    advanceSlot_decrease_last advanceOk decreases
  obtain ⟨middle, updated, events, replay, update, validators, balances⟩ :=
    epochBalanceReplay_result cached epoched outerEarly epochOk
  have finalValidators : advanced.validators = updated.validators := by
    rw [_finalSlot]
    exact validators.symm
  have finalBalances : advanced.balances = middle.balances := by
    rw [_finalSlot]
    exact balances.symm
  have lower : effectiveAt ⟨outer.fork, updated⟩ i.toNat < effectiveAt outer i.toNat := by
    simpa only [effectiveAt, finalValidators] using decreases
  obtain ⟨before, amount, effective, found, owned, afterRead, scalar, smaller, frame, gap⟩ :=
    reachable_update_decrease_gap (shared.append pre) genesis caps aligned outerEarly cachedOk
      epochOk replay update (Array.getElem?_eq_some_iff.mp located).1 lower
  have stepReplay := slot_epoch_events_eq ok cachedOk checked last replay advanceOk noCrossing
  have resource := slot_update_deficit_resources shared pre genesis caps ok early delay
    stepReplay i v u w initial located final unslashed clean short high endEpoch retained
    (noCrossing _ stepReplay) trace balance unmarked debt capped covered advanceOk finalBalances
  refine ⟨{
    outer := outer, after := after, pre := pre, post := post,
    advanced := advanced, cached := cached, middle := middle, updated := updated,
    next := next, stepOk := ok, split := split, nextOk := checked, last := last,
    advancedOk := advanceOk, cachedOk := cachedOk, events := events, replay := replay,
    updateOk := update, finalValidators := finalValidators, beforeValidator := before,
    afterValidator := { before with effectiveBalance := effective }, foundBefore := found,
    foundAfter := afterRead, actualUpdate := ?_, decreases := smaller, noEarlier := ordered,
    beforeFrame := frame, prefixEvents := prefixEvents, prefixReplay := prefixReplay,
    gap := ?_, resources := ?_ }⟩
  · simpa only [owned, Option.getD_some] using scalar
  · simpa only [owned, Option.map_some, Option.getD_some] using gap
  · simpa only [actualBalanceAt, owned, Option.map_some, Option.getD_some, ← frame,
      UInt64.ofNat_toNat] using resource
theorem FirstUpdate.events_prefix
    {x y : ForkedBeaconState preset} {tail : Run config checks x y}
    {events : List (BalanceEvent preset)}
    (first : FirstUpdate tail high i)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (replayed : tail.balanceEvents high = .ok events) :
    (first.prefixEvents ++ first.events) <+: events := by
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp first.stepOk
  have same : advanced = first.advanced := Except.ok.inj (advanceOk.symm.trans first.advancedOk)
  subst advanced
  obtain ⟨crossings, crossingOk, _⟩ := upgradeBalanceReplay_bounded upgrades
  have checked : liftAccessor (liftArith (Uint64.addChecked first.outer.state.slot 1)) =
      (Except.ok first.next : Except TransitionError Slot) := by
    simp [first.nextOk, liftArith, liftAccessor, Except.mapError]
  have stepEvents := Step.balanceEvents_epoch_slot first.stepOk first.cachedOk checked
    first.last first.replay first.advancedOk crossingOk
  have outerEpoch : (getCurrentEpoch first.outer.state).toNat ≤ high + 1 :=
    (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      ((Run.nil.snoc (.slot first.stepOk)).append first.post).chainSteps)).trans endEpoch
  have prefixOk : (first.pre.snoc (.slot first.stepOk)).balanceEvents high =
      .ok (first.prefixEvents ++ (first.events ++ crossings)) := by
    simp only [Run.balanceEvents, first.prefixReplay, outerEpoch, ↓reduceIte,
      stepEvents, bind, Except.bind, pure, Except.pure]
  rw [← first.split] at replayed
  obtain ⟨before, beforeOk, initial⟩ :=
    (first.pre.snoc (.slot first.stepOk)).balanceEvents_prefix first.post high events replayed
  have equal := Except.ok.inj (beforeOk.symm.trans prefixOk)
  rw [equal, ← List.append_assoc] at initial
  exact (List.prefix_append _ _).trans initial
theorem prefix_resource_sum_le {α : Type} (carrier : Finset Nat)
    (parts : Nat → List α) (events : List α) (debit : Nat → α → Nat)
    (included : ∀ i ∈ carrier, parts i <+: events) :
    (∑ i ∈ carrier, ((parts i).map (debit i)).sum) ≤
      (events.map fun event => ∑ i ∈ carrier, debit i event).sum := by
  have point : (∑ i ∈ carrier, ((parts i).map (debit i)).sum) ≤
      ∑ i ∈ carrier, (events.map (debit i)).sum := by
    apply Finset.sum_le_sum
    intro i member
    exact ((included i member).sublist.map _).sum_le_sum (fun _ _ => Nat.zero_le _)
  have swap : (∑ i ∈ carrier, (events.map (debit i)).sum) =
      (events.map fun event => ∑ i ∈ carrier, debit i event).sum := by
    clear included point
    induction events with
    | nil => simp
    | cons event events ih => simp [Finset.sum_add_distrib, ih]
  exact point.trans_eq swap
structure LedgerCuts {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) where
  stops : (i : Nat) → Stop tail i
  cut : Nat → ForkedBeaconState preset
  headRun : (i : Nat) → Run config checks x (cut i)
  suffix : (i : Nat) → Run config checks (cut i) y
  split : ∀ i, (headRun i).append (suffix i) = tail
  retainedCut : ∀ i, (y.state.validators.data[i]?).any (fun v =>
    isActiveValidator v (getCurrentEpoch y.state)) → cut i = y ∧ HEq (headRun i) tail
  stoppedCut : ∀ i, ¬ (y.state.validators.data[i]?).any (fun v =>
    isActiveValidator v (getCurrentEpoch y.state)) →
    cut i = (stops i).state ∧ HEq (headRun i) (stops i).pre
def LedgerCuts.ofStops {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (stops : (i : Nat) → Stop tail i) : LedgerCuts tail := by
  let cuts (i : Nat) : (s : ForkedBeaconState preset) ×
      (pre : Run config checks x s) × {post : Run config checks s y // pre.append post = tail} :=
    if (y.state.validators.data[i]?).any (fun v =>
        isActiveValidator v (getCurrentEpoch y.state)) then
      ⟨y, tail, .nil, rfl⟩
    else ⟨(stops i).state, (stops i).pre, (stops i).post, (stops i).split⟩
  exact {
    stops := stops
    cut := fun i => (cuts i).1
    headRun := fun i => (cuts i).2.1
    suffix := fun i => (cuts i).2.2.val
    split := fun i => (cuts i).2.2.property
    retainedCut := fun i active => by
      dsimp only [cuts]
      rw [ite_eq_left active]
      exact ⟨rfl, HEq.rfl⟩
    stoppedCut := fun i inactive => by
      dsimp only [cuts]
      rw [ite_eq_right inactive]
      exact ⟨rfl, HEq.rfl⟩ }
structure RoundLedger {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : Nat) extends LedgerCuts tail where
  falling : Finset Nat
  exactCarrier : ∀ i, i ∈ falling ↔ i < x.state.validators.data.size ∧
    (x.state.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch x.state) &&
      !v.slashed && decide (v.exitEpoch = FAR_FUTURE_EPOCH ∨ horizonEnd x high < v.exitEpoch.toNat))
        ∧
    ((cut i).state.validators.data[i]?.map (·.slashed)).getD true = false ∧
    FirstDown (headRun i) i
  first : ∀ i, i ∈ falling → FirstUpdate (headRun i) high i
  a : Nat → Nat
  p : Nat → Nat
  exactA : ∀ i (member : i ∈ falling), a i = (effectiveAt x i - actualBalanceAt x i) +
    (((first i member).prefixEvents ++ (first i member).events).map (floorPenaltyDebit i)).sum
  exactP : ∀ i (member : i ∈ falling), p i =
    (((first i member).prefixEvents ++ (first i member).events).map
      (floorPartialDebit (UInt64.ofNat i))).sum
  aBound : (∑ i ∈ falling, a i) ≤
    startSlack x + windowPenalties (config := config) x high (driftHorizon x high + 1)
  pBound : (∑ i ∈ falling, p i) ≤ withdrawalBudget (config := config) x high
  countBound : falling.card ≤
    finalKeyCount preset (referenceStake x) (referenceCount x)
        (stakeCeilingAt config x high (driftHorizon x high + 1))
  roundBound : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * falling.card ≤
    roundingBudget (config := config) x high
  sourceFalling : Finset Nat
  exactSourceCarrier : ∀ i, i ∈ sourceFalling ↔ i < x.state.validators.data.size ∧
    NewReference x i ∧
    ((stops i).state.state.validators.data[i]?.map (·.slashed)).getD true = false ∧
    FirstDown (stops i).pre i
  sourceFirst : ∀ i, i ∈ sourceFalling → FirstUpdate (stops i).pre high i
  sourceA : Nat → Nat
  sourceP : Nat → Nat
  exactSourceA : ∀ i (member : i ∈ sourceFalling), sourceA i =
    (effectiveAt x i - actualBalanceAt x i) +
      (((sourceFirst i member).prefixEvents ++ (sourceFirst i member).events).map
        (floorPenaltyDebit i)).sum
  exactSourceP : ∀ i (member : i ∈ sourceFalling), sourceP i =
    (((sourceFirst i member).prefixEvents ++ (sourceFirst i member).events).map
      (floorPartialDebit (UInt64.ofNat i))).sum
  sourceABound : (∑ i ∈ sourceFalling, sourceA i) ≤
    startSlack x + windowPenalties (config := config) x high (driftHorizon x high + 1)
  sourcePBound : (∑ i ∈ sourceFalling, sourceP i) ≤ withdrawalBudget (config := config) x high
  sourceCountBound : sourceFalling.card ≤
    finalKeyCount preset (referenceStake x) (referenceCount x)
        (stakeCeilingAt config x high (driftHorizon x high + 1))
  sourceRoundBound : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * sourceFalling.card ≤
    roundingBudget (config := config) x high
/-- A sum over keys active at `x` is at most the sum over the active indices. -/
theorem initial_active_sum_le
    {x : ForkedBeaconState preset} (carrier : Finset Nat) (early : x.fork < .glamsterdam)
    (active : ∀ i ∈ carrier, ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true) (f : Nat → Nat) :
    (∑ i ∈ carrier, f i) ≤
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        f i.toNat).sum := by
  have within := x.state.validators.bound early
  have numeric : ∀ i ∈ carrier, (UInt64.ofNat i).toNat = i := by
    intro i member
    obtain ⟨v, found, _⟩ := active i member
    exact toNat_toUInt64_of_lt within (Array.getElem?_eq_some_iff.mp found).1
  have subset : carrier.image UInt64.ofNat ⊆
      (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset := by
    intro index member
    obtain ⟨i, inside, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨v, found, enabled⟩ := active i inside
    apply List.mem_toFinset.mpr
    exact (mem_getActiveValidatorIndices within).mpr
      ⟨v, by simpa only [numeric i inside] using found, enabled⟩
  have unique := (getActiveValidatorIndices_sorted within (getCurrentEpoch x.state)).imp
    (fun {a b} less (same : a = b) => by subst same; exact UInt64.lt_irrefl _ less)
  rw [← List.sum_toFinset _ unique]
  have sumImage : (carrier.image UInt64.ofNat).sum (fun idx => f idx.toNat) =
      ∑ i ∈ carrier, f i := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i member
      rw [numeric i member]
    · intro i hi j hj same
      have equal := congrArg UInt64.toNat same
      simpa only [numeric i hi, numeric j hj] using equal
  rw [← sumImage]
  exact Finset.sum_le_sum_of_subset subset
theorem initial_active_slack_le
    {x : ForkedBeaconState preset} (carrier : Finset Nat) (early : x.fork < .glamsterdam)
    (active : ∀ i ∈ carrier, ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true) :
    (∑ i ∈ carrier, (effectiveAt x i - actualBalanceAt x i)) ≤ startSlack x :=
  initial_active_sum_le carrier early active fun i => effectiveAt x i - actualBalanceAt x i
theorem initial_unslashed_debit_le
    {x : ForkedBeaconState preset} (carrier : Finset Nat) (early : x.fork < .glamsterdam)
    (active : ∀ i ∈ carrier, ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false)
    (debit : Nat → Nat) :
    (∑ i ∈ carrier, debit i) ≤
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else debit i.toNat).sum := by
  have within := x.state.validators.bound early
  have numeric : ∀ i ∈ carrier, (UInt64.ofNat i).toNat = i := by
    intro i member
    obtain ⟨v, found, _⟩ := active i member
    exact toNat_toUInt64_of_lt within (Array.getElem?_eq_some_iff.mp found).1
  have subset : carrier.image UInt64.ofNat ⊆
      (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset := by
    intro index member
    obtain ⟨i, inside, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨v, found, enabled, _⟩ := active i inside
    apply List.mem_toFinset.mpr
    exact (mem_getActiveValidatorIndices within).mpr
      ⟨v, by simpa only [numeric i inside] using found, enabled⟩
  have unique := (getActiveValidatorIndices_sorted within (getCurrentEpoch x.state)).imp
    (fun {a b} less (same : a = b) => by subst same; exact UInt64.lt_irrefl _ less)
  rw [← List.sum_toFinset _ unique]
  have sumImage : (carrier.image UInt64.ofNat).sum (fun idx =>
      if (x.state.validators.data[idx.toNat]?.map (·.slashed)).getD true then 0
        else debit idx.toNat) = ∑ i ∈ carrier, debit i := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i member
      obtain ⟨v, found, _, unslashed⟩ := active i member
      simp [numeric i member, found, unslashed]
    · intro i hi j hj same
      have equal := congrArg UInt64.toNat same
      simpa only [numeric i hi, numeric j hj] using equal
  rw [← sumImage]
  exact Finset.sum_le_sum_of_subset subset
/-- A slot records no withdrawal event: its epoch passes and fork crossings pay no withdrawal. -/
theorem slot_events_no_withdrawals {x y : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks x = .ok y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source ≠ .withdrawals := by
  obtain ⟨advanced, cached, crossings, _, _, _, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  rcases split with ⟨_, rfl⟩ |
    ⟨middle, _, recorded, recordedOk, _, _, _, shape, _, _, _, _, _⟩
  · intro e member source
    have crossed := upgradeBalanceReplay_crossing crossingOk e member
    rw [crossed] at source
    cases source
  · intro e member source
    rw [shape] at member
    rcases List.mem_append.mp member with recordedMember | crossingMember
    · exact epochBalanceReplay_no_withdrawals recordedOk e recordedMember source
    · have crossed := upgradeBalanceReplay_crossing crossingOk e crossingMember
      rw [crossed] at source
      cases source
private theorem slot_partial_sum {x y : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks x = .ok y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events) :
    (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
      floorPartialDebit (UInt64.ofNat i) e).sum = 0 := by
  have absent := slot_events_no_withdrawals ok early replayed
  have each : ∀ e ∈ events,
      (∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e) = 0 := by
    intro e member
    simp [floorPartialDebit, absent e member]
  exact List.sum_eq_zero (by
    intro n member
    obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
    exact each e present)
private theorem partial_calls_le_window (calls : List (IndexedDepartureCall preset config))
    (cutoff : Nat) :
    ((calls.filter fun called => called.index.isNone &&
      decide (called.call.epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        cutoff)).map (·.call.amount.toNat)).sum ≤
    ((calls.filter fun called => called.call.epoch.toNat ≤ cutoff).map
      (·.call.amount.toNat)).sum := by
  induction calls with
  | nil => exact Nat.le_refl _
  | cons called rest ih =>
    by_cases due : called.call.epoch.toNat +
        config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤ cutoff
    · have before : called.call.epoch.toNat ≤ cutoff := by omega
      cases indexed : called.index.isNone <;> simp [due, before, indexed] <;> omega
    · by_cases before : called.call.epoch.toNat ≤ cutoff <;> simp [due, before] <;> omega
private theorem initial_partials_at_L (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) :
    (((x.state.pendingPartialWithdrawals electra).data.toList.filter
      (fun entry => entry.withdrawableEpoch.toNat ≤ horizonEnd x high)).map (·.amount.toNat)).sum =
      duePartialWithdrawals x (driftHorizon x high) := by
  unfold duePartialWithdrawals
  simp only [electra, ↓reduceDIte]
  generalize (x.state.pendingPartialWithdrawals electra).data.toList = entries
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    by_cases due : entry.withdrawableEpoch.toNat ≤ horizonEnd x high
    · simpa [due, horizonEnd] using congrArg (entry.amount.toNat + ·) ih
    · simpa [due, horizonEnd] using ih
private theorem initial_partials_le_Pp (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) :
    (((x.state.pendingPartialWithdrawals electra).data.toList.filter
      (fun entry => entry.withdrawableEpoch.toNat ≤ high + 1)).map (·.amount.toNat)).sum ≤
      duePartialWithdrawals x (driftHorizon x high) := by
  rw [← initial_partials_at_L x high electra]
  have horizon : high + 1 ≤ horizonEnd x high := by unfold horizonEnd driftHorizon; omega
  generalize (x.state.pendingPartialWithdrawals electra).data.toList = entries
  induction entries with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
    by_cases due : entry.withdrawableEpoch.toNat ≤ high + 1
    · have later := due.trans horizon
      simp [due, later]; omega
    · by_cases later : entry.withdrawableEpoch.toNat ≤
        horizonEnd x high <;> simp [due, later] <;> omega
private theorem opened_exit_capacity_le_paid (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) :
    (∑ epoch ∈ Finset.Ico (max (getCurrentEpoch x.state).toNat (exitQueueStart x + 1))
        (horizonEnd x high + 1),
      exitFlowAt (config := config) x high (epoch - (getCurrentEpoch x.state).toNat)) ≤
    (((List.range (driftHorizon x high + 2)).filter
      (max (exitQueueStart x - (getCurrentEpoch x.state).toNat)
        (preElectraEpochs config x high) ≤ ·)).map (exitFlowAt (config := config) x high)).sum := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  have convertSum :
      (((List.range (driftHorizon x high + 2)).filter
        (max (exitQueueStart x - (getCurrentEpoch x.state).toNat)
          (preElectraEpochs config x high) ≤ ·)).map (exitFlowAt (config := config) x high)).sum =
      ∑ t ∈ Finset.range (driftHorizon x high + 2),
        if exitQueueStart x - (getCurrentEpoch x.state).toNat ≤ t then
          exitFlowAt (config := config) x high t else 0 := by
    have sums := List.sum_map_ite
      (fun t => exitQueueStart x - (getCurrentEpoch x.state).toNat ≤ t)
      (exitFlowAt (config := config) x high) (fun _ => 0) (List.range (driftHorizon x high + 2))
    rw [← List.sum_toFinset _ List.nodup_range] at sums
    simpa [zero, List.toFinset_range] using sums.symm
  rw [convertSum]
  refine Finset.sum_le_sum_of_injOn
    (s := Finset.Ico (max (getCurrentEpoch x.state).toNat (exitQueueStart x + 1))
      (horizonEnd x high + 1))
    (t := Finset.range (driftHorizon x high + 2))
    (fun epoch => epoch - (getCurrentEpoch x.state).toNat) ?_ ?_ ?_ ?_
  · intro a ha b hb same
    have ha := Finset.mem_Ico.mp ha
    have hb := Finset.mem_Ico.mp hb
    change a - (getCurrentEpoch x.state).toNat = b - (getCurrentEpoch x.state).toNat at same
    omega
  · intro epoch member
    obtain ⟨original, inside, rfl⟩ := Finset.mem_image.mp member
    have inside := Finset.mem_Ico.mp inside
    simp only [Finset.mem_range]
    unfold horizonEnd at inside
    omega
  · intro epoch member
    simp only [Finset.mem_Ico] at member
    rw [ite_eq_left (by omega)]
  · intro _ _ _
    exact Nat.zero_le _
private theorem exit_trace_le_paid (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) {epoch : Epoch} {left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace (x.state.earliestExitEpoch electra)
      (x.state.exitBalanceToConsume electra) calls epoch left)
    (starts : ∀ call ∈ calls, (getCurrentEpoch x.state).toNat ≤ call.first.toNat)
    (rates : ∀ call ∈ calls, ∀ n, call.first.toNat ≤ n → call.earliest.toNat < n →
      n ≤ call.epoch.toNat → call.rate.toNat ≤
        exitFlowAt (config := config) x high (n - (getCurrentEpoch x.state).toNat)) :
    ((calls.filter fun call => call.epoch.toNat ≤ horizonEnd x high).map (·.amount.toNat)).sum ≤
      withdrawalBudget (config := config) x high -
          duePartialWithdrawals x (driftHorizon x high) := by
  have bound := trace_window_envelope_from trace
    (fun n => exitFlowAt (config := config) x high (n - (getCurrentEpoch x.state).toNat))
    (getCurrentEpoch x.state).toNat (horizonEnd x high) starts rates
  have capacity := opened_exit_capacity_le_paid (config := config) x high electra
  have start : (x.state.earliestExitEpoch electra).toNat = exitQueueStart x := by
    simp [exitQueueStart, electra]
  rw [start] at bound
  by_cases inside : exitQueueStart x ≤ horizonEnd x high
  · rw [ite_eq_left inside] at bound
    simp only
        [withdrawalBudget, dueExitCarry, inside, ↓reduceIte, exitBalanceCarry, electra, ↓reduceDIte]
    omega
  · rw [ite_eq_right inside] at bound
    exact bound.trans (Nat.zero_le _)
theorem exit_rate_le_churn {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) {total rate : Gwei}
    (read : getTotalActiveBalance s = .ok total)
    (computed : exitChurnLimit config s = .ok rate) :
    rate.toNat ≤ activationExitChurn preset config total.toNat := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have value : rate = min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
      (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT))) := by
    simpa [exitChurnLimit, notGloas, getActivationExitChurnLimit,
      getBalanceChurnLimit, read, bind, Except.bind, pure, Except.pure] using computed.symm
  rw [value, Uint64.toNat_min, toNat_roundToIncrement, Uint64.toNat_max, UInt64.toNat_div]
  have share := Nat.div_add_mod (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat)
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  have rounded :
      max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
          (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) -
        max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
          (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ balanceChurn preset config total.toNat := by
    unfold balanceChurn
    rw [Nat.mul_comm (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)]
    rcases Nat.le_total config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) with low | high
    · rw [Nat.max_eq_right low]
      omega
    · rw [Nat.max_eq_left high]
      omega
  exact min_le_min_left _ rounded
theorem exit_churn_mono {low high : Nat} (less : low ≤ high) :
    activationExitChurn preset config low ≤ activationExitChurn preset config high := by
  exact min_le_min_left _
    (max_le_max_left _ (Nat.mul_le_mul_right _
      (Nat.div_le_div_right (Nat.div_le_div_right less))))
private theorem exit_site_opened_rate (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) {total rate : Gwei}
    (read : getTotalActiveBalance s = .ok total)
    (computed : exitChurnLimit config s = .ok rate) (atEpoch : Nat)
    (ceiling : total.toNat ≤ stakeCeilingAt config x high atEpoch) :
    ∀ n, atEpoch ≤ n - (getCurrentEpoch x.state).toNat →
      rate.toNat ≤ exitFlowAt (config := config) x high (n - (getCurrentEpoch x.state).toNat) := by
  intro n later
  have rateBound := exit_rate_le_churn early read computed
  have stake := ceiling.trans (ceilingAt_mono (config := config) electra high later)
  have bound := rateBound.trans (exit_churn_mono (config := config) stake)
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  simpa only [exitFlowAt, exitFlow, zero, Nat.not_lt_zero, ↓reduceIte] using bound
private theorem exit_call_opened_rate (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) (call : DepartureQueueCall)
    (first : computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first)
    (computed : exitChurnLimit config s = .ok call.rate) {total : Gwei}
    (read : getTotalActiveBalance s = .ok total)
    (ceiling : total.toNat ≤ stakeCeilingAt config x high
      ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat)) :
    ∀ n, call.first.toNat ≤ n → call.earliest.toNat < n → n ≤ call.epoch.toNat →
      call.rate.toNat ≤ exitFlowAt (config := config) x high
        (n - (getCurrentEpoch x.state).toNat) := by
  intro n opened _ _
  have firstEpoch := (computeActivationExitEpoch_ok_iff.mp first).2
  apply exit_site_opened_rate x high electra early read computed _ ceiling n
  omega
private theorem run_partials_le_paid (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) {y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ horizonEnd x high)
    (ceilings : ∀ {u v} (step : Step config checks u v), tail.Contains step →
      ∀ total, getTotalActiveBalance u.state = .ok total → total.toNat ≤
        stakeCeilingAt config x high
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)) :
    (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
      floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high := by
  obtain ⟨calls, trace, firsts, rates, partials⟩ := run_partial_queue_trace
    (partialDebit := floorPartialDebit)
    (ceilingValue := stakeCeilingAt config x high)
    (exitEnvelope := exitFlowAt (config := config) x high)
    (callRate := exit_call_opened_rate x high electra)
    (partialDebit_eq := rfl) (slot_zero := slot_partial_sum)
    high (horizonEnd x high) electra tail early replayed endpoint ceilings
  rw [initial_partials_at_L x high electra] at partials
  have selected := partial_calls_le_window calls (horizonEnd x high)
  have capacity := exit_trace_le_paid x high electra trace
    (by
      intro call member
      obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
      exact firsts called present)
    (by
      intro call member
      obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
      exact rates called present)
  have mapped : (((calls.map (·.call)).filter fun call => call.epoch.toNat ≤ horizonEnd x high).map
      (·.amount.toNat)).sum =
      ((calls.filter fun called => called.call.epoch.toNat ≤ horizonEnd x high).map
        (·.call.amount.toNat)).sum := by
    rw [List.filter_map, List.map_map]
    rfl
  rw [mapped] at capacity
  have included : duePartialWithdrawals x (driftHorizon x high) ≤
      withdrawalBudget (config := config) x high := by
    unfold withdrawalBudget
    omega
  omega
private theorem run_partials_le_paid_of_stake (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) {y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ horizonEnd x high)
    (stake : ∀ {u v} (step : Step config checks u v), tail.Contains step →
      ∑ i ∈ (getActiveValidatorIndices u.state (getCurrentEpoch u.state)).toFinset,
        effectiveAt u i.toNat ≤ stakeCeilingAt config x high
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat))
    (unit : ∀ {u v} (step : Step config checks u v), tail.Contains step →
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high
        ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)) :
    (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
      floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high := by
  apply run_partials_le_paid x high electra tail early replayed endpoint
  intro u v step member total read
  have value := (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok read)).2.2
  rw [value]
  exact max_le (unit step member) (stake step member)
theorem run_partials_le_paid_of_endpoint_floor
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high : Nat)
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
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
      floorPartialDebit (UInt64.ofNat i) e).sum ≤ withdrawalBudget (config := config) x high := by
  have contained {u v} (step : Step config checks u v) (member : tail.Contains step) :
      u.fork < .glamsterdam ∧
      (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch y.state).toNat ∧
      (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat ≤
        driftHorizon x high + 1 := by
    obtain ⟨_, _, _, uEarly, order⟩ := Run.contains_step_facts member early
    refine ⟨uEarly, order, ?_⟩
    unfold driftHorizon
    omega
  apply run_partials_le_paid_of_stake x high electra tail early replayed
    (endpoint.trans (by unfold horizonEnd driftHorizon; omega))
  · intro u v step member
    obtain ⟨pre, _, _⟩ := tail.contains_split step member
    have bounds := contained step member
    exact (activeStake_le_ceiling shared genesis pre electra bounds.1 high
      (bounds.2.1.trans endpoint) guard maxAligned unit others
      (fun path pathEarly earlier total read => floor path pathEarly
        (earlier.trans_le bounds.2.1) total read)).1
  · intro u v step member
    exact unit.trans (ceilingAt_mono electra high (Nat.zero_le _))
private theorem run_joint_departures_high_scalar (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) {y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (ceilings : ∀ {u v} (step : Step config checks u v), tail.Contains step →
      ∀ total, getTotalActiveBalance u.state = .ok total → total.toNat ≤
        stakeCeilingAt config x high
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)) :
    ((tail.departureCharges.filter fun charge => charge.epoch ≤ high + 1).map (·.amount)).sum +
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ duePartialWithdrawals x (driftHorizon x high) +
          queueCarry x high +
      (high + 2 - max (getCurrentEpoch x.state).toNat (exitQueueStart x)) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
      (high + 2 - max (getCurrentEpoch x.state).toNat (consolidationQueueStart x)) *
        consolidationFlowAt (config := config) x high 0 := by
  have initial := initial_partials_le_Pp x high electra
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  have bound :=
      run_joint_partial_window (partialDebit := floorPartialDebit) (partialDebit_eq := rfl)
    (slot_zero := slot_partial_sum) tail electra early replayed endpoint
    (consolidationFlowAt (config := config) x high 0) (by
      intro u v step member _ total read rate computed
      obtain ⟨_, _, _, sourceEarly, epochOrder⟩ := Run.contains_step_facts member early
      have index : (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat ≤
          driftHorizon x high + 1 := by
        unfold driftHorizon
        omega
      have bound := (consolidationChurnLimit_le sourceEarly read computed).trans
        (consolidationChurn_mono ((ceilings step member total read).trans
          (ceilingAt_mono electra high index)))
      simpa only [consolidationFlowAt, consolidationFlow, zero, Nat.lt_irrefl, ↓reduceIte]
          using bound)
  simp only [queueCarry, exitQueueStart, consolidationQueueStart, electra, ↓reduceDIte]
  omega
private theorem run_joint_departures_high_budget (x : ForkedBeaconState preset) (high : Nat)
    (electra : .pectra ≤ x.fork) {y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (ceilings : ∀ {u v} (step : Step config checks u v), tail.Contains step →
      ∀ total, getTotalActiveBalance u.state = .ok total → total.toNat ≤
        stakeCeilingAt config x high
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)) :
    ((tail.departureCharges.filter fun charge => charge.epoch ≤ high + 1).map (·.amount)).sum +
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ departureBudgetAt (config := config) x high +
          duePartialWithdrawals x (driftHorizon x high) := by
  have bound :=
      run_joint_departures_high_scalar x high electra tail early replayed endpoint ceilings
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  have from_ (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat start ≤
      driftHorizon x high + 2 - (start - (getCurrentEpoch x.state).toNat) := by
    unfold driftHorizon
    omega
  have exitTerm := Nat.mul_le_mul_right
    config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (from_ (exitQueueStart x))
  have consolidationTerm := Nat.mul_le_mul_right
    (consolidationFlowAt (config := config) x high 0) (from_ (consolidationQueueStart x))
  simp only [departureBudgetAt, departureBudget, zero, lt_self_iff_false, ↓reduceIte]
  simp only [consolidationFlowAt, consolidationFlow, zero, Nat.lt_irrefl, ↓reduceIte]
    at bound consolidationTerm
  simp only [stakeCeilingAt] at bound exitTerm consolidationTerm ⊢
  simp only [zero] at bound consolidationTerm
  omega
/-- Each step of a branch starts where the total active balance fits the ceiling of its epoch. -/
theorem stepTotal_le_ceiling {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high : Nat)
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
    {u v : ForkedBeaconState preset} (step : Step config checks u v) (member : tail.Contains step)
    {total : Gwei} (read : getTotalActiveBalance u.state = .ok total) :
    total.toNat ≤ stakeCeilingAt config x high
      ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) := by
  obtain ⟨pre, _, _, uEarly, epochOrder⟩ := Run.contains_step_facts member early
  have stake := (activeStake_le_ceiling shared genesis pre electra uEarly high
    (epochOrder.trans endpoint) guard maxAligned unit others
    (fun path pathEarly earlier total read =>
      floor path pathEarly (earlier.trans_le epochOrder) total read)).1
  have value := (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok read)).2.2
  rw [value]
  exact max_le (unit.trans (ceilingAt_mono electra high (Nat.zero_le _))) stake

private theorem run_joint_departures_budget_of_ceiling {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high : Nat)
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
    ((tail.departureCharges.filter fun charge => charge.epoch ≤ high + 1).map (·.amount)).sum +
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum ≤ departureBudgetAt (config := config) x high +
          duePartialWithdrawals x (driftHorizon x high) := by
  exact run_joint_departures_high_budget x high electra tail early replayed endpoint
    (fun step member _ read => stepTotal_le_ceiling shared genesis tail electra early high endpoint
      guard maxAligned unit others floor step member read)
theorem stopped_charges_le_run {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (stops : (i : Nat) → Stop tail i)
    (carrier : Finset Nat) (charge : Nat → Nat) (cutoff : Nat)
    (selected : ∀ i ∈ carrier, ∃ c, (stops i).charge = some c ∧
      charge i = c.amount ∧ c.epoch ≤ cutoff) :
    (∑ i ∈ carrier, charge i) ≤
      ((tail.departureCharges.filter fun c => c.epoch ≤ cutoff).map (·.amount)).sum := by
  by_cases empty : carrier = ∅
  · simp [empty]
  obtain ⟨seed, seedMember⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have position (i : Nat) (member : i ∈ carrier) :
      ∃ j : Fin tail.departureCharges.length,
        tail.departureCharges[j].index = i ∧
        tail.departureCharges[j].amount = charge i ∧
        tail.departureCharges[j].epoch ≤ cutoff := by
    obtain ⟨c, chosen, amount, before⟩ := selected i member
    have actual := (stops i).selected
    rw [chosen] at actual
    obtain ⟨j, inside, atIndex⟩ := List.getElem_of_mem actual.1
    refine ⟨⟨j, inside⟩, ?_⟩
    change tail.departureCharges[j].index = i ∧
      tail.departureCharges[j].amount = charge i ∧ tail.departureCharges[j].epoch ≤ cutoff
    rw [atIndex]
    exact ⟨actual.2.1, amount.symm, before⟩
  choose pick paired using position
  let injection (i : Nat) : Fin tail.departureCharges.length :=
    if member : i ∈ carrier then pick i member else pick seed seedMember
  have bound := Finset.sum_le_sum_of_injOn
    (s := carrier) (t := Finset.univ) injection
    (f := charge)
    (g := fun j : Fin tail.departureCharges.length =>
      if tail.departureCharges[j].epoch ≤ cutoff then tail.departureCharges[j].amount else 0)
    (by
      intro i hi j hj same
      have left := (paired i hi).1
      have right := (paired j hj).1
      have hi' : i ∈ carrier := hi
      have hj' : j ∈ carrier := hj
      simp only [injection, dite_eq_left hi', dite_eq_left hj'] at same
      rw [same] at left
      exact left.symm.trans right)
    (by simp)
    (by
      intro i member
      simp only [injection, dite_eq_left member, (paired i member).2.2, ↓reduceIte,
        (paired i member).2.1]
      exact Nat.le_refl _)
    (fun _ _ _ => Nat.zero_le _)
  have sums : (∑ j : Fin tail.departureCharges.length,
      if tail.departureCharges[j].epoch ≤ cutoff then tail.departureCharges[j].amount else 0) =
      ((tail.departureCharges.filter fun c => c.epoch ≤ cutoff).map (·.amount)).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn (fun j : Fin tail.departureCharges.length =>
      if tail.departureCharges[j.val].epoch ≤ cutoff then
        tail.departureCharges[j.val].amount else 0)).sum = _
    rw [List.ofFn_getElem_eq_map tail.departureCharges
      (fun c => if c.epoch ≤ cutoff then c.amount else 0)]
    simpa using List.sum_map_ite (fun c : DepartureCharge => c.epoch ≤ cutoff)
      (·.amount) (fun _ => 0) tail.departureCharges
  exact bound.trans_eq sums
private theorem Stop.charge_endpoint {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {i : Nat} (stop : Stop tail i)
    {c : DepartureCharge} (selected : stop.charge = some c) :
    ∃ w, y.state.validators.data[i]? = some w ∧ w.exitEpoch.toNat = c.epoch := by
  have actual := stop.selected
  rw [selected] at actual
  obtain ⟨next, step, rest, _, _, v, w, _, found, _, assigned, epoch⟩ := actual.2.2.2
  obtain ⟨last, lastFound, kept⟩ := rest.registryLifecycle.validators i w found
  exact ⟨last, lastFound, by rw [kept.exitEpoch assigned]; exact epoch⟩
theorem Stop.charge_cutoff {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {i : Nat} (stop : Stop tail i)
    {c : DepartureCharge} (selected : stop.charge = some c) (cutoff : Nat)
    (endpoint : ∃ w, y.state.validators.data[i]? = some w ∧ w.exitEpoch.toNat ≤ cutoff) :
    c.epoch ≤ cutoff := by
  obtain ⟨w, found, epoch⟩ := stop.charge_endpoint selected
  obtain ⟨v, read, before⟩ := endpoint
  have same := Option.some.inj (found.symm.trans read)
  subst v
  omega
theorem initial_active_exit_cutoff {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {i : Nat} {v w : Validator}
    (initial : x.state.validators.data[i]? = some v)
    (active : isActiveValidator v (getCurrentEpoch x.state) = true)
    (final : y.state.validators.data[i]? = some w)
    (inactive : isActiveValidator w (getCurrentEpoch y.state) = false) :
    w.exitEpoch.toNat ≤ (getCurrentEpoch y.state).toNat := by
  obtain ⟨later, found, kept⟩ := tail.registryLifecycle.validators i v initial
  have same := Option.some.inj (found.symm.trans final)
  subst later
  have chronological := currentEpoch_le_of_chainSteps tail.chainSteps
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  have activationStart := UInt64.le_iff_toNat_le.mp active.1
  have exitStart := UInt64.lt_iff_toNat_lt.mp active.2
  have assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    have bound := activationStart.trans_lt exitStart
    rw [far] at bound
    have largest : v.exitEpoch.toNat ≤ FAR_FUTURE_EPOCH.toNat :=
      Nat.le_sub_one_of_lt v.exitEpoch.toNat_lt
    omega
  have activation : w.activationEpoch ≤ getCurrentEpoch y.state := by
    rw [kept.activationEpoch assigned]
    exact UInt64.le_iff_toNat_le.mpr
      (activationStart.trans (UInt64.le_iff_toNat_le.mp chronological))
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not] at inactive
  rcases inactive with before | after
  · exact False.elim (before activation)
  · exact UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp after)
theorem Stop.inactive_charge_cutoff {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {i : Nat} (stop : Stop tail i)
    {c : DepartureCharge} (selected : stop.charge = some c)
    (initial : ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true)
    (inactive : (y.state.validators.data[i]?).any
      (fun w => isActiveValidator w (getCurrentEpoch y.state)) = false) :
    c.epoch ≤ (getCurrentEpoch y.state).toNat := by
  obtain ⟨v, before, active⟩ := initial
  obtain ⟨w, found, _⟩ := stop.charge_endpoint selected
  have noActive : isActiveValidator w (getCurrentEpoch y.state) = false := by
    simpa only [found, Option.any_some] using inactive
  exact stop.charge_cutoff selected _ ⟨w, found,
    initial_active_exit_cutoff tail before active found noActive⟩
theorem stopped_partial_occurrences {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (replayed : tail.balanceEvents high = .ok events)
    (carrier : Finset Nat) (parts : Nat → List (BalanceEvent preset))
    (indices : ∀ i ∈ carrier, i < x.state.validators.data.size)
    (prefixes : ∀ i ∈ carrier, parts i <+: events) :
    (∑ i ∈ carrier, ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) ≤
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum := by
  have prefixBound := prefix_resource_sum_le carrier parts events
    (fun i => floorPartialDebit (UInt64.ofNat i)) prefixes
  have subset (e : BalanceEvent preset) (member : e ∈ events) :
      carrier ⊆ Finset.range e.before.state.validators.data.size := by
    have life := (replay_event_provenance shared tail genesis early high endEpoch
      events replayed e member).1
    intro i inside
    exact Finset.mem_range.mpr ((indices i inside).trans_le life.size_le)
  have bound : (events.map fun e => ∑ i ∈ carrier,
      floorPartialDebit (UInt64.ofNat i) e).sum ≤
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum := by
    clear prefixes prefixBound replayed
    induction events with
    | nil => simp
    | cons e events ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (Finset.sum_le_sum_of_subset (subset e (by simp)))
        (ih (fun e member => subset e (by simp [member])))
  exact prefixBound.trans bound
theorem stopped_joint_budget_of_ceiling {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high : Nat)
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
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (stops : (i : Nat) → Stop tail i) (carrier : Finset Nat) (charge : Nat → Nat)
    (selected : ∀ i ∈ carrier, ∃ c, (stops i).charge = some c ∧
      charge i = c.amount ∧ c.epoch ≤ high + 1)
    (partialTotal : Nat)
    (partialBudget : partialTotal ≤ (events.map fun e =>
      ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum) :
    (∑ i ∈ carrier, charge i) + partialTotal ≤ departureBudgetAt (config := config) x high +
        duePartialWithdrawals x (driftHorizon x high) := by
  have selectedBound := stopped_charges_le_run tail stops carrier charge (high + 1) selected
  have joint := run_joint_departures_budget_of_ceiling shared genesis tail electra early high
    endpoint guard maxAligned unit others floor replayed
  omega
theorem Stop.charge_of_new_exit {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {i : Nat} (stop : Stop tail i)
    {v w : Validator} (initial : x.state.validators.data[i]? = some v)
    (final : y.state.validators.data[i]? = some w)
    (unset : v.exitEpoch = FAR_FUTURE_EPOCH) (assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ c, stop.charge = some c ∧ c.amount = effectiveAt stop.state i := by
  obtain ⟨actual, member, index, _⟩ :=
    tail.departure_charge_of_assigned i v w initial final unset assigned
  cases chosen : stop.charge with
  | none =>
    have absent := stop.selected
    rw [chosen] at absent
    exact False.elim (absent.2 actual member index)
  | some c =>
    have selected := stop.selected
    rw [chosen] at selected
    exact ⟨c, rfl, selected.2.2.1⟩
theorem initial_active_carrier_card_le
    {x : ForkedBeaconState preset} (carrier : Finset Nat)
    (unique : PubkeysDistinct x.state) (early : x.fork < .glamsterdam)
    (active : ∀ i ∈ carrier, ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true) :
    carrier.card ≤ referenceCount x := by
  let key : Nat → BLSPubkey := keyAt x.state
  apply Finset.card_le_card_of_injOn key
  · intro i member
    obtain ⟨v, found, enabled⟩ := active i member
    apply (mem_keysAt_epoch early _ _).mpr
    exact ⟨i, v, found, by simp [key, keyAt, found], enabled⟩
  · intro i hi j hj same
    obtain ⟨v, found, _⟩ := active i hi
    obtain ⟨w, read, _⟩ := active j hj
    exact unique.index_eq found read (by simpa [key, keyAt, found, read] using same)
theorem carrier_resource_count_le (carrier : Finset Nat) (a p : Nat → Nat)
    (band budgetA budgetP : Nat) (positive : 0 < band)
    (gap : ∀ i ∈ carrier, band < a i + p i)
    (aBound : (∑ i ∈ carrier, a i) ≤ budgetA)
    (pBound : (∑ i ∈ carrier, p i) ≤ budgetP) :
    carrier.card ≤ (budgetA + budgetP) / band := by
  apply (Nat.le_div_iff_mul_le positive).mpr
  calc
    carrier.card * band = ∑ _i ∈ carrier, band := by simp
    _ ≤ ∑ i ∈ carrier, (a i + p i) :=
      Finset.sum_le_sum fun i member => Nat.le_of_lt (gap i member)
    _ = (∑ i ∈ carrier, a i) + ∑ i ∈ carrier, p i := Finset.sum_add_distrib
    _ ≤ budgetA + budgetP := Nat.add_le_add aBound pBound
private theorem ReservedReplay.selected_source_round_bound
    {tagged : List (TaggedEntry × Payment preset)}
    {tail : Run config checks x y}
    (ledger : RoundLedger (config := config) (checks := checks) tail high)
    (history : ReservedReplay (config := config) (checks := checks) x high
      (fun i => if i ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after)
    (select : (TaggedEntry × Payment preset) × OwnedRelease → Bool) :
    tagged.length = allocations.length ∧
      (((tagged.zip allocations).filter select).map fun pair => pair.2.sourceRound).sum ≤
        roundingBudget (config := config) x high := by
  have bound := history.selected_round_sum_le ledger.sourceFalling
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat select
  exact ⟨bound.1, bound.2.trans ledger.sourceRoundBound⟩
theorem ReservedReplay.fresh_source_round_bound
    {tagged : List (TaggedEntry × Payment preset)}
    {tail : Run config checks x y}
    (ledger : RoundLedger (config := config) (checks := checks) tail high)
    (history : ReservedReplay (config := config) (checks := checks) x high
      (fun i => if i ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
      x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0
      events queue final tagged allocations calls before after)
    (freshAllocations : List OwnedRelease)
    (projection : freshAllocations = ((tagged.zip allocations).filter fun pair =>
      pair.1.1.tag.isFresh).map Prod.snd) :
    (freshAllocations.map (·.sourceRound)).sum ≤ roundingBudget (config := config) x high := by
  rw [projection, List.map_map]
  exact (history.selected_source_round_bound ledger
    (fun pair => pair.1.1.tag.isFresh)).2
theorem ReservedReplay.fresh_baseline_sum_le
    {tagged : List (TaggedEntry × Payment preset)}
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      start startEpoch finish finishEpoch eventPosition paymentPosition callPosition
      events queue final tagged allocations calls before after) :
    let fresh := (tagged.zip allocations).filter fun pair =>
      pair.1.1.tag.isFresh
    (fresh.map fun pair => pair.2.baseline).sum ≤
      (fresh.map fun pair => pair.1.1.amount).sum +
        (fresh.map fun pair => pair.2.sourceRound).sum := by
  dsimp only
  rw [← List.sum_map_add]
  apply List.sum_le_sum
  intro pair member
  have paired := List.forall₂_zip history.paired_baselines (List.mem_filter.mp member).1
  have selected := (List.mem_filter.mp member).2
  cases tagEq : pair.1.1.tag <;> simp_all

end RunContracts

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
