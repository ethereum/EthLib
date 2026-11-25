module

import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
import Mathlib.Algebra.Order.Floor.Div
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.EventsKept
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.SlashFloor

@[expose] public section

namespace EthLib.Consensus.Models.Network

open DirectSafety.Apriori.Internal (recordBalance_single)

section

/-! ## The credits of one key along a run -/

namespace PinDrift.Internal

open Base Uint64 Models DirectSafety

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The credit of key `i` in one replayed event. -/
def keyCredit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.after i - actualBalanceAt e.before i

/-- The credits to the key in one step, from the sources that count at that kind of step. -/
def stepCredit (blockP slotP : BalanceSource → Bool) (v : ℕ)
    {x y : ForkedBeaconState preset} (step : Step config checks x y) : ℕ :=
  let events := step.balanceEvents.toOption.getD []
  match step with
  | .slot _ => ((events.filter (slotP ·.source)).map (PinDrift.Internal.keyCredit v)).sum
  | .block .. => ((events.filter (blockP ·.source)).map (PinDrift.Internal.keyCredit v)).sum

/-- The credits to the key over a run.

The scan includes only steps that start by epoch `high + 1`. -/
def creditScan (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ
  | _, .nil => 0
  | _, .snoc (middle := m) pre step =>
    let before := PinDrift.Internal.creditScan blockP slotP v high pre
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      before + PinDrift.Internal.stepCredit blockP slotP v step
    else before

/-- The credits that a scan reads from a run, after one more step. -/
theorem creditScan_snoc (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m y) :
    PinDrift.Internal.creditScan blockP slotP v high (pre.snoc step) =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        PinDrift.Internal.creditScan blockP slotP v high pre + PinDrift.Internal.stepCredit blockP
          slotP v step
      else PinDrift.Internal.creditScan blockP slotP v high pre := rfl

/-- The credits to a key in two consecutive runs add. -/
theorem creditScan_append (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (post : Run config checks m y) :
    (PinDrift.Internal.creditScan blockP slotP v high (pre.append post)) =
      (PinDrift.Internal.creditScan blockP slotP v high pre) + (PinDrift.Internal.creditScan blockP
        slotP v high post) := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change (PinDrift.Internal.creditScan blockP slotP v high ((pre.append post).snoc step)) = _
    rw [PinDrift.Internal.creditScan_snoc, PinDrift.Internal.creditScan_snoc]
    split
    · omega
    · exact ih

/-- The credits that a scan reads are 0 if each step of the run credits 0. -/
theorem creditScan_eq_zero_of_steps (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (zero : ∀ {m n : ForkedBeaconState preset} (step : Step config checks m n),
      tail.Contains step → PinDrift.Internal.stepCredit blockP slotP v step = 0) :
    (PinDrift.Internal.creditScan blockP slotP v high tail) = 0 := by
  induction tail with
  | nil => rfl
  | @snoc m n pre step ih =>
    have prior := ih fun inner member => zero inner (.earlier member step)
    have here := zero step (.last pre step)
    rw [PinDrift.Internal.creditScan_snoc]
    split <;> omega

/-- The credits of a list of events from one source set are at most those from a larger set. -/
private theorem sum_filter_credit_le (p q : BalanceSource → Bool)
    (sub : ∀ s, p s = true → q s = true) (v : ℕ) (L : List (BalanceEvent preset)) :
    ((L.filter (p ·.source)).map (PinDrift.Internal.keyCredit v)).sum ≤
      ((L.filter (q ·.source)).map (PinDrift.Internal.keyCredit v)).sum := by
  induction L with
  | nil => simp
  | cons e rest ih =>
    by_cases inP : p e.source = true
    · have inQ := sub _ inP
      simp only [List.filter_cons, inP, inQ, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · by_cases inQ : q e.source = true
      · simp only [List.filter_cons, inP, inQ, Bool.false_eq_true, ↓reduceIte, List.map_cons,
          List.sum_cons]
        omega
      · simp only [List.filter_cons, inP, inQ, Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- The credits of a set of keys over a run, read as a scan, fit one bound per replayed event. -/
theorem creditScan_bounds {ι : Type} (S : Finset ι) (key : ι → ℕ)
    (blockP slotP : BalanceSource → Bool) (high : ℕ) (T : BalanceEvent preset → ℕ)
    {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (each : ∀ e ∈ events, (blockP e.source = true ∨ slotP e.source = true) →
      ∑ v ∈ S, PinDrift.Internal.keyCredit (key v) e ≤ T e) :
    -- A block step counts the events of `blockP`.
    --
    -- A slot step counts the events of `slotP`.
    --
    -- So an event of the run is counted at most once.
    (∑ v ∈ S, (PinDrift.Internal.creditScan blockP slotP (key v) high tail) ≤
      (events.map fun e =>
        if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum) ∧
    -- The credits of a key from a source set `src` over the events are at most its scan.
    --
    -- Each kind of step either counts all of `src`, or records no credit from `src`.
    --
    -- That holds for a run from Electra to before Glamsterdam.
    (∀ src : BalanceSource → Bool,
      ((∀ s, src s = true → blockP s = true) ∨
        ∀ {f : Fork} {u w : BeaconState preset f} {engine : ExecutionEngine preset f}
          {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, u⟩ = false}
          {ok : applySignedBlock config checks engine u signed true = .ok w}
          {es : List (BalanceEvent preset)}, .pectra ≤ f → f < .glamsterdam →
          (Step.block engine signed due ok : Step config checks ⟨f, u⟩ ⟨f, w⟩).balanceEvents =
            .ok es → ∀ i, ((es.filter (src ·.source)).map (PinDrift.Internal.keyCredit i)).sum = 0)
              →
      ((∀ s, src s = true → slotP s = true) ∨
        ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
          {es : List (BalanceEvent preset)}, .pectra ≤ u.fork → w.fork < .glamsterdam →
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
            ∀ i, ((es.filter (src ·.source)).map (PinDrift.Internal.keyCredit i)).sum = 0) →
      .pectra ≤ x.fork → y.fork < .glamsterdam →
      ∀ v, ((events.filter (src ·.source)).map (PinDrift.Internal.keyCredit v)).sum ≤
        (PinDrift.Internal.creditScan blockP slotP v high tail)) := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    exact ⟨Nat.le_zero.mpr (Finset.sum_eq_zero fun v _ => rfl), fun _ _ _ _ _ v => by simp⟩
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      obtain ⟨previous, previousSrc⟩ :=
        ih priorOk fun e member => each e (List.mem_append_left _ member)
      have swap (L : List (BalanceEvent preset)) : ∑ v ∈ S, (L.map (PinDrift.Internal.keyCredit (key
        v))).sum =
          (L.map fun e => ∑ v ∈ S, PinDrift.Internal.keyCredit (key v) e).sum := by
        simpa using (Multiset.sum_map_sum (m := (L : Multiset (BalanceEvent preset)))
          (s := S) (f := fun e v => PinDrift.Internal.keyCredit (key v) e)).symm
      have part (p : BalanceSource → Bool)
          (sub : ∀ s, p s = true → blockP s = true ∨ slotP s = true) :
          ∑ v ∈ S, ((added.filter fun x => p x.source).map (PinDrift.Internal.keyCredit (key
            v))).sum ≤
            (added.map fun e =>
              if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum := by
        rw [swap]
        calc ((added.filter fun x => p x.source).map fun e => ∑ v ∈ S, PinDrift.Internal.keyCredit
          (key v) e).sum
            ≤ ((added.filter fun x => p x.source).map T).sum := List.sum_le_sum fun e member =>
              each e (List.mem_append_right _ (List.mem_filter.mp member).1)
                (sub _ (by simpa using (List.mem_filter.mp member).2))
          _ = (added.map fun e => if p e.source = true then T e else 0).sum := by
              rw [List.sum_map_ite (fun e : BalanceEvent preset => p e.source = true) T
                (fun _ => 0)]
              simp
          _ ≤ _ := List.sum_le_sum fun e _ => by
              by_cases hp : p e.source = true
              · have := sub _ hp
                simp [hp, this]
              · simp [hp]
      have step_le : ∑ v ∈ S, PinDrift.Internal.stepCredit blockP slotP (key v) step ≤
          (added.map fun e =>
            if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum := by
        cases step with
        | slot ok =>
          simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
          exact part slotP fun _ h => Or.inr h
        | block engine signed due ok =>
          simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
          exact part blockP fun _ h => Or.inl h
      refine ⟨?_, fun src blockKind slotKind electra early v => ?_⟩
      · simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte, Finset.sum_add_distrib,
          List.map_append, List.sum_append]
        omega
      · have prior := previousSrc src blockKind slotKind electra
          (Nat.lt_of_le_of_lt step.chainStep.fork_le early) v
        have stepSrc : ((added.filter (src ·.source)).map (PinDrift.Internal.keyCredit v)).sum ≤
            PinDrift.Internal.stepCredit blockP slotP v step := by
          have inRun := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
          cases step with
          | slot ok =>
            simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
            rcases slotKind with covered | quiet
            · exact sum_filter_credit_le src slotP covered v added
            · rw [quiet ok inRun early addedOk v]
              exact Nat.zero_le _
          | block engine signed due ok =>
            simp only [PinDrift.Internal.stepCredit, addedOk, Except.toOption, Option.getD_some]
            rcases blockKind with covered | quiet
            · exact sum_filter_credit_le src blockP covered v added
            · rw [quiet inRun early addedOk v]
              exact Nat.zero_le _
        simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte, List.filter_append,
          List.map_append,
          List.sum_append]
        omega
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      obtain rfl := rest
      obtain ⟨previous, previousSrc⟩ := ih priorOk each
      refine ⟨?_, fun src blockKind slotKind electra early v => ?_⟩
      · simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte]
        exact previous
      · simp only [PinDrift.Internal.creditScan_snoc, selected, ↓reduceIte]
        exact previousSrc src blockKind slotKind electra
          (Nat.lt_of_le_of_lt step.chainStep.fork_le early) v

/-- The credits of a set of keys over a run, read as a scan, fit one bound for each replayed event.

A block step counts the events of `blockP`.

A slot step counts the events of `slotP`.

So an event of the run is counted at most once. -/
theorem creditScan_sum_le {ι : Type} (S : Finset ι) (key : ι → ℕ)
    (blockP slotP : BalanceSource → Bool) (high : ℕ) (T : BalanceEvent preset → ℕ)
    {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (each : ∀ e ∈ events, (blockP e.source = true ∨ slotP e.source = true) →
      ∑ v ∈ S, PinDrift.Internal.keyCredit (key v) e ≤ T e) :
    ∑ v ∈ S, (PinDrift.Internal.creditScan blockP slotP (key v) high tail) ≤
      (events.map fun e =>
        if blockP e.source = true ∨ slotP e.source = true then T e else 0).sum :=
  (PinDrift.Internal.creditScan_bounds S key blockP slotP high T tail replayed each).1

/-- The net rise of a key in one step.

A block step counts the rise of the key's balance across it, and a slot step counts nothing. -/
def stepNet (v : ℕ) {x y : ForkedBeaconState preset} (step : Step config checks x y) : ℕ :=
  match step with
  | .block .. => actualBalanceAt y v - actualBalanceAt x v
  | .slot _ => 0

/-- The net credits to the key in the block steps of a run.

A block step counts the rise of the key's balance across the whole step.

A credit that the same step takes back counts for nothing.

The scan includes only steps that start by epoch `high + 1`. -/
def netScan (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → ℕ
  | _, .nil => 0
  | _, .snoc (middle := m) pre step =>
    if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      PinDrift.Internal.netScan v high pre + PinDrift.Internal.stepNet v step
    else PinDrift.Internal.netScan v high pre

/-- The net credits to a key in the block steps of a run, after one more step. -/
theorem netScan_snoc (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m y) :
    PinDrift.Internal.netScan v high (pre.snoc step) =
      if (getCurrentEpoch m.state).toNat ≤ high + 1 then
        PinDrift.Internal.netScan v high pre + PinDrift.Internal.stepNet v step
      else PinDrift.Internal.netScan v high pre := rfl

/-- A run with no step has no net credits. -/
theorem netScan_nil (v high : ℕ) {x : ForkedBeaconState preset} :
    PinDrift.Internal.netScan v high (Run.nil : Run config checks x x) = 0 := rfl

/-- A run with no step has no credits to scan. -/
theorem creditScan_nil (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x : ForkedBeaconState preset} :
    (PinDrift.Internal.creditScan blockP slotP v high (Run.nil : Run config checks x x)) = 0 := rfl

/-- Events within their credit limits credit the slashing events at most their limits. -/
theorem slashing_credits_le_limits (events : List (BalanceEvent preset))
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ((events.filter (·.source = .slashings)).map BalanceEvent.credits).sum ≤
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  induction events with
  | nil => simp
  | cons head rest ih =>
    have tailLe := ih fun e member => bounded e (List.mem_cons_of_mem _ member)
    have headLe := bounded head List.mem_cons_self
    by_cases source : head.source = .slashings
    · simp only [List.filter_cons, source, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    · simp only [List.filter_cons, source, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons]
      omega

/-! ## A floor and a ceiling on one key's effective balance -/

/-- A successful update of the effective balances applies the scalar update at each index.

It reads the balance of the index, which it keeps. -/
private theorem effective_update_at {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) {i : ℕ}
    (inside : i < s.validators.data.size) :
    ∃ (v : Validator) (balance new : Gwei), s.validators.data[i]? = some v ∧
      s.balances.data[i]? = some balance ∧
      t.validators.data[i]? = some { v with effectiveBalance := new } ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset f v) balance
        v.effectiveBalance = .ok new := by
  have found : ∃ v, s.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨v, found⟩ := found
  obtain ⟨balance, owned⟩ := processEffectiveBalanceUpdates_owned ok found
  obtain ⟨new, read, updated⟩ := processEffectiveBalanceUpdates_effectiveBalance_eq ok found owned
  exact ⟨v, balance, new, found, owned, read, updated⟩

/-- The update of the effective balances keeps a lower bound on the effective balance of a key.

Suppose the update changes the effective balance only if the balance rounded down is at least `low`.

Suppose also that the cap is at least `capLow`, and `low` is at most `capLow`.

The new value is the old one, or the balance rounded down to an increment, at most the cap. -/
private theorem effective_floor_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i capLow low : ℕ)
    (inside : i < s.validators.data.size) (lowCap : low ≤ capLow)
    (reach : (actualBalanceAt ⟨f, s⟩ i + preset.downwardBand < effectiveAt ⟨f, s⟩ i ∨
        effectiveAt ⟨f, s⟩ i + preset.upwardBand < actualBalanceAt ⟨f, s⟩ i) →
      low ≤ actualBalanceAt ⟨f, s⟩ i - actualBalanceAt ⟨f, s⟩ i %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  obtain ⟨v, balance, new, found, owned, read, updated⟩ := effective_update_at ok inside
  have capped := cap _ read
  change capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat at capped
  simp only [actualBalanceAt, owned, Option.map_some, Option.getD_some] at reach
  simp only [effectiveAt, found, Option.map_some, Option.getD_some] at reach previous
  simp only [effectiveAt, read, Option.map_some, Option.getD_some]
  rcases updatedEffectiveBalance_split updated with ⟨rfl, -⟩ | ⟨rfl, fires⟩
  · exact previous
  · rw [Base.Uint64.toNat_min, toNat_rounded]
    exact Nat.le_min.mpr ⟨reach fires, Nat.le_trans lowCap capped⟩

/-- One slot step keeps the lower bound, given the balance and the cap after it.

Only the epoch transition changes an effective balance, in its update. -/
private theorem effective_floor_slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (i capLow low : ℕ)
    (inside : i < s.validators.data.size) (lowCap : low ≤ capLow)
    (reach : (actualBalanceAt ⟨f, t⟩ i + preset.downwardBand < effectiveAt ⟨f, s⟩ i ∨
        effectiveAt ⟨f, s⟩ i + preset.upwardBand < actualBalanceAt ⟨f, t⟩ i) →
      low ≤ actualBalanceAt ⟨f, t⟩ i - actualBalanceAt ⟨f, t⟩ i %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (previous : low ≤ effectiveAt ⟨f, s⟩ i)
    (cap : ∀ v, t.validators.data[i]? = some v →
      capLow ≤ (withdrawalMaxEffectiveBalance preset f v).toNat) :
    low ≤ effectiveAt ⟨f, t⟩ i := by
  have life := (registryLifecycle_advanceSlot ok).size_le
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨next, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch advance
    have insideTail : i < advanced.validators.data.size := Nat.lt_of_lt_of_le inside life
    have insideBefore : i < before.validators.data.size := by
      rw [← (sameSizes_processEffectiveBalanceUpdates updated).1]
      rw [validators] at insideTail
      exact insideTail
    have prior : low ≤ effectiveAt ⟨f, before⟩ i := by
      rw [kept i inside]
      exact previous
    have bound := effective_floor_update updated i capLow low insideBefore lowCap
      (by
        rw [kept i inside]
        have reach' := reach
        simp only [actualBalanceAt, balances] at reach' ⊢
        exact reach') prior
      (fun v read => cap v (by rw [validators]; exact read))
    simpa only [effectiveAt, validators] using bound
  · cases advance
    exact previous

/-- The update of the effective balances keeps an upper bound on the effective balance of a key. -/
private theorem effective_ceiling_update {f : Fork} {s t : BeaconState preset f}
    (ok : processEffectiveBalanceUpdates s = .ok t) (i ceil capHigh : ℕ)
    (inside : i < s.validators.data.size)
    -- The cap bound is a whole number of increments, and the old effective balance is at most it.
    (alignedHigh : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (old : effectiveAt ⟨f, s⟩ i ≤ capHigh)
    -- The smaller of the balance and `capHigh` must be at most `ceil`.
    (funded : min (actualBalanceAt ⟨f, s⟩ i) capHigh ≤ ceil)
    -- The cap must be at most `capHigh`.
    (cap : ∀ v, t.validators.data[i]? = some v →
      (withdrawalMaxEffectiveBalance preset f v).toNat ≤ capHigh) :
    -- The new value is at most `ceil` plus the downward band.
    effectiveAt ⟨f, t⟩ i ≤ ceil + preset.downwardBand ∧
    -- It is also at most the old one, or the balance rounded down to an increment, at most the cap.
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i)
      (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) := by
  obtain ⟨v, balance, new, found, owned, read, updated⟩ := effective_update_at ok inside
  have capped := cap _ read
  change (withdrawalMaxEffectiveBalance preset f v).toNat ≤ capHigh at capped
  simp only [actualBalanceAt, owned, Option.map_some, Option.getD_some] at funded
  simp only [effectiveAt, found, Option.map_some, Option.getD_some] at old
  simp only [effectiveAt, read, found, Option.map_some, Option.getD_some]
  have add := updatedEffectiveBalance_le_add updated
  refine ⟨?_, ?_⟩
  · by_cases small : balance.toNat ≤ capHigh
    · omega
    · have newHigh : new.toNat ≤ capHigh := by
        rcases updatedEffectiveBalance_cases updated with rfl | rfl
        · exact old
        · rw [Base.Uint64.toNat_min, toNat_rounded]
          exact Nat.le_trans (Nat.min_le_right _ _) capped
      omega
  · rcases updatedEffectiveBalance_cases updated with rfl | rfl
    · exact Nat.le_max_left _ _
    · refine Nat.le_trans ?_ (Nat.le_max_right _ _)
      rw [Base.Uint64.toNat_min, toNat_rounded]
      by_cases small : balance.toNat ≤ capHigh
      · have funded' : balance.toNat ≤ ceil := by omega
        exact Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left _ _) (rounded_mono _ funded'),
          Nat.le_trans (Nat.min_le_right _ _) capped⟩
      · have ceilHigh : capHigh ≤ ceil := by omega
        have r := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat ceilHigh
        rw [alignedHigh, Nat.sub_zero] at r
        exact Nat.le_min.mpr ⟨Nat.le_trans (Nat.le_trans (Nat.min_le_right _ _) capped) r,
          Nat.le_trans (Nat.min_le_right _ _) capped⟩

/-- One slot step keeps an upper bound on the effective balance, given the balance and cap after it.

The step either keeps the effective balance and the epoch.

Or it moves to a later epoch, and the effective balance is at most `ceil` plus the band. -/
private theorem effective_ceiling_slot {f : Fork} {s t : BeaconState preset f}
    (ok : advanceSlot config checks s = .ok t) (i ceil capHigh : ℕ)
    (inside : i < s.validators.data.size)
    (alignedHigh : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (old : effectiveAt ⟨f, s⟩ i ≤ capHigh)
    (funded : min (actualBalanceAt ⟨f, t⟩ i) capHigh ≤ ceil)
    (cap : ∀ v, t.validators.data[i]? = some v →
      (withdrawalMaxEffectiveBalance preset f v).toNat ≤ capHigh) :
    effectiveAt ⟨f, t⟩ i ≤ max (effectiveAt ⟨f, s⟩ i)
      (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
    ((effectiveAt ⟨f, t⟩ i = effectiveAt ⟨f, s⟩ i ∧
        (getCurrentEpoch t).toNat = (getCurrentEpoch s).toNat) ∨
      (effectiveAt ⟨f, t⟩ i ≤ ceil + preset.downwardBand ∧
        (getCurrentEpoch s).toNat < (getCurrentEpoch t).toNat)) := by
  obtain ⟨next, cached, epoched, sum, cache, edge, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  have cases : ∀ c : BeaconState preset f, epochIfLast config checks next c = .ok epoched →
      next % preset.SLOTS_PER_EPOCH = 0 ∧ processEpoch config checks c = .ok epoched ∨
      next % preset.SLOTS_PER_EPOCH ≠ 0 ∧ epoched = c := by
    intro c edge
    unfold epochIfLast at edge
    split at edge
    · exact .inl ⟨‹_›, edge⟩
    · exact .inr ⟨‹_›, (Except.ok.inj edge).symm⟩
  rcases cases _ edge with ⟨boundary, epoch⟩ | ⟨inner, rfl⟩
  · obtain ⟨before, after, kept, updated, validators, balances⟩ := balanceDrift_epoch epoch
    have insideTail : i < epoched.validators.data.size := by
      have := (registryLifecycle_advanceSlot ok).size_le
      simpa using Nat.lt_of_lt_of_le inside this
    have insideBefore : i < before.validators.data.size := by
      rw [← (sameSizes_processEffectiveBalanceUpdates updated).1]
      rw [validators] at insideTail
      exact insideTail
    have bound := effective_ceiling_update updated i ceil capHigh insideBefore alignedHigh
      (by rw [kept i inside]; exact old)
      (by simpa only [actualBalanceAt, balances] using funded)
      (fun v read => cap v (by rw [validators]; exact read))
    have e := nextSlot_epoch_of_boundary sum boundary
    refine ⟨?_, .inr ⟨?_, ?_⟩⟩
    · have := bound.2
      rw [kept i inside] at this
      simpa only [effectiveAt, validators] using this
    · simpa only [effectiveAt, validators] using bound.1
    · simp only
      omega
  · refine ⟨?_, .inl ⟨rfl, ?_⟩⟩
    · exact Nat.le_max_left _ _
    · simp only
      rw [nextSlot_epoch_of_inside sum inner]

section Rewards

/-! ### One key's reward in an epoch pass -/

/-- The epoch-pass reward credits to the key in one step.

A slot step's events are those of its epoch pass and its upgrades.

So its `.rewards` events are the epoch's rewards.

A block step has none counted: its proposer credits are charged elsewhere. -/
def epochRewards (v : ℕ) {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : ℕ :=
  match step with
  | .slot ok =>
    ((((Step.slot (config := config) (checks := checks) ok).balanceEvents.toOption.getD []).filter
      (·.source = .rewards)).map (PinDrift.Internal.keyCredit v)).sum
  | .block .. => 0

/-- The reward credits of a list of events are those of the events, read at one position. -/
private theorem sum_filter_rewards (events : List (BalanceEvent preset)) (v : ℕ) :
    ((events.filter (·.source = .rewards)).map (PinDrift.Internal.keyCredit v)).sum =
      (events.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    by_cases rewards : e.source = .rewards
    · simp [rewards, PinDrift.Internal.keyCredit, DirectSafety.Apriori.Internal.rewardCredit, ih]
    · simp [rewards, DirectSafety.Apriori.Internal.rewardCredit, ih]

/-- A flag pays a key at most its base reward times the flag's weight, over the active stake. -/
private theorem flagReward_le {f : Fork} (altair : .altair ≤ f) {state : BeaconState preset f}
    (within : state.RegistryWithinLimit) {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flag = .ok (rewards, penalties))
    {total : Gwei} (active : getTotalActiveBalance state = .ok total) (P v : ℕ)
    (inside : v < state.validators.data.size)
    -- The rate read in the previous epoch is at most `P` times the active increments.
    --
    -- A key that is not active in the previous epoch earns nothing, so it needs no rate.
    (rate : v.toUInt64 ∉ getActiveValidatorIndices state (getPreviousEpoch state) ∨
      ∀ perIncrement : Gwei, getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat *
            ((∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
              balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    (rewards.getD v 0).toNat *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) ≤
      balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
    (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      (rewards.getD v 0).toNat = 0) ∧
    -- A key that is not active in the previous epoch also gets a reward of 0 outright.
    (v.toUInt64 ∉ getActiveValidatorIndices state (getPreviousEpoch state) →
      (rewards.getD v 0).toNat = 0) := by
  -- The increments that set the flag in the previous epoch are at most those active then.
  obtain ⟨participating, participatingBalance, total', flaggedOk, weighed, totalOk, perKey⟩ :=
    getFlagIndexDeltas_getD within computed
  obtain rfl : total = total' := Except.ok.inj (active.symm.trans totalOk)
  obtain ⟨eligible, -, notEligible, eligibleCase⟩ := perKey v inside
  have zero (h : (rewards.getD v 0).toNat = 0) :
      (rewards.getD v 0).toNat *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) ≤
      balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
      (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
        (rewards.getD v 0).toNat = 0) ∧
      (v.toUInt64 ∉ getActiveValidatorIndices state (getPreviousEpoch state) →
        (rewards.getD v 0).toNat = 0) :=
    ⟨by rw [h, Nat.zero_mul]; exact Nat.zero_le _, fun _ => h, fun _ => h⟩
  by_cases isEligible : eligible = true
  swap
  · exact zero (by simp [(notEligible (by simpa using isEligible)).1])
  obtain ⟨base, baseOk, member⟩ := eligibleCase isEligible
  by_cases present : v.toUInt64 ∈ participating
  swap
  · exact zero (by simp [(member.2 present).1])
  have rate := rate.resolve_left fun idle =>
    idle (mem_getUnslashedParticipatingIndices flaggedOk _ present).1
  obtain ⟨leak, leakOk, formula, -⟩ := member.1 present
  cases leak
  swap
  · simp only [↓reduceIte] at formula
    exact zero formula
  simp only [Bool.false_eq_true, ↓reduceIte] at formula
  have index : v.toUInt64.toNat = v := toNat_toUInt64_of_lt within inside
  obtain ⟨per, perOk⟩ : ∃ per, getBaseRewardPerIncrement preset total = .ok per := by
    simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff] at baseOk
    obtain ⟨_, -, per, perOk, -⟩ := baseOk
    exact ⟨per, perOk⟩
  obtain ⟨validator, found, baseEq⟩ := getBaseReward_eq_mul_of_altair altair perOk baseOk
  rw [index] at found
  have stakeV : balanceAt state v = validator.effectiveBalance.toNat := by
    simp [balanceAt, found]
  have increments : (rewards.getD v 0).toNat *
      (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) ≤
      base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    rw [formula]
    exact Nat.div_mul_le_self _ _
  refine ⟨?_, fun none => by rw [formula, none, Nat.zero_mul, Nat.div_zero],
    fun idle => absurd (mem_getUnslashedParticipatingIndices flaggedOk _ present).1 idle⟩
  -- A key with less than one increment has no base reward.
  by_cases small : balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0
  · have noBase : base.toNat = 0 := by rw [baseEq, ← stakeV, small, Nat.zero_mul]
    rw [noBase, Nat.zero_mul, Nat.zero_mul] at increments
    rw [small, Nat.zero_mul, Nat.zero_mul]
    exact increments
  -- The key sets the flag and is active in the previous epoch, so both stakes hold its balance.
  have stakeParticipating : balanceAt state v ≤
      ∑ i ∈ participating.toFinset, balanceAt state i.toNat := by
    have := Finset.single_le_sum (f := fun i : ValidatorIndex => balanceAt state i.toNat)
      (fun _ _ => Nat.zero_le _) (List.mem_toFinset.mpr present)
    simpa only [index] using this
  have subset : ∑ i ∈ participating.toFinset, balanceAt state i.toNat ≤
      ∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
        balanceAt state i.toNat :=
    Finset.sum_le_sum_of_subset fun i member =>
      List.mem_toFinset.mpr (mem_getUnslashedParticipatingIndices flaggedOk i
        (List.mem_toFinset.mp member)).1
  obtain ⟨-, -, balanceEq⟩ := getTotalBalance_ok_iff_stake.mp weighed
  have positive : 0 < balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero small
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    refine Nat.pos_of_ne_zero fun zero => ?_
    rw [zero, Nat.div_zero] at positive
    exact Nat.lt_irrefl _ positive
  have one : 1 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ balanceAt state v :=
    (Nat.le_div_iff_mul_le incPos).mp positive
  rw [Nat.one_mul] at one
  have participatingLe : participatingBalance.toNat ≤
      ∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
        balanceAt state i.toNat := by
    rw [balanceEq]
    exact max_le (Nat.le_trans (Nat.le_trans one stakeParticipating) subset) subset
  have share : participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      (∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
        balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.div_le_div_right participatingLe
  have bound := rate per perOk
  calc (rewards.getD v 0).toNat *
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat)
      ≤ base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := increments
    _ ≤ base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        ((∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
          balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :=
        Nat.mul_le_mul_left _ share
    _ = balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (per.toNat * ((∑ i ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset,
          balanceAt state i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
        rw [baseEq, stakeV]
        ring
    _ ≤ balanceAt state v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
        (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
        Nat.mul_le_mul_left _ bound

/-- The three flags pay a key, in a rewards replay of a state, at most its stake times `P`. -/
private theorem replayRewards_credit_le {f : Fork} (altair : .altair ≤ f)
    {pass : BeaconState preset f} (within : pass.RegistryWithinLimit)
    {rewarded : BalanceReplay preset f}
    (replayed : replayRewards (config := config) (pass, []) = .ok rewarded) (P v : ℕ)
    (inside : v < pass.validators.data.size)
    (rate : v.toUInt64 ∉ getActiveValidatorIndices pass (getPreviousEpoch pass) ∨
      ∀ total perIncrement : Gwei, getTotalActiveBalance pass = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat *
            ((∑ i ∈ (getActiveValidatorIndices pass (getPreviousEpoch pass)).toFinset,
              balanceAt pass i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0 ∨
      ∃ total : Gwei,
        -- The credit is scaled by `64` and by the active increments.
        --
        -- It is at most the key's increments times `54`, `P` and the active increments.
        (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum *
            (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
          balanceAt pass v / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 54 *
            (P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
        -- A state with no active increment pays nothing.
        (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
          (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0) ∧
        -- A key that is not active in the previous epoch is paid nothing.
        (v.toUInt64 ∉ getActiveValidatorIndices pass (getPreviousEpoch pass) →
          (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0) := by
  by_cases genesis : getCurrentEpoch pass = GENESIS_EPOCH
  · simp only [replayRewards, genesis, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    exact .inl rfl
  obtain ⟨source, target, head, inactivity, first, second, third, sourceOk, targetOk, headOk,
    inactivityOk, firstOk, secondOk, thirdOk, last⟩ :=
    DirectSafety.Apriori.Internal.replayRewards_passes altair genesis replayed
  obtain ⟨-, -, total, -, -, active, -⟩ := getFlagIndexDeltas_getD within sourceOk
  have wd : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  have flagBound (flag : Fin PARTICIPATION_FLAG_WEIGHTS.length) {deltas : Array Gwei × Array Gwei}
      (computed : getFlagIndexDeltas pass altair flag = .ok deltas) :=
    flagReward_le altair within (flag := flag) (rewards := deltas.1) (penalties := deltas.2)
      computed active P v inside (rate.imp_right fun rate per perOk => rate total per active perOk)
  have one := flagBound ⟨0, by decide⟩ sourceOk
  have two := flagBound ⟨1, by decide⟩ targetOk
  have three := flagBound ⟨2, by decide⟩ headOk
  have flows (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset f}
      (src : BalanceSource) (ok : replayDeltas src deltas pre = .ok post) :=
    (DirectSafety.Apriori.Internal.replayDeltas_flows src deltas ok v).2
  have s1 := flows source .penalties firstOk
  have s2 := flows target .penalties secondOk
  have s3 := flows head .penalties thirdOk
  have s4 := flows inactivity .inactivity last
  have noReward : (inactivity.1.getD v 0).toNat = 0 := by
    simp [getInactivityPenaltyDeltas_rewards inactivityOk]
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at s1
  have weights : PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ : Fin 3)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ : Fin 3)].toNat = 54 := rfl
  have sum : (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum ≤
      (source.1.getD v 0).toNat + (target.1.getD v 0).toNat + (head.1.getD v 0).toNat := by
    omega
  rw [wd] at one two three
  obtain ⟨b1, z1, i1⟩ := one
  obtain ⟨b2, z2, i2⟩ := two
  obtain ⟨b3, z3, i3⟩ := three
  refine .inr ⟨total, ?_, fun none => ?_, fun idle => ?_⟩
  · have scaled := Nat.mul_le_mul_right
      (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) sum
    simp only [Nat.add_mul] at scaled
    rw [← weights]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  · have := z1 none
    have := z2 none
    have := z3 none
    omega
  · have := i1 idle
    have := i2 idle
    have := i3 idle
    omega

/-- Quotients of the reward bound: the rewards of a pass are at most a rate for each increment. -/
private theorem reward_sum_le (S A K Ke P : ℕ)
    (bound : S * (A * 64) ≤ K * 54 * (P * A)) (none : A = 0 → S = 0) (small : K ≤ Ke) :
    S ≤ Ke * P * 54 / 64 := by
  by_cases zero : A = 0
  · rw [none zero]
    exact Nat.zero_le _
  have positive : 0 < A := Nat.pos_of_ne_zero zero
  have times : S * 64 * A ≤ K * 54 * P * A := by
    calc S * 64 * A = S * (A * 64) := by ring
      _ ≤ K * 54 * (P * A) := bound
      _ = K * 54 * P * A := by ring
  have cancelled : S * 64 ≤ K * 54 * P := Nat.le_of_mul_le_mul_right times positive
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 64)]
  calc S * 64 ≤ K * 54 * P := cancelled
    _ ≤ Ke * 54 * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ small)
    _ = Ke * P * 54 := by ring

/-- The rewards replay credits no key past the registry.

It records an increase or a decrease at an index that the registry holds, and keeps its sizes. -/
private theorem replayRewards_absent {f : Fork} {pass : BeaconState preset f}
    {rewarded : BalanceReplay preset f}
    (replayed : replayRewards (config := config) (pass, []) = .ok rewarded)
    (matched : BalancesMatch pass) {v : ℕ} (outside : pass.validators.data.size ≤ v) :
    (rewarded.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0 := by
  have final := replayRewards_induction (config := config)
    (fun pre : BalanceReplay preset f => BalancesMatch pre.1 ∧
      pre.1.validators = pass.validators ∧
        (pre.2.map (DirectSafety.Apriori.Internal.rewardCredit v)).sum = 0)
    (fun {pre post index reward} held ok => by
      obtain ⟨_, _, _, actionOk, events⟩ := recordBalance_single ok
      rw [events]
      have increased := liftAccessor_ok.mp actionOk
      have same := sameSizes_increaseBalance increased
      have registry := increaseBalance_validators increased
      obtain ⟨preMatched, preSame, preSum⟩ := held
      have preSize : pre.1.balances.data.size ≤ v := by
        unfold BalancesMatch at preMatched
        rw [preMatched, preSame]
        exact outside
      refine ⟨balancesMatch_of_sameSizes same preMatched, registry.trans preSame, ?_⟩
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, preSum, DirectSafety.Apriori.Internal.rewardCredit, ↓reduceIte,
        actualBalanceAt, Array.getElem?_eq_none preSize,
        Array.getElem?_eq_none (show post.1.balances.data.size ≤ v by rw [same.2]; exact preSize),
        Option.map_none,
        Option.getD_none, Nat.sub_self, Nat.add_zero])
    (fun {source pre post index penalty} sourceCases held ok => by
      obtain ⟨_, _, _, actionOk, events⟩ := recordBalance_single ok
      rw [events]
      have decreased := liftAccessor_ok.mp actionOk
      have same := sameSizes_decreaseBalance decreased
      have registry := decreaseBalance_validators decreased
      obtain ⟨preMatched, preSame, preSum⟩ := held
      refine ⟨balancesMatch_of_sameSizes same preMatched, registry.trans preSame, ?_⟩
      rcases sourceCases with rfl | rfl <;>
        simp [List.map_append, List.sum_append, preSum,
          DirectSafety.Apriori.Internal.rewardCredit])
    ⟨matched, rfl, rfl⟩ replayed
  exact final.2.2

open DirectSafety.Apriori.Internal in
/-- One key's rewards credit in a step is at most a rate for each epoch that the step ends. -/
theorem epochRewards_le {m n : ForkedBeaconState preset}
    (step : Step config checks m n) (altair : .altair ≤ m.fork) (early : n.fork < .glamsterdam)
    -- A key past the registry of a state with matched balances gets no reward.
    (v : ℕ) (known : v < m.state.validators.data.size ∨ BalancesMatch m.state) (E P : ℕ)
    -- The key's stake at the start is at most `E`.
    (envelope : v.toUInt64 ∉ getActiveValidatorIndices m.state (getPreviousEpoch m.state) ∨
      effectiveAt m v ≤ E)
    -- `P` bounds the rate read at the active stake, scaled by the previous epoch's share of it.
    (rate : v.toUInt64 ∉ getActiveValidatorIndices m.state (getPreviousEpoch m.state) ∨
      ∀ total perIncrement : Gwei, getTotalActiveBalance m.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat *
            ((∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
              effectiveAt m i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    PinDrift.Internal.epochRewards v step ≤ ((getCurrentEpoch n.state).toNat - (getCurrentEpoch
      m.state).toNat) *
      (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) := by
  -- The step is a slot, and it ends an epoch exactly when it runs the epoch's pass.
  cases step with
  | block engine signed due ok => simp [PinDrift.Internal.epochRewards]
  | slot ok =>
    have mEarly : m.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
    simp only [PinDrift.Internal.epochRewards]
    cases hev : (Step.slot (config := config) (checks := checks) ok).balanceEvents with
    | error err => simp [Except.toOption]
    | ok events =>
      simp only [Except.toOption, Option.getD_some]
      rw [sum_filter_rewards]
      obtain ⟨advanced, cached, crossings, -, upgrades, cachedOk, crossingOk, kind⟩ :=
        Step.balanceEvents_slot ok early hev
      have crossed := upgradeBalanceReplay_crossing crossingOk
      have crossingsQuiet : (crossings.map (rewardCredit v)).sum = 0 :=
        List.sum_eq_zero fun x member => by
          obtain ⟨e, mem, rfl⟩ := List.mem_map.mp member
          simp [rewardCredit, crossed e mem]
      rcases kind with ⟨-, eventsEq⟩ |
        ⟨middle, updated, recorded, recordOk, -, -, -, eventsEq, next, nextEq, advSlot, last, -⟩
      · subst eventsEq
        rw [crossingsQuiet]
        exact Nat.zero_le _
      subst eventsEq
      obtain ⟨just, pass, rewarded, later, justified, scored, rewardedOk, recordedEq,
        laterSources, -⟩ := epochReplay_events altair (epochBalanceReplay_trace recordOk)
      simp only at recordedEq
      subst recordedEq
      have laterQuiet : (later.map (rewardCredit v)).sum = 0 :=
        List.sum_eq_zero fun x member => by
          obtain ⟨e, mem, rfl⟩ := List.mem_map.mp member
          rcases laterSources e mem with s | s | s <;> simp [rewardCredit, s]
      simp only [List.map_append, List.sum_append, laterQuiet, crossingsQuiet, Nat.add_zero]
      -- The slot ends one epoch.
      have nSlot : n.state.slot = next := (processUpgrades_slot upgrades).trans advSlot
      have epochs : (getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat = 1 := by
        have boundary := nextSlot_epoch_of_boundary nextEq last
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, nSlot, boundary]
        exact Nat.add_sub_cancel_left _ _
      rw [epochs, Nat.one_mul]
      -- The pass reads the registry and the epoch of the start.
      obtain ⟨-, -, -, validatorsEq, slotEq⟩ :=
        pass_kept_of_effective (config := config) (checks := checks)
          (inner := (Run.nil : Run config checks m m)) (effectiveKept_refl m.state) rfl
          cachedOk justified scored
      -- A key past the registry gets no reward, as the replay keeps the sizes of the balances.
      by_cases inside : v < m.state.validators.data.size
      swap
      · have matched := known.resolve_left inside
        have passBalances : pass.balances = m.state.balances := by
          have first := justified.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          have second := scored.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
          obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
          exact second.2.1.trans first.2.1
        rw [replayRewards_absent rewardedOk (by
          unfold BalancesMatch at matched ⊢
          rw [passBalances, validatorsEq]
          exact matched) (by rw [validatorsEq]; omega)]
        exact Nat.zero_le _
      have within : pass.RegistryWithinLimit := pass.validators.bound mEarly
      have insidePass : v < pass.validators.data.size := by
        rw [validatorsEq]
        exact inside
      have balanceAtEq (i : ℕ) : balanceAt pass i = effectiveAt m i := by
        simp [balanceAt, effectiveAt, validatorsEq]
      have totalEq : getTotalActiveBalance pass = getTotalActiveBalance m.state := by
        simp only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getCurrentEpoch,
          slotEq, validatorsEq, getTotalBalance]
        rfl
      have prevEpoch : getPreviousEpoch pass = getPreviousEpoch m.state := by
        simp only [getPreviousEpoch, getCurrentEpoch, slotEq]
      have prevEq : getActiveValidatorIndices pass (getPreviousEpoch pass) =
          getActiveValidatorIndices m.state (getPreviousEpoch m.state) := by
        rw [prevEpoch]
        simp only [getActiveValidatorIndices, validatorsEq]
      have ratePass : v.toUInt64 ∉ getActiveValidatorIndices pass (getPreviousEpoch pass) ∨
          ∀ total perIncrement : Gwei, getTotalActiveBalance pass = .ok total →
            getBaseRewardPerIncrement preset total = .ok perIncrement →
            perIncrement.toNat *
                ((∑ i ∈ (getActiveValidatorIndices pass (getPreviousEpoch pass)).toFinset,
                  balanceAt pass i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
              P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
        rw [prevEq]
        refine rate.imp_right fun rate total perIncrement totalOk perOk => ?_
        have sums : (∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
            balanceAt pass i.toNat) =
            ∑ i ∈ (getActiveValidatorIndices m.state (getPreviousEpoch m.state)).toFinset,
              effectiveAt m i.toNat :=
          Finset.sum_congr rfl fun i _ => balanceAtEq i.toNat
        rw [sums]
        exact rate total perIncrement (totalEq.symm.trans totalOk) perOk
      have bound := replayRewards_credit_le altair within rewardedOk P v insidePass ratePass
      have flagSum : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := rfl
      have wd : WEIGHT_DENOMINATOR.toNat = 64 := by decide
      rw [flagSum, wd]
      rcases bound with zero | ⟨total, scaled, none, idle⟩
      · rw [zero]
        exact Nat.zero_le _
      rcases envelope with inactive | envelope
      · rw [idle (by rw [prevEq]; exact inactive)]
        exact Nat.zero_le _
      · exact reward_sum_le _ _ _ _ P scaled none (Nat.div_le_div_right (by
          rw [balanceAtEq]
          exact envelope))

/-- A step raises the balance of a key by at most the credits of its events. -/
theorem step_balance_le_events {m n : ForkedBeaconState preset}
    (step : Step config checks m n) (early : n.fork < .glamsterdam) (i : ℕ)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events) :
    actualBalanceAt n i ≤ actualBalanceAt m i + (events.map (PinDrift.Internal.keyCredit i)).sum :=
      by
  have run := DirectSafety.Apriori.Internal.single_balanceEvents step ok
  have cover := coverage_run (Run.nil.snoc step) early (getCurrentEpoch n.state).toNat
    (Nat.le_succ _) run false i
  have ends := Run.balancePath_ends (Run.nil.snoc step)
  have rise := Apriori.Internal.balance_le_pathCredits i _ m n ends.1 ends.2
  simp only [coveragePath, Bool.false_eq_true, ↓reduceIte, coverageDelta] at cover
  exact le_trans rise (Nat.add_le_add_left cover _)

/-- A step raises the balance of a key by at most its epoch rewards and its other credits.

A block step counts the rise of the key's balance across the whole step.

A slot step counts the credits of its events from the sources other than the epoch rewards. -/
theorem step_balance_le {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (i : ℕ) :
    actualBalanceAt n i ≤ actualBalanceAt m i + PinDrift.Internal.epochRewards i step +
      PinDrift.Internal.stepNet i step + PinDrift.Internal.stepCredit (fun _ => false) (fun s =>
        decide (s ≠ .rewards)) i step := by
  cases step with
  | block engine signed due okb =>
    simp only [PinDrift.Internal.epochRewards, PinDrift.Internal.stepNet]
    omega
  | slot oks =>
    obtain ⟨events, ok⟩ := (Step.slot oks : Step config checks m n).balanceEvents_ok early
    have base := PinDrift.Internal.step_balance_le_events (Step.slot oks : Step config checks m n)
      early i ok
    simp only [PinDrift.Internal.epochRewards, PinDrift.Internal.stepNet,
      PinDrift.Internal.stepCredit, ok, Except.toOption, Option.getD_some] at base ⊢
    have split := List.sum_map_filter_add_sum_map_filter_not
      (fun e : BalanceEvent preset => e.source = .rewards) (PinDrift.Internal.keyCredit i) events
    simp only [ne_eq] at split ⊢
    omega

/-- The bound on a key's balance below a cap along a run.

It is the start, the epoch rewards and the other credits. -/
def creditBound {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (i high E P capHigh : ℕ) : ℕ :=
  -- The start and the balance count only up to the cap.
  min (actualBalanceAt x i) capHigh +
    -- The epoch rewards are those of the epochs that the run ends.
    --
    -- They are read at the rate given by `E` and `P`.
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
      (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
    -- The other credits are the net rises of its block steps and the credits of its slot steps.
    --
    -- The slot-step credits leave out the epoch rewards.
    PinDrift.Internal.netScan i high tail +
      (PinDrift.Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high tail)

end Rewards

/-- A balance ceiling, an envelope or a floor on a key's balance bounds its effective balance. -/
theorem Run.effective_floor_pair {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size)
    (floor capLow capHigh high E P : ℕ) :
    -- First, suppose a key's balance stays at least `floor` at every state of the run.
    --
    -- Suppose also that its cap stays at least `capLow`.
    --
    -- Then its effective balance at the end is at least the least of three values.
    --
    -- They are its effective balance at the start, `capLow`, and `floor` rounded down.
    --
    -- That rounding is down to an increment.
    ((∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i) →
      (∀ z ∈ tail.balancePath, capLow ≤ PinTerms.capAt z i) →
      min (effectiveAt x i)
        (min capLow (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
          effectiveAt y i) ∧
    -- Second, suppose the effective balance at the start is a whole number of increments.
    --
    -- Suppose a step that could lower it leaves a balance of at least that effective balance.
    --
    -- A step could lower it when the balance after it plus the downward band is below it.
    --
    -- Suppose also that its cap stays at least its effective balance at the start.
    --
    -- Then the effective balance at the end is at least that at the start.
    --
    -- A downward update sets it to the balance rounded down.
    --
    -- That is at least the effective balance at the start, which is a whole number of increments.
    --
    -- An update moves the effective balance only at an epoch's first slot.
    --
    -- It moves it down to the balance rounded to an increment, and up to at most the cap.
    --
    -- It never moves it up below where it was.
    (effectiveAt x i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      (∀ {m n : ForkedBeaconState preset} (before : Run config checks x m)
          (step : Step config checks m n) (after : Run config checks n y),
        (before.snoc step).append after = tail →
        actualBalanceAt n i + preset.downwardBand < effectiveAt m i →
        effectiveAt x i ≤ actualBalanceAt n i) →
      (∀ z ∈ tail.balancePath, effectiveAt x i ≤ PinTerms.capAt z i) →
      effectiveAt x i ≤ effectiveAt y i) ∧
    -- Third, suppose the smaller of the balance and `capHigh` stays at most `ceil`.
    --
    -- Suppose also that the cap stays at most `capHigh`.
    --
    -- The bound `capHigh` is a whole number of increments.
    --
    -- The effective balance at the start is at most `capHigh`.
    --
    -- Then the effective balance at the end is at most the greater of two values.
    --
    -- They are its effective balance at the start, and the ceiling rounded down, at most the cap.
    --
    -- If no epoch boundary is crossed, it is the effective balance at the start.
    --
    -- After a boundary, it is at most `ceil` plus the downward band.
    --
    -- The epoch never moves back.
    (∀ ceil : ℕ, capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      effectiveAt x i ≤ capHigh →
      (∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ ceil) →
      (∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) →
      effectiveAt y i ≤ max (effectiveAt x i)
        (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
      ((getCurrentEpoch y.state).toNat ≤ (getCurrentEpoch x.state).toNat →
        effectiveAt y i = effectiveAt x i) ∧
      ((getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat →
        effectiveAt y i ≤ ceil + preset.downwardBand) ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat) ∧
    -- Fourth, suppose the cap stays at most `capHigh`, as in the third.
    --
    -- Suppose the rate of the rewards at every state is at most `P`.
    --
    -- Suppose also that the run ends by the epoch `high + 1`.
    --
    -- Suppose also that `E` is at least the greatest effective balance that the bound below allows.
    --
    -- Then the balance at every state is at most its start, plus the epoch rewards.
    --
    -- Those rewards are read at the rate of `E`.
    --
    -- It also adds the other credits that the events of the run give the key.
    (capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → effectiveAt x i ≤ capHigh →
      (∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) →
      (∀ z ∈ tail.balancePath,
        i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) ∨
        ∀ total perIncrement : Gwei,
          getTotalActiveBalance z.state = .ok total →
          getBaseRewardPerIncrement preset total = .ok perIncrement →
          perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
            (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
            P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) →
      (getCurrentEpoch y.state).toNat ≤ high + 1 →
      max (effectiveAt x i) (min capHigh (PinDrift.Internal.creditBound tail i high E P capHigh -
        PinDrift.Internal.creditBound tail i high E P capHigh %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E →
      ∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤
        PinDrift.Internal.creditBound tail i high E P capHigh) := by
  induction tail with
  | nil => exact ⟨fun _ _ => Nat.min_le_left _ _, fun _ _ _ => Nat.le_refl _,
      fun _ _ _ _ _ => ⟨Nat.le_max_left _ _, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl _),
        Nat.le_refl _⟩,
      fun _ _ _ _ _ _ z hz => by
        rw [Run.balancePath, List.mem_singleton] at hz
        subst hz
        simp [PinDrift.Internal.creditBound, PinDrift.Internal.netScan_nil,
          PinDrift.Internal.creditScan_nil]⟩
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨ihFloor, ihEnvelope, ihCeiling, ihCredit⟩ := ih middleEarly
    have room : i < middle.state.validators.data.size :=
      Nat.lt_of_lt_of_le inside pre.registryLifecycle.size_le
    have atMiddle : middle ∈ pre.balancePath :=
      List.mem_of_mem_getLast? (Run.balancePath_ends pre).2
    have altair : .altair ≤ middle.fork :=
      Nat.le_trans (by decide) (Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps))
    have key : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → effectiveAt x i ≤ capHigh →
        (∀ z ∈ (pre.snoc step).balancePath, PinTerms.capAt z i ≤ capHigh) →
        (∀ z ∈ (pre.snoc step).balancePath,
          i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) ∨
          ∀ total perIncrement : Gwei,
            getTotalActiveBalance z.state = .ok total →
            getBaseRewardPerIncrement preset total = .ok perIncrement →
            perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
              (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
              P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) →
        (getCurrentEpoch last.state).toNat ≤ high + 1 →
        max (effectiveAt x i) (min capHigh (PinDrift.Internal.creditBound (pre.snoc step) i high E P
          capHigh -
          PinDrift.Internal.creditBound (pre.snoc step) i high E P capHigh %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E →
        (∀ z ∈ step.balancePath, z = middle ∨ z = last) →
        ∀ z ∈ (pre.snoc step).balancePath,
          min (actualBalanceAt z i) capHigh ≤ PinDrift.Internal.creditBound (pre.snoc step) i high E
            P capHigh := by
      intro alignedHigh startCap capC rate endEp closed pathCases z hz
      have xm : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch middle.state).toNat :=
        UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
      have ml : (getCurrentEpoch middle.state).toNat ≤ (getCurrentEpoch last.state).toNat :=
        UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
      have within : (getCurrentEpoch middle.state).toNat ≤ high + 1 := by omega
      have scan := PinDrift.Internal.creditScan_snoc (fun _ => false) (fun s => decide (s ≠
        .rewards))
        i high pre step
      have net := PinDrift.Internal.netScan_snoc i high pre step
      simp only [within, ↓reduceIte] at scan net
      have tailEq : PinDrift.Internal.creditBound (pre.snoc step) i high E P capHigh =
          PinDrift.Internal.creditBound pre i high E P capHigh +
            ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) *
              (E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
                (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
            (PinDrift.Internal.stepNet i step +
              PinDrift.Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step)
                := by
        unfold PinDrift.Internal.creditBound
        rw [scan, net]
        generalize E / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat = G
        have split : ((getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat) * G =
            ((getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat) * G +
              ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) * G := by
          rw [← Nat.add_mul]
          congr 1
          omega
        rw [split]
        omega
      have closedPre : max (effectiveAt x i) (min capHigh (PinDrift.Internal.creditBound pre i high
        E P capHigh -
          PinDrift.Internal.creditBound pre i high E P capHigh %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E :=
        le_trans (max_le_max le_rfl (min_le_min le_rfl (rounded_mono _ (by omega)))) closed
      have ihPre := ihCredit alignedHigh startCap
        (fun p member => capC p (List.mem_append_left _ member))
        (fun p member => rate p (List.mem_append_left _ member)) within closedPre
      rcases List.mem_append.mp hz with old | stepMember
      · exact (ihPre z old).trans (by omega)
      · rcases pathCases z stepMember with rfl | rfl
        · exact (ihPre _ atMiddle).trans (by omega)
        · have ceilings : ∀ p ∈ pre.balancePath,
              min (actualBalanceAt p i) capHigh ≤ PinDrift.Internal.creditBound (pre.snoc step) i
                high E P capHigh :=
            fun p member => (ihPre p member).trans (by omega)
          obtain ⟨c1, -, -, -⟩ := ihCeiling (PinDrift.Internal.creditBound (pre.snoc step) i high E
            P capHigh)
            alignedHigh startCap ceilings
            (fun p member => capC p (List.mem_append_left _ member))
          rw [Nat.min_comm] at c1
          have envelope : effectiveAt middle i ≤ E := c1.trans closed
          have rewards := PinDrift.Internal.epochRewards_le step altair early i (Or.inl room) E P
            (.inr envelope)
            (rate middle (List.mem_append_left _ atMiddle))
          have stepBound := PinDrift.Internal.step_balance_le step early i
          have mid := ihPre _ atMiddle
          rw [tailEq]
          omega
    cases step with
    | @block fork before after engine signed due ok =>
      have kept := effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i room
      have epoch : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
        simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
      refine ⟨fun balanceFloor capFloor => ?_, fun aligned downs capFloor => ?_,
        fun ceil alignedHigh startCap balanceCeil capCeil => ?_,
        fun alignedHigh startCap capC rate endEp closed =>
          key alignedHigh startCap capC rate endEp closed
            (fun z hz => by simpa [Step.balancePath] using hz)⟩
      · rw [kept]
        exact ihFloor (fun p member => balanceFloor p (List.mem_append_left _ member))
          (fun p member => capFloor p (List.mem_append_left _ member))
      · rw [kept]
        exact ihEnvelope aligned
          (fun r1 st r2 cut => downs r1 st (r2.snoc (Step.block engine signed due ok))
            (congrArg (fun r => Run.snoc r (Step.block engine signed due ok)) cut))
          (fun p member => capFloor p (List.mem_append_left _ member))
      · obtain ⟨c1, c2, c3, c4⟩ := ihCeiling ceil alignedHigh startCap
          (fun p member => balanceCeil p (List.mem_append_left _ member))
          (fun p member => capCeil p (List.mem_append_left _ member))
        simp only at epoch c2 c3 c4 ⊢
        rw [kept, epoch]
        exact ⟨c1, c2, c3, c4⟩
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have onPath : (⟨middle.fork, next⟩ : ForkedBeaconState preset) ∈
          (Step.slot ok).balancePath := by
        simp [Step.balancePath, advanced, Except.toOption]
      have fuluMiddle : Fork.fusaka ≤ middle.fork :=
        Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      have same := DirectSafety.Apriori.Internal.processUpgrades_eq_of_window upgraded
        fuluMiddle early
      subst same
      refine ⟨fun balanceFloor capFloor => ?_, fun aligned downs capFloor => ?_,
        fun ceil alignedHigh startCap balanceCeil capCeil => ?_,
        fun alignedHigh startCap capC rate endEp closed =>
          key alignedHigh startCap capC rate endEp closed
            (fun z hz => by simpa [Step.balancePath, advanced, Except.toOption] using hz)⟩
      · have funded := balanceFloor _ (List.mem_append_right _ onPath)
        have capped := capFloor _ (List.mem_append_right _ onPath)
        have prior := ihFloor (fun p member => balanceFloor p (List.mem_append_left _ member))
          (fun p member => capFloor p (List.mem_append_left _ member))
        refine effective_floor_slot advanced i capLow _ room
          (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)) (fun _ => ?_) prior
          (fun v read => by simpa [PinTerms.capAt, read] using capped)
        exact (Nat.min_le_right _ _).trans ((Nat.min_le_right _ _).trans (rounded_mono _ funded))
      · have capped := capFloor _ (List.mem_append_right _ onPath)
        have prior := ihEnvelope aligned
          (fun r1 st r2 cut => downs r1 st (r2.snoc (Step.slot ok))
            (congrArg (fun r => Run.snoc r (Step.slot ok)) cut))
          (fun p member => capFloor p (List.mem_append_left _ member))
        refine effective_floor_slot advanced i (PinTerms.capAt ⟨middle.fork, next⟩ i) _ room capped
          (fun fires => ?_) prior (fun v read => by simp [PinTerms.capAt, read])
        have eta : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i =
            effectiveAt middle i := rfl
        rw [eta] at fires
        have reach : effectiveAt x i ≤ actualBalanceAt ⟨middle.fork, next⟩ i := by
          rcases fires with below | above
          · exact downs pre (Step.slot ok) Run.nil rfl below
          · omega
        have lift := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat reach
        rw [aligned, Nat.sub_zero] at lift
        exact lift
      · have funded := balanceCeil _ (List.mem_append_right _ onPath)
        have capped := capCeil _ (List.mem_append_right _ onPath)
        obtain ⟨c1, c2, c3, c4⟩ := ihCeiling ceil alignedHigh startCap
          (fun p member => balanceCeil p (List.mem_append_left _ member))
          (fun p member => capCeil p (List.mem_append_left _ member))
        have oldHigh : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i ≤
            capHigh := by
          have eta : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i =
              effectiveAt middle i := rfl
          rw [eta]
          omega
        obtain ⟨d1, d2⟩ := effective_ceiling_slot advanced i ceil capHigh room alignedHigh oldHigh
          funded (fun v read => by simpa [PinTerms.capAt, read] using capped)
        simp only at c1 c2 c3 c4 d1 d2 ⊢
        have eta : effectiveAt (⟨middle.fork, middle.state⟩ : ForkedBeaconState preset) i =
            effectiveAt middle i := rfl
        rw [eta] at d1 d2
        generalize min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh = bound
          at c1 d1 ⊢
        rcases d2 with ⟨keep, same⟩ | ⟨rise, later⟩
        · refine ⟨by omega, fun h => ?_, fun h => ?_, by omega⟩
          · rw [keep]
            exact c2 (by omega)
          · rw [keep]
            exact c3 (by omega)
        · refine ⟨by omega, fun h => by omega, fun _ => rise, by omega⟩

/-- A balance floor and a cap floor along a run give an effective-balance floor, rounded.

Its effective balance at the end is at least the least of three values.

They are its effective balance at the start, `capLow`, and `floor` rounded down to an increment. -/
theorem Run.effective_floor_rounded {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (floor capLow : ℕ)
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ PinTerms.capAt z i) :
    min (effectiveAt x i) (min capLow (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i :=
  (PinDrift.Internal.Run.effective_floor_pair tail early fulu i inside floor capLow 0 0 0 0).1
    balanceFloor
    capFloor

/-- A balance floor and a cap floor along a run give an effective-balance floor.

The key's effective balance at the end is at least the least of three values.

They are its starting effective balance, `capLow`, and `floor` less one increment of rounding. -/
private theorem Run.effective_floor_of_balance_floor {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (i : ℕ)
    (inside : i < x.state.validators.data.size) (floor capLow : ℕ)
    -- Suppose a key's balance stays at least `floor` at every state of a run.
    (balanceFloor : ∀ z ∈ tail.balancePath, floor ≤ actualBalanceAt z i)
    -- Suppose also that its cap stays at least `capLow`.
    (capFloor : ∀ z ∈ tail.balancePath, capLow ≤ PinTerms.capAt z i) :
    min (effectiveAt x i) (min capLow (floor + 1 - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt y i := by
  -- The floor rounded down to an increment is at least `floor + 1 - inc`.
  have remainder := Nat.mod_lt floor incPos
  refine Nat.le_trans ?_
    (PinDrift.Internal.Run.effective_floor_rounded tail early fulu i inside floor capLow
      balanceFloor capFloor)
  omega

/-- A balance ceiling and a cap ceiling along a run give an effective-balance ceiling.

The key's effective balance at the end is at most the greater of two values.

They are its effective balance at the start, and the ceiling rounded down, at most the cap. -/
theorem Run.effective_ceiling_of_balance_ceiling {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (ceil capHigh : ℕ)
    -- The bound `capHigh` is a whole number of increments.
    (alignedHigh : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    -- The effective balance at the start is at most `capHigh`.
    (startCap : effectiveAt x i ≤ capHigh)
    -- Suppose the smaller of a key's balance and `capHigh` stays at most `ceil` along a run.
    (balanceCeil : ∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ ceil)
    -- Suppose also that its cap stays at most `capHigh`.
    (capCeil : ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) :
    effectiveAt y i ≤ max (effectiveAt x i)
      (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
    -- If no epoch boundary is crossed, it is the effective balance at the start.
    ((getCurrentEpoch y.state).toNat ≤ (getCurrentEpoch x.state).toNat →
      effectiveAt y i = effectiveAt x i) ∧
    -- After a boundary, it is at most `ceil` plus the downward band.
    ((getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat →
      effectiveAt y i ≤ ceil + preset.downwardBand) ∧
    -- The epoch never moves back.
    (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat :=
  (PinDrift.Internal.Run.effective_floor_pair tail early fulu i inside 0 0 capHigh 0 0 0).2.2.1 ceil
    alignedHigh startCap balanceCeil capCeil

/-! ## The penalty rate of one key in a rewards pass -/

/-- One rewards pass debits a key at a state at a rate of at most the pin reserve's leak rate.

The rate is taken at the key's effective balance at the state. -/
theorem passPenaltyRate_le_leak (z : ForkedBeaconState preset) (v : ℕ) (pulledTotal : ℕ)
    (scoreBound : ℕ) (facts : PinPresetFacts preset)
    (pulledFits : pulledTotal < 2 ^ 64)
    -- Effective balances are whole increments.
    (aligned : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ effectiveAt z v)
    -- The state's total is at least two thirds of R's.
    --
    -- So its square root is at least the quarter's.
    (band : 2 * pulledTotal ≤ 3 * activeBalanceTotal z.state)
    -- The leak rate uses a bound on the pass's score after its update.
    --
    -- That score is the score plus one bias.
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤ scoreBound) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    -- Use a quarter of R's active balance from 18 increments.
    --
    -- Below that, use a fifth of an increment.
    --
    -- The reserve reads the base reward per increment at the quarter.
    let quarter := if 18 * inc ≤ pulledTotal then pulledTotal / 4 else inc / 5
    let perIncrement := inc * preset.BASE_REWARD_FACTOR.toNat / quarter.sqrt
    PinDrift.Internal.passPenaltyRate config z v ≤
      2 * (effectiveAt z v / inc * perIncrement) +
        effectiveAt z v * scoreBound /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  intro inc quarter perIncrement
  unfold PinDrift.Internal.passPenaltyRate
  let total := activeBalanceTotal z.state
  let score := if altair : .altair ≤ z.fork then
    (((z.state.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0
  have sizeInc : 10 ^ 8 ≤ inc := facts.incrementSize
  -- This makes the rounding of the per-increment reward lose less than its fraction.
  have roomy := Nat.le_trans (show 2 ^ 33 ≤ 2 ^ 35 by decide) facts.rewardScale
  have positive : 0 < inc := by omega
  have weights : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = 40 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  obtain ⟨k, hk⟩ := aligned
  have hinc : inc ≤ total := le_max_left _ _
  -- the numerator of the per-increment reward, `X`, dominates the square root of the quarter
  obtain ⟨X, hX⟩ : ∃ X, inc * preset.BASE_REWARD_FACTOR.toNat = X := ⟨_, rfl⟩
  rw [hX] at roomy
  have hp : perIncrement = X / quarter.sqrt := by
    simp only [perIncrement, hX]
  have incX : inc ≤ X := by
    rw [← hX]
    exact Nat.le_mul_of_pos_right _ (PinDrift.Internal.PinPresetFacts.reward facts)
  have quarterLe : quarter ≤ X ^ 2 := by
    by_cases big : 18 * inc ≤ pulledTotal
    · have : 2 ^ 66 ≤ X ^ 2 := by
        calc 2 ^ 66 = (2 ^ 33) ^ 2 := by norm_num
          _ ≤ X ^ 2 := Nat.pow_le_pow_left roomy 2
      have : pulledTotal / 4 < 2 ^ 62 := by omega
      simp only [quarter, big, ↓reduceIte]
      omega
    · simp only [quarter, big, ↓reduceIte]
      exact Nat.le_trans (Nat.div_le_self _ _)
        (Nat.le_trans incX (Nat.le_self_pow (by decide) _))
  have quarterTotal : quarter ≤ total := by
    by_cases big : 18 * inc ≤ pulledTotal
    · simp only [quarter, big, ↓reduceIte]
      have : 2 * pulledTotal ≤ 3 * total := band
      omega
    · simp only [quarter, big, ↓reduceIte]
      exact Nat.le_trans (Nat.div_le_self _ _) hinc
  have quarterPositive : 0 < quarter.sqrt := by
    refine Nat.sqrt_pos.mpr ?_
    by_cases big : 18 * inc ≤ pulledTotal
    · simp only [quarter, big, ↓reduceIte]
      omega
    · simp only [quarter, big, ↓reduceIte]
      omega
  have quarterRoot : quarter.sqrt ≤ X := by
    have := Nat.sqrt_le_sqrt quarterLe
    rwa [Nat.sqrt_eq'] at this
  have totalRoot : quarter.sqrt ≤ total.sqrt := Nat.sqrt_le_sqrt quarterTotal
  have perOne : 1 ≤ X / quarter.sqrt := (Nat.le_div_iff_mul_le quarterPositive).mpr (by omega)
  -- The flag term is `40 / 64` of a base reward per increment for each increment.
  --
  -- It fits in `2 * (increments * perIncrement)`.
  --
  -- The floor of a quotient that is at least one is at least half of it.
  have rewardRate : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v / (64 * total.sqrt) ≤
      2 * (effectiveAt z v / inc * perIncrement) := by
    have increments : effectiveAt z v / inc = k := by
      rw [hk, Nat.mul_div_cancel_left _ positive]
    have numerator : 40 * preset.BASE_REWARD_FACTOR.toNat * effectiveAt z v = 40 * (k * X) := by
      rw [hk, ← hX]
      ring
    have totalPositive : 0 < total.sqrt := Nat.lt_of_lt_of_le quarterPositive totalRoot
    rw [increments, numerator]
    calc 40 * (k * X) / (64 * total.sqrt)
        ≤ 40 * (k * X) / (40 * total.sqrt) :=
          Nat.div_le_div_left (Nat.mul_le_mul_right _ (by decide)) (by positivity)
      _ = k * X / total.sqrt := Nat.mul_div_mul_left _ _ (by decide)
      _ ≤ k * X / quarter.sqrt := Nat.div_le_div_left totalRoot quarterPositive
      _ ≤ 2 * (k * perIncrement) := by
        refine Nat.div_le_of_le_mul ?_
        have split : X < (X / quarter.sqrt + 1) * quarter.sqrt := by
          have := Nat.lt_mul_div_succ X quarterPositive
          rwa [Nat.mul_comm] at this
        have step : X ≤ 2 * perIncrement * quarter.sqrt := by
          have : (X / quarter.sqrt + 1) ≤ 2 * (X / quarter.sqrt) := by omega
          rw [hp]
          exact Nat.le_of_lt (Nat.lt_of_lt_of_le split (Nat.mul_le_mul_right _ this))
        calc k * X ≤ k * (2 * perIncrement * quarter.sqrt) := Nat.mul_le_mul_left _ step
          _ = quarter.sqrt * (2 * (k * perIncrement)) := by ring
  have scoreRate : effectiveAt z v * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
      effectiveAt z v * scoreBound /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat) :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ scored)
  exact Nat.add_le_add rewardRate scoreRate

/-! ## Credits to exiting keys along a run -/

/-! ## Deposits leave the balance of an exiting key alone -/

/-- Every exiting key of the first state keeps its balance in the second state. -/
def KeepsExiting {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) :
    Prop :=
  ∀ (i : ℕ) (v : Validator), s.validators.data[i]? = some v → v.exitEpoch.toNat < 2 ^ 64 - 1 →
    (getCurrentEpoch s).toNat < v.withdrawableEpoch.toNat →
    t.balances.data[i]? = s.balances.data[i]?

/-- Every deposit event of the list leaves the balance of an exiting key alone. -/
private def Quiet (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source = .deposits → PinDrift.Internal.KeepsExiting e.before.state e.after.state

/-- The event raises no balance of the registry. -/
def Unconditional (e : BalanceEvent preset) : Prop :=
  ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i

/-- The empty list of events is quiet. -/
private theorem quiet_nil : Quiet ([] : List (BalanceEvent preset)) := fun _ mem => by
  simp at mem

/-- A pass that records no event keeps the events quiet. -/
private theorem quiet_carry {f : Fork}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (ok : carryBalance action pre = .ok post) : Quiet post.2 := by
  rw [(PinDrift.Internal.carryBalance_cases ok).2]
  exact initial

/-- A recorded pass keeps the events quiet when its deposit action keeps exiting balances. -/
private theorem quiet_record {f : Fork} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (initial : Quiet pre.2)
    (keeps : source = .deposits → ∀ t, action pre.1 = .ok t → PinDrift.Internal.KeepsExiting pre.1
      t)
    (ok : recordBalance source limits action pre = .ok post) : Quiet post.2 := by
  obtain ⟨credit, debit, _, actionOk, events⟩ := recordBalance_single ok
  rw [events]
  intro e member sourceEq
  rcases List.mem_append.mp member with old | new
  · exact initial e old sourceEq
  · obtain rfl := List.mem_singleton.mp new
    exact keeps sourceEq _ actionOk

/-- A new validator with no balance never raises a balance. -/
private theorem addValidatorToRegistry_zero_balance {f : Fork} {s t : BeaconState preset f}
    (altair : .altair ≤ f) {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32}
    (ok : addValidatorToRegistry s pubkey credentials 0 = .ok t) (i : ℕ) :
    ((t.balances.data[i]?).map (·.toNat)).getD 0 ≤
      ((s.balances.data[i]?).map (·.toNat)).getD 0 := by
  unfold addValidatorToRegistry at ok
  simp only [altair, ↓reduceDIte, addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, balancesOk, _, _, _, _, _, _, rfl⟩ := ok
  show ((_ : Option Gwei).map (·.toNat)).getD 0 ≤ _
  rw [setOrAppendList_getElem? balancesOk]
  split <;> simp

/-- From Electra, a block deposit raises no balance. -/
private theorem processDeposit_balance_le {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) {before : f < .hegota} {dep : Deposit}
    (ok : processDeposit config checks before s dep = .ok t) (i : ℕ) :
    actualBalanceAt ⟨f, t⟩ i ≤ actualBalanceAt ⟨f, s⟩ i := by
  obtain ⟨-, -, next, -, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, middle, pending, rfl | added, rfl⟩ |
      ⟨early, _⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact addValidatorToRegistry_zero_balance (Nat.le_trans (by decide) electra) added i
  · exact absurd (Nat.lt_of_lt_of_le early electra) (Nat.lt_irrefl _)

/-- A property of the events of a block replay that each recorded event keeps.

Every operation of a block records an event of its own source.

The deposits of the block are the only events of the source `.deposits`.

No operation of a block records the source `.consolidations`. -/
private theorem blockReplay_invariant {f : Fork} (electra : .pectra ≤ f) (early : f < .glamsterdam)
    (P : List (BalanceEvent preset) → Prop) (nil : P [])
    (ordinary : ∀ (l : List (BalanceEvent preset)) (e : BalanceEvent preset),
      e.source ≠ .deposits → e.source ≠ .consolidations → P l → P (l ++ [e]))
    (deposit : ∀ (l : List (BalanceEvent preset)) (s t : BeaconState preset f)
      (before : f < .hegota) (dep : Deposit) (credit debit : ℕ), P l →
      processDeposit config checks before s dep = .ok t →
      P (l ++ [⟨.deposits, ⟨f, s⟩, ⟨f, t⟩, credit, debit⟩]))
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : P post.2 := by
  have carry {pre post : BalanceReplay preset f}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (initial : P pre.2) (ok : carryBalance action pre = .ok post) : P post.2 := by
    rw [(PinDrift.Internal.carryBalance_cases ok).2]
    exact initial
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notDeposit : source ≠ .deposits) (notConsolidation : source ≠ .consolidations)
      (initial : P pre.2) (ok : recordBalance source limits action pre = .ok post) :
      P post.2 := by
    obtain ⟨credit, debit, -, -, events⟩ := recordBalance_single ok
    rw [events]
    exact ordinary _ _ notDeposit notConsolidation initial
  have altair : .altair ≤ f := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ f := Nat.le_trans (by decide) electra
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headedOk, rest⟩ := bind_ok_iff.mp ok
  have headedQuiet := carry nil headedOk
  simp only [bellatrix, ↓reduceDIte] at rest
  obtain ⟨executed, executedOk, rest⟩ := bind_ok_iff.mp rest
  have executedQuiet := record (by decide : BalanceSource.withdrawals ≠ .deposits)
    (by decide) headedQuiet executedOk
  simp only [bind_ok_iff] at rest
  obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
    proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
    exited, exitOk, changed, changedOk, rest⟩ := rest
  have randaoQuiet := carry executedQuiet randaoOk
  have votedQuiet := carry randaoQuiet votedOk
  have proposedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    votedQuiet proposedOk
  have attestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.slashings ≠ .deposits) (by decide) h ok)
    proposedQuiet attestedOk
  have rewardedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.rewards ≠ .deposits) (by decide) h ok)
    attestedQuiet rewardedOk
  have depositedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun pre dep post h ok => by
      obtain ⟨credit, debit, _, actionOk, events⟩ := recordBalance_single ok
      rw [events]
      exact deposit _ _ _ _ _ _ _ h actionOk)
    rewardedQuiet depositOk
  have exitedQuiet := carry depositedQuiet exitOk
  have changedQuiet := carry exitedQuiet changedOk
  simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
    requested, consolidations, rest⟩ := rest
  have depositsQuiet := carry changedQuiet depositRequestOk
  have withdrawalsQuiet := carry depositsQuiet withdrawalOk
  have requestedQuiet := foldlM_ok_invariant (fun p => P p.2)
    (fun _ _ _ h ok => record (by decide : BalanceSource.excess ≠ .deposits) (by decide) h ok)
    withdrawalsQuiet consolidations
  simp only [altair, ↓reduceDIte] at rest
  exact record (by decide : BalanceSource.sync ≠ .deposits) (by decide) requestedQuiet rest

/-- From Electra, the deposit events of a block replay raise no balance. -/
theorem blockReplay_unconditional {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam)
    (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) :
    ∀ e ∈ post.2, e.source = .deposits → PinDrift.Internal.Unconditional e :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source = .deposits →
    PinDrift.Internal.Unconditional e)
    (fun _ h => by simp at h)
    (fun l e notDeposit _ held e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · exact absurd ((List.mem_singleton.mp new) ▸ sourceEq) notDeposit)
    (fun l s t _ dep credit debit held computed e' member sourceEq => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        exact fun i => processDeposit_balance_le electra computed i)
    engine s block ok

/-- No operation of a block records a consolidation event. -/
theorem blockReplay_noConsolidations {f : Fork} (electra : .pectra ≤ f)
    (early : f < .glamsterdam) (engine : ExecutionEngine preset f) (s : BeaconState preset f)
    (block : BeaconBlock preset f) {post : BalanceReplay preset f}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) : ∀ e ∈ post.2, e.source ≠ .consolidations :=
  blockReplay_invariant electra early (fun l => ∀ e ∈ l, e.source ≠ .consolidations)
    (fun _ h => by simp at h)
    (fun l e _ notConsolidation held e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · exact (List.mem_singleton.mp new) ▸ notConsolidation)
    (fun l s t _ dep credit debit held _ e' member => by
      rcases List.mem_append.mp member with old | new
      · exact held e' old
      · obtain rfl := List.mem_singleton.mp new
        exact fun eq => by cases eq)
    engine s block ok

/-- The deposit events of an epoch replay leave the balance of an exiting key alone.

The pending deposits of an epoch are the only deposit events of the replay. -/
private theorem epochReplay_quiet {f : Fork} {s : BeaconState preset f}
    {post : BalanceReplay preset f}
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    Quiet post.2 := by
  refine (epochBalanceReplay_trace ok).transport
    (fun a b : BalanceReplay preset f => Quiet a.2 → Quiet b.2)
    (fun _ => id) (fun one two held => two (one held)) ?_ quiet_nil
  intro k member pre after step held
  cases k <;> simp only [epochReplayAction] at step
  case justification | registry => exact quiet_carry held step
  case inactivity | eth1Reset =>
    split at step
    · exact quiet_carry held step
    · cases step; exact held
  case rewards =>
    exact replayRewards_induction (fun pre => Quiet pre.2)
      (fun prior ok => quiet_record prior (fun eq => by cases eq) ok)
      (fun penalty prior ok => quiet_record prior
        (fun eq => by rcases penalty with rfl | rfl <;> cases eq) ok) held step
  case slashings => exact quiet_record held (fun eq => by cases eq) step
  case pendingDeposits =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨deposited, depositedOk, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        intro i v found exited withdrawable
        exact PinDrift.Internal.processPendingDeposits_exited_balance depositedOk found exited
          withdrawable
    · cases step; exact held
  case pendingConsolidations =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨consolidated, -, rfl⟩ := step
      intro e member sourceEq
      rcases List.mem_append.mp member with old | new
      · exact held e old sourceEq
      · obtain rfl := List.mem_singleton.mp new
        cases sourceEq
    · cases step; exact held
  all_goals simp [EpochStage.prefixStages] at member

/-- The deposit events of a slot step leave the balance of an exiting key alone. -/
private theorem slot_quiet {x y : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks x = .ok y)
    (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events) :
    Quiet events := by
  obtain ⟨advanced, cached, crossings, -, -, -, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  have crossed : Quiet crossings := fun e member sourceEq => by
    cases (upgradeBalanceReplay_crossing crossingOk e member).symm.trans sourceEq
  rcases split with ⟨-, rfl⟩ | ⟨middle, updated, recorded, recordOk, -, -, -, rfl, -⟩
  · exact crossed
  · intro e member sourceEq
    rcases List.mem_append.mp member with old | new
    · exact epochReplay_quiet recordOk e old sourceEq
    · exact crossed e new sourceEq

/-- A deposit event of a run raises no balance, or it is an epoch's deposit event of a slot step.

Then it leaves the balance of an exiting key alone. -/
def Located {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (e : BalanceEvent preset) : Prop :=
  PinDrift.Internal.Unconditional e ∨ ∃ (u w : ForkedBeaconState preset)
    (ok : advanceSlotAcross config checks u = .ok w) (es : List (BalanceEvent preset)),
    tail.Contains (Step.slot ok) ∧ (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧
      e ∈ es ∧ PinDrift.Internal.KeepsExiting e.before.state e.after.state

/-- Locate each deposit event and each consolidation event of a run.

A deposit event raises no balance, or it is in the events of a slot step of the run.

A consolidation event is in the events of a slot step of the run, since no block records one. -/
theorem run_located {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (∀ e ∈ events, e.source = .deposits → PinDrift.Internal.Located tail e) ∧
      (∀ e ∈ events, e.source = .consolidations →
        ∃ (u w : ForkedBeaconState preset) (ok : advanceSlotAcross config checks u = .ok w)
          (es : List (BalanceEvent preset)), tail.Contains (Step.slot ok) ∧
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧ e ∈ es) := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    exact ⟨fun e member => by simp at member, fun e member => by simp at member⟩
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    obtain ⟨priorLocated, priorSlot⟩ := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    have lift : ∀ e, PinDrift.Internal.Located pre e → PinDrift.Internal.Located (pre.snoc step) e
      := by
      rintro e (unconditional | ⟨u, w, ok, es, contains, replayedEs, member, keeps⟩)
      · exact .inl unconditional
      · exact .inr ⟨u, w, ok, es, .earlier contains step, replayedEs, member, keeps⟩
    have liftSlot : ∀ e, (∃ (u w : ForkedBeaconState preset)
        (ok : advanceSlotAcross config checks u = .ok w) (es : List (BalanceEvent preset)),
        pre.Contains (Step.slot ok) ∧
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧ e ∈ es) →
        ∃ (u w : ForkedBeaconState preset) (ok : advanceSlotAcross config checks u = .ok w)
          (es : List (BalanceEvent preset)), (pre.snoc step).Contains (Step.slot ok) ∧
          (Step.slot ok : Step config checks u w).balanceEvents = .ok es ∧ e ∈ es := by
      rintro e ⟨u, w, ok, es, contains, replayedEs, member⟩
      exact ⟨u, w, ok, es, .earlier contains step, replayedEs, member⟩
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have inFork : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      refine ⟨fun e member sourceEq => ?_, fun e member sourceEq => ?_⟩
      · rcases List.mem_append.mp member with old | new
        · exact lift e (priorLocated e old sourceEq)
        · cases step with
          | block engine signed due ok =>
            exact .inl (PinDrift.Internal.blockReplay_unconditional inFork early engine _ _
              (Step.balanceEvents_block early addedOk) e new sourceEq)
          | slot ok =>
            exact .inr ⟨_, _, ok, added, .last pre _, addedOk, new,
              slot_quiet ok early addedOk e new sourceEq⟩
      · rcases List.mem_append.mp member with old | new
        · exact liftSlot e (priorSlot e old sourceEq)
        · cases step with
          | block engine signed due ok =>
            exact absurd sourceEq (PinDrift.Internal.blockReplay_noConsolidations inFork early
              engine _ _
              (Step.balanceEvents_block early addedOk) e new)
          | slot ok => exact ⟨_, _, ok, added, .last pre _, addedOk, new⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      exact ⟨fun e member sourceEq => lift e (priorLocated e member sourceEq),
        fun e member sourceEq => liftSlot e (priorSlot e member sourceEq)⟩

/-! ## Consolidation credits of one pass -/

/-- The stake that a pending consolidation can move at a pass: the source's effective balance.

It counts only a source that is unslashed and can withdraw by the next epoch.

A pass reads the other sources without moving anything. -/
private def sourceBound {f : Fork} (s : BeaconState preset f) (next : Epoch)
    (c : PendingConsolidation) : ℕ :=
  match s.validators.data[c.sourceIndex.toNat]? with
  | some v => if v.slashed = false ∧ v.withdrawableEpoch ≤ next then v.effectiveBalance.toNat else 0
  | none => 0

/-- The credits of the balances at some positions, from one state to another. -/
private def creditedAt {f : Fork} (T : Finset ℕ) (s t : BeaconState preset f) : ℕ :=
  ∑ j ∈ T, (actualBalanceAt ⟨f, t⟩ j - actualBalanceAt ⟨f, s⟩ j)

/-- The credits at some positions telescope along two steps. -/
private theorem creditedAt_trans {f : Fork} (T : Finset ℕ) {a b c : BeaconState preset f} :
    creditedAt T a c ≤ creditedAt T a b + creditedAt T b c := by
  unfold creditedAt
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => by omega

/-- One transfer of a pass credits at most the amount moved, and only at its target. -/
private theorem creditedAt_transfer {f : Fork} (T : Finset ℕ)
    {s lowered raised : BeaconState preset f} {source target : ValidatorIndex} {moved : Gwei}
    (lowerOk : decreaseBalance s source moved = .ok lowered)
    (raiseOk : increaseBalance lowered target moved = .ok raised) :
    creditedAt T s raised ≤ if target.toNat ∈ T then moved.toNat else 0 := by
  have sizes := (sameSizes_increaseBalance raiseOk).2.trans (sameSizes_decreaseBalance lowerOk).2
  unfold creditedAt
  have pointwise : ∀ j, actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j ≤
      if target.toNat = j then moved.toNat else 0 := by
    intro j
    by_cases inside : j < s.balances.data.size
    · obtain ⟨balance, found⟩ : ∃ balance, s.balances.data[j]? = some balance :=
        ⟨_, Array.getElem?_eq_getElem inside⟩
      obtain ⟨down, downFound, downEq⟩ := balance_decreaseBalance lowerOk found
      obtain ⟨up, upFound, upEq⟩ := balance_increaseBalance raiseOk downFound
      simp only [actualBalanceAt, found, upFound, Option.map_some, Option.getD_some]
      split at downEq <;> split at upEq <;> split <;> omega
    · have missing : s.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      have outside : raised.balances.data[j]? = Option.none := Array.getElem?_eq_none (by omega)
      simp [actualBalanceAt, missing, outside]
  calc ∑ j ∈ T, (actualBalanceAt ⟨f, raised⟩ j - actualBalanceAt ⟨f, s⟩ j)
      ≤ ∑ j ∈ T, if target.toNat = j then moved.toNat else 0 :=
        Finset.sum_le_sum fun j _ => pointwise j
    _ = if target.toNat ∈ T then moved.toNat else 0 := by rw [Finset.sum_ite_eq]

/-- A pass credits the targets in `T` at most the effective balances of the due sources it reads.

The sources are those of the entries whose target is in `T`.

It keeps the registry and the number of balances. -/
private theorem pass_credits_le_targets {f : Fork} (next : Epoch) (T : Finset ℕ) :
    ∀ (items : List PendingConsolidation) {s t : BeaconState preset f} {read : ℕ},
      passPendingConsolidations next s items = .ok (t, read) →
      t.validators = s.validators ∧ t.balances.data.size = s.balances.data.size ∧
        creditedAt T s t ≤
          (((items.take read).filter fun c => c.targetIndex.toNat ∈ T).map
            (sourceBound s next)).sum
  | [], s, t, read, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    refine ⟨rfl, rfl, ?_⟩
    simp [creditedAt, actualBalanceAt]
  | c :: rest, s, t, read, computed => by
    simp only [passPendingConsolidations, liftAccessor, bind_ok_iff, mapError_ok_iff] at computed
    obtain ⟨source, sourceRead, computed⟩ := computed
    have found := getValidator_eq_ok_iff.mp sourceRead
    have bound : sourceBound s next c = if source.slashed = false ∧ source.withdrawableEpoch ≤ next
        then source.effectiveBalance.toNat else 0 := by
      simp [sourceBound, found]
    by_cases slashed : source.slashed = true
    · simp only [slashed, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at computed
      obtain ⟨⟨state', read'⟩, passed, rfl, rfl⟩ := computed
      obtain ⟨validators, sizes, credits⟩ := pass_credits_le_targets next T rest passed
      refine ⟨validators, sizes, ?_⟩
      by_cases inT : c.targetIndex.toNat ∈ T <;>
        simpa [bound, slashed, List.take_succ_cons, List.filter_cons, inT] using credits
    · replace slashed : source.slashed = false := by simpa using slashed
      by_cases early : next < source.withdrawableEpoch
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨rfl, rfl⟩ := computed
        refine ⟨rfl, rfl, ?_⟩
        simp [creditedAt, actualBalanceAt]
      · simp only [slashed, early, Bool.false_eq_true, ↓reduceIte, bind_ok_iff,
          mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
        obtain ⟨balance, -, lowered, loweredOk, raised, raisedOk,
          ⟨state', read'⟩, passed, rfl, rfl⟩ := computed
        obtain ⟨validators, sizes, credits⟩ := pass_credits_le_targets next T rest passed
        have sameValidators := (increaseBalance_validators raisedOk).trans
          (decreaseBalance_validators loweredOk)
        have step := creditedAt_transfer T loweredOk raisedOk
        have sizeStep := (sameSizes_increaseBalance raisedOk).2.trans
          (sameSizes_decreaseBalance loweredOk).2
        have moved : (min balance source.effectiveBalance).toNat ≤
            source.effectiveBalance.toNat := by
          rw [Uint64.toNat_min]; exact Nat.min_le_right _ _
        have restBound : (((rest.take read').filter fun c => c.targetIndex.toNat ∈ T).map
            (sourceBound raised next)) =
            (((rest.take read').filter fun c => c.targetIndex.toNat ∈ T).map
              (sourceBound s next)) := by
          congr 1
          funext d
          simp only [sourceBound, sameValidators]
        refine ⟨validators.trans sameValidators, sizes.trans sizeStep, ?_⟩
        have total := creditedAt_trans T (a := s) (b := raised) (c := state')
        rw [restBound] at credits
        have isDue : sourceBound s next c = source.effectiveBalance.toNat := by
          rw [bound]; simp [slashed, UInt64.not_lt.mp early]
        by_cases inT : c.targetIndex.toNat ∈ T
        · simp only [inT, ↓reduceIte] at step
          simp only [List.take_succ_cons, List.filter_cons, inT, decide_true, ↓reduceIte,
            List.map_cons, List.sum_cons, isDue]
          omega
        · simp only [inT, ↓reduceIte] at step
          simp only [List.take_succ_cons, List.filter_cons, inT, decide_false,
            Bool.false_eq_true, ↓reduceIte]
          omega

/-! ## The queue of a run from X, and the stake a pass can move -/

/-- From Electra on, the funding sources are the pending consolidations. -/
private theorem fundingSources_eq {f : Fork} (electra : .pectra ≤ f) (s : BeaconState preset f) :
    fundingSources s = (s.pendingConsolidations electra).data.toList := by
  simp [fundingSources, electra]

/-- The queue is the unread part of X's queue, then entries that are new since X.

Every new entry has a source whose exit was assigned after `e0`, the epoch of X. -/
private def Shape (L : List PendingConsolidation) (e0 : Epoch) (n : ℕ) {f : Fork}
    (z : BeaconState preset f) : Prop :=
  ∃ N : List PendingConsolidation, fundingSources z = L.drop n ++ N ∧
    ∀ c ∈ N, ∃ w, z.validators.data[c.sourceIndex.toNat]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH

/-- An assigned exit stays fixed, so its queue entry still has a source that exited after `e0`. -/
private theorem carry_source_exit {e0 : Epoch} {i : ℕ} {f g : Fork}
    {a : BeaconState preset f} {b : BeaconState preset g} (life : RegistryLifecycle a b)
    (source : ∃ w, a.validators.data[i]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ w, b.validators.data[i]? = some w ∧
      e0 < w.exitEpoch ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨w, read, later, assigned⟩ := source
  obtain ⟨w', read', kept⟩ := life.validators i w read
  exact ⟨w', read', by rw [kept.exitEpoch assigned]; exact ⟨later, assigned⟩⟩

/-- A state of any fork with the same queue and a later life of its validators has the shape. -/
private theorem Shape.carry {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f g : Fork}
    {a : BeaconState preset f} {b : BeaconState preset g} (shape : Shape L e0 n a)
    (queue : fundingSources b = fundingSources a) (life : RegistryLifecycle a b) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  exact ⟨N, queue.trans eq, fun c member => carry_source_exit life (new c member)⟩

/-- A block that grows the queue keeps the shape. -/
private theorem Shape.grow {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ} {f : Fork}
    {a b : BeaconState preset f} (electra : .pectra ≤ f) (shape : Shape L e0 n a)
    (grows : ConsolidationQueueRise.Appends a b) (life : RegistryLifecycle a b)
    (started : e0 ≤ getCurrentEpoch a) :
    Shape L e0 n b := by
  obtain ⟨N, eq, new⟩ := shape
  obtain ⟨added, queue, fresh⟩ := grows electra
  refine ⟨N ++ added, by rw [fundingSources_eq electra, queue, ← fundingSources_eq electra, eq,
    List.append_assoc], fun c member => ?_⟩
  rcases List.mem_append.mp member with old | recent
  · exact carry_source_exit life (new c old)
  · obtain ⟨w, read, later, assigned⟩ := fresh c recent
    exact ⟨w, read, UInt64.lt_of_le_of_lt started later, assigned⟩

/-- A pass that reads `r` entries moves the shape on by `r`. -/
private theorem Shape.pass {L : List PendingConsolidation} {e0 : Epoch} {n r : ℕ} {f : Fork}
    {a b : BeaconState preset f} (shape : Shape L e0 n a)
    (queue : fundingSources b = (fundingSources a).drop r) (life : RegistryLifecycle a b) :
    Shape L e0 (n + r) b := by
  obtain ⟨N, eq, new⟩ := shape
  refine ⟨N.drop (r - (L.length - n)), ?_, fun c member => ?_⟩
  · rw [queue, eq, List.drop_append, List.drop_drop]
    simp [List.length_drop]
  · exact carry_source_exit life (new c (List.mem_of_mem_drop member))

/-- The stake that X lets a pending consolidation move: the cap of its source at X.

It counts only a source that is unslashed at X and can withdraw by `high + 1`. -/
private def capBound (x : ForkedBeaconState preset) (high : ℕ) (c : PendingConsolidation) : ℕ :=
  match x.state.validators.data[c.sourceIndex.toNat]? with
  | some v =>
    if v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 then
      (withdrawalMaxEffectiveBalance preset x.fork v).toNat
    else 0
  | none => 0

/-- A key that cannot switch to compounding credentials has a cap that does not rise. -/
private theorem withdrawalMax_le {f g : Fork} (hf : .pectra ≤ f) (hg : .pectra ≤ g)
    (caps : CapOrder preset) {v w : Validator}
    (frozen : hasCompoundingWithdrawalCredential w = true →
      hasCompoundingWithdrawalCredential v = true) :
    withdrawalMaxEffectiveBalance preset f w ≤ withdrawalMaxEffectiveBalance preset g v := by
  simp only [withdrawalMaxEffectiveBalance, hf, hg, ↓reduceIte, getMaxEffectiveBalance]
  by_cases hw : hasCompoundingWithdrawalCredential w = true
  · simp [hw, frozen hw]
  · by_cases hv : hasCompoundingWithdrawalCredential v = true
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact caps.compounding
    · simp only [hw, hv, Bool.false_eq_true, ↓reduceIte]
      exact UInt64.le_refl _

/-- What a run from X, at a state `p` of the epoch pass, knows about the pending consolidations. -/
private structure PassFacts (x : ForkedBeaconState preset) (high : ℕ) {f : Fork}
    (p : BeaconState preset f) : Prop where
  electraX : .pectra ≤ x.fork
  electraP : .pectra ≤ f
  caps : CapOrder preset
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  life : RegistryLifecycle x.state p
  cap : Internal.CapStep config x.state p
  orderedX : PendingConsolidationsOrdered config (getCurrentEpoch x.state).toNat x.state
  invariantP : PendingConsolidationInvariant config p
  cappedX : ∀ v ∈ x.state.validators.data,
    v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset x.fork v
  next : (getCurrentEpoch p).toNat + 1 ≤ high + 1
  nextNat : (getCurrentEpoch p + 1).toNat = (getCurrentEpoch p).toNat + 1

/-- An entry of X's queue, still queued at the pass, moves at most its cap at X. -/
private theorem old_entry_bound {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inX : c ∈ (x.state.pendingConsolidations facts.electraX).data.toList)
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) :
    sourceBound p (getCurrentEpoch p + 1) c ≤ capBound x high c := by
  obtain ⟨v, foundX, -, -, assignedX⟩ := (facts.orderedX.1 facts.electraX).2 c inX
  obtain ⟨-, unslashedX, -⟩ := (facts.orderedX.2 facts.electraX).2 c inX v foundX
  obtain ⟨wP, foundP', -, exitDelayP, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain ⟨w, foundP, lifecycle⟩ := facts.life.validators _ v foundX
  obtain rfl : w = wP := Option.some.inj (foundP.symm.trans foundP')
  simp only [sourceBound, capBound, foundP, foundX]
  split
  · rename_i due
    have exitEq := lifecycle.exitEpoch assignedX
    have slashedX : v.slashed = false := by
      cases flag : v.slashed
      · rfl
      · have := ((facts.cap.withdrawal _ v w foundX foundP).1 flag assignedX).1
        rw [due.1] at this
        cases this
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    have withdrawX := unslashedX slashedX
    rw [facts.nextNat] at dueNat
    have exitNat := congrArg UInt64.toNat exitEq
    have exitDelay : w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        w.withdrawableEpoch.toNat := exitDelayP
    have dueX : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1 :=
      ⟨slashedX, by have := facts.next; omega⟩
    simp only [dueX, and_self, ↓reduceIte]
    have capped : w.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset f w :=
      facts.cap.capped facts.cappedX w (Array.mem_of_getElem? foundP)
    have bounded := withdrawalMax_le facts.electraP facts.electraX facts.caps
      ((facts.cap.frozen _ v w foundX foundP assignedX).2)
    exact UInt64.le_iff_toNat_le.mp (UInt64.le_trans capped bounded)
  · exact Nat.zero_le _

/-- An entry that is new since X moves nothing at the pass.

Its source exits after X, so it withdraws after the run. -/
private theorem new_entry_zero {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p : BeaconState preset f} (facts : PassFacts (config := config) x high p)
    {c : PendingConsolidation}
    (inP : c ∈ (p.pendingConsolidations facts.electraP).data.toList) {w : Validator}
    (foundW : p.validators.data[c.sourceIndex.toNat]? = some w)
    (fresh : getCurrentEpoch x.state < w.exitEpoch) :
    sourceBound p (getCurrentEpoch p + 1) c = 0 := by
  obtain ⟨w', found', -, exitDelay, -⟩ := (facts.invariantP facts.electraP).2 c inP
  obtain rfl : w' = w := Option.some.inj (found'.symm.trans foundW)
  have later := UInt64.lt_iff_toNat_lt.mp fresh
  simp only [sourceBound, foundW]
  split
  · rename_i due
    have dueNat := UInt64.le_iff_toNat_le.mp due.2
    rw [facts.nextNat] at dueNat
    have := facts.next
    have := facts.within
    have := facts.delay
    omega
  · rfl

/-- A pass, from a state with the shape, credits the targets in `T` at most the caps at X.

The caps are those of the entries it reads whose target is in `T`. -/
private theorem pass_step_targets {x : ForkedBeaconState preset} {high : ℕ} {f : Fork}
    {p t : BeaconState preset f} {n : ℕ} (facts : PassFacts (config := config) x high p)
    (shape : Shape (x.state.pendingConsolidations facts.electraX).data.toList
      (getCurrentEpoch x.state) n p)
    (computed : processPendingConsolidations p facts.electraP = .ok t) :
    ∃ r, Shape (x.state.pendingConsolidations facts.electraX).data.toList
        (getCurrentEpoch x.state) (n + r) t ∧ RegistryLifecycle p t ∧
      ∀ T : Finset ℕ, creditedAt T p t ≤
        (((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take r).filter
          fun c => c.targetIndex.toNat ∈ T).map (capBound x high)).sum := by
  obtain ⟨result, passed, balancesEq, queueEq⟩ := processPendingConsolidations_pass computed
  have sameValidators := (processPendingConsolidations_kept computed).1
  have life : RegistryLifecycle p t := .of_data (congrArg (·.data) sameValidators)
  have queue : fundingSources t = (fundingSources p).drop result.2 := by
    rw [fundingSources_eq facts.electraP, fundingSources_eq facts.electraP]
    exact queueEq
  refine ⟨result.2, shape.pass queue life, life, fun T => ?_⟩
  obtain ⟨-, -, credits⟩ :=
    pass_credits_le_targets (getCurrentEpoch p + 1) T _ passed
  have creditsEq : creditedAt T p t = creditedAt T p result.1 := by
    simp [creditedAt, actualBalanceAt, balancesEq]
  rw [creditsEq]
  refine Nat.le_trans credits ?_
  obtain ⟨N, eq, new⟩ := shape
  rw [← fundingSources_eq facts.electraP, eq, List.take_append, List.filter_append,
    List.map_append, List.sum_append]
  have oldPart : (((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take
      result.2).filter fun c => c.targetIndex.toNat ∈ T).map
        (sourceBound p (getCurrentEpoch p + 1))).sum ≤
      (((((x.state.pendingConsolidations facts.electraX).data.toList.drop n).take
        result.2).filter fun c => c.targetIndex.toNat ∈ T).map (capBound x high)).sum := by
    apply List.sum_le_sum
    intro c member
    have inDrop := List.mem_of_mem_take (List.mem_of_mem_filter member)
    refine old_entry_bound facts (List.mem_of_mem_drop inDrop) ?_
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_left _ inDrop
  have newPart : (((N.take (result.2 -
      ((x.state.pendingConsolidations facts.electraX).data.toList.drop n).length)).filter
        fun c => c.targetIndex.toNat ∈ T).map
        (sourceBound p (getCurrentEpoch p + 1))).sum = 0 := by
    apply List.sum_eq_zero
    intro m member
    obtain ⟨c, inTake, rfl⟩ := List.mem_map.mp member
    have inN := List.mem_of_mem_take (List.mem_of_mem_filter inTake)
    obtain ⟨w, foundW, fresh, -⟩ := new c inN
    refine new_entry_zero facts ?_ foundW fresh
    rw [← fundingSources_eq facts.electraP, eq]
    exact List.mem_append_right _ inN
  omega

/-- The upgrades due at a slot keep the shape of the queue. -/
private theorem upgrade_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (shape : Shape L e0 n pre.state)
    (ok : upgradeNext config checks pre = .ok post) (early : post.val.fork < .glamsterdam) :
    .pectra ≤ post.val.fork ∧ Shape L e0 n post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.phase0 < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.altair < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.bellatrix < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.shapella < Fork.pectra))
  · exact absurd electra (Nat.not_le_of_lt (by decide : Fork.dencun < Fork.pectra))
  · obtain ⟨_, upgraded, rfl⟩ := ok
    refine ⟨(by decide : Fork.pectra ≤ Fork.fusaka),
      shape.carry ?_ (.of_data (upgradeToFulu_spec upgraded).1)⟩
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    simp [fundingSources, carryFields, carryList, carryRooted,
      show Fork.pectra ≤ Fork.fusaka from by decide]
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.not_le_of_lt early (show Fork.glamsterdam ≤ .hegota from by decide))

/-- All the upgrades of a step keep the shape of the queue, as each one does. -/
private theorem upgrades_shape {L : List PendingConsolidation} {e0 : Epoch} {n : ℕ}
    {advanced last : ForkedBeaconState preset} (electra : .pectra ≤ advanced.fork)
    (early : last.fork < .glamsterdam) (shape : Shape L e0 n advanced.state)
    (ok : processUpgrades config checks advanced = .ok last) : Shape L e0 n last.state := by
  have rest := processUpgrades_induction
    (property := fun z => z.fork < .glamsterdam → .pectra ≤ z.fork ∧ Shape L e0 n z.state)
    (fun {pre post} h ok early => by
      obtain ⟨electraPre, shapePre⟩ := h (Nat.lt_trans post.property early)
      exact upgrade_shape electraPre shapePre ok early)
    (fun _ => ⟨electra, shape⟩) ok
  exact (rest early).2

/-! ## The stages of an epoch -/

/-- The order of the pending consolidations of a state at its own epoch. -/
private abbrev OrderedAt {f : Fork} (config : Config) (s : BeaconState preset f) : Prop :=
  PendingConsolidationsOrdered config (getCurrentEpoch s).toNat s

/-- A stage other than the pass keeps the slot, the queue and the order, and the lifecycle. -/
private theorem stage_rel {f : Fork} (electra : .pectra ≤ f) {k : EpochStage}
    (notPass : k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (edge : EpochStage.Edge config checks k a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  refine ⟨edge.registryLifecycle, edge.slot_eq, ?_, edge.pendingConsolidationsOrdered⟩
  rw [fundingSources_eq electra, fundingSources_eq electra,
    show b.pendingConsolidations = a.pendingConsolidations from edge.samePendingQueue notPass]

/-- The stages before the pass, from the cached state, keep what the pass reads. -/
private theorem prefix_rel {f : Fork} (electra : .pectra ≤ f) {stages : List EpochStage}
    (notPass : ∀ k ∈ stages, k ≠ .pendingConsolidations) {a b : BeaconState preset f}
    (trace : EpochTrace (EpochStage.action config checks) stages a b) :
    RegistryLifecycle a b ∧ b.slot = a.slot ∧ fundingSources b = fundingSources a ∧
      (OrderedAt config a → OrderedAt config b) := by
  apply trace.transport
    (fun a b : BeaconState preset f => RegistryLifecycle a b ∧ b.slot = a.slot ∧
      fundingSources b = fundingSources a ∧ (OrderedAt config a → OrderedAt config b))
    (fun _ => ⟨.refl _, rfl, rfl, id⟩)
    (fun one two => ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
      two.2.2.2 ∘ one.2.2.2⟩)
  intro k member s t computed
  exact stage_rel electra (notPass k member) (EpochStage.action_cases.mp computed)

/-- The events that the replay of the rewards records are rewards, penalties or inactivity. -/
private theorem rewards_noConsolidations {f : Fork} {pre post : BalanceReplay preset f}
    (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (ok : replayRewards (config := config) pre = .ok post) :
    ∀ e ∈ post.2, e.source ≠ .consolidations := by
  have record {pre post : BalanceReplay preset f} {source : BalanceSource}
      {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
      (notConsolidation : source ≠ .consolidations)
      (initial : ∀ e ∈ pre.2, e.source ≠ .consolidations)
      (ok : recordBalance source limits action pre = .ok post) :
      ∀ e ∈ post.2, e.source ≠ .consolidations := fun e member => by
    obtain ⟨_, _, _, _, events⟩ := recordBalance_single ok
    rcases PinDrift.Internal.mem_or_source_of_append events rfl member with old | new
    · exact initial e old
    · exact new ▸ notConsolidation
  exact replayRewards_induction (fun pre => ∀ e ∈ pre.2, e.source ≠ .consolidations)
    (fun prior ok => record (by decide) prior ok)
    (fun penalty prior ok => record (by rcases penalty with rfl | rfl <;> decide) prior ok)
    initial ok

/-- The queue of X. -/
private abbrev queueX (x : ForkedBeaconState preset) (h : .pectra ≤ x.fork) :
    List PendingConsolidation :=
  (x.state.pendingConsolidations h).data.toList

/-- A slot step moves the shape of the queue on.

It credits the targets in `T` at most the caps of the entries it reads that have such a target. -/
private theorem slot_step_targets {g x m last : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (electra : .pectra ≤ x.fork)
    (high : ℕ) (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ok : advanceSlotAcross config checks m = .ok last) (early : last.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch last.state).toNat ≤ high + 1) {n : ℕ}
    (shape : Shape (queueX x electra) (getCurrentEpoch x.state) n m.state) :
    ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
      ∀ {events : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks m last).balanceEvents = .ok events →
        ∀ T : Finset ℕ,
          (T.sum fun i => ((events.filter (·.source = .consolidations)).map
            (PinDrift.Internal.keyCredit i)).sum) ≤
            (((((queueX x electra).drop n).take r).filter fun c => c.targetIndex.toNat ∈ T).map
              (capBound x high)).sum := by
  have beforeFork : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  have mFork : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨crossings, crossingOk, -⟩ := upgradeBalanceReplay_bounded upgrades
  have advanceCopy := slotOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, afterEq⟩ := advanceCopy
  have sum : next.toNat = m.state.slot.toNat + 1 :=
    (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have shapeCached : Shape (queueX x electra) (getCurrentEpoch x.state) n cached := by
    rw [cachedEq]; exact shape
  by_cases boundary : next % preset.SLOTS_PER_EPOCH = 0
  · simp only [epochIfLast, boundary, ↓reduceIte] at epochOk
    obtain ⟨middle, updated, recorded, recordOk, updatedOk, -, balances, cutOk⟩ :=
      epochBalanceReplay_result_before cached epoched beforeFork epochOk
    obtain ⟨reset, deposited, ⟨stages, rewardEvents, limit, rewardReplay, _⟩, depositedOk,
      consolidatedOk, recordedEq⟩ := funding_epoch_site cutOk recordOk
    have trace7 := stages.depositTrace depositedOk
    simp only [EpochStage.Edge, mFork, ↓reduceDIte] at consolidatedOk
    simp only [mFork, ↓reduceDIte] at recordedEq
    -- The facts about the run before the step.
    have xEarly : x.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) beforeFork
    have lifeXM : RegistryLifecycle x.state m.state := pre.registryLifecycle
    have capXM := (Internal.CapStep.run pre caps).1
    have orderedM : OrderedAt config m.state :=
      (shared.append pre).pendingConsolidationsOrdered genesis delay
    have orderedX := shared.pendingConsolidationsOrdered genesis delay
    have cappedX := shared.effectiveBalance_capped genesis caps
    -- The cached state is the state of the step, up to its roots.
    have lifeMC : RegistryLifecycle m.state cached := .of_data (by rw [cachedEq])
    have slotMC : cached.slot = m.state.slot := by rw [cachedEq]
    have queueMC : fundingSources cached = fundingSources m.state := by rw [cachedEq]; rfl
    have orderedC : OrderedAt config cached := by rw [cachedEq]; exact orderedM
    have capMC : Internal.CapStep config m.state cached := by
      rw [cachedEq]; exact Internal.CapStep.data
    -- The stages up to the pass.
    obtain ⟨lifeCD, slotCD, queueCD, orderedCD⟩ := prefix_rel mFork (by
      intro k member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fun h => by cases h)
      trace7
    have capCD := Internal.CapStep.epochTrace trace7
    have epochD : getCurrentEpoch deposited = getCurrentEpoch m.state := by
      simp only [getCurrentEpoch, slotCD, slotMC]
    -- The epoch of the next state.
    have epochLast : (getCurrentEpoch last.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
      have advancedEpoch : getCurrentEpoch last.state = getCurrentEpoch
          ({ epoched with slot := next } : BeaconState preset m.fork) := by
        rw [afterEq]
        exact congrArg (computeEpochAtSlot preset) (processUpgrades_slot upgrades)
      rw [advancedEpoch]
      have nextEpoch :=
        getCurrentEpoch_toNat ({ epoched with slot := next } : BeaconState preset m.fork)
      simp only at nextEpoch
      rw [nextEpoch, getCurrentEpoch_toNat m.state]
      exact nextSlot_epoch_of_boundary sum boundary
    have nextBound : (getCurrentEpoch deposited).toNat + 1 ≤ high + 1 := by
      rw [epochD]; omega
    have nextNat :
        (getCurrentEpoch deposited + 1).toNat = (getCurrentEpoch deposited).toNat + 1 := by
      have fits := (getCurrentEpoch last.state).toNat_lt
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
      rw [epochD]; omega
    have facts : PassFacts (config := config) x high deposited :=
      { electraX := electra, electraP := mFork, caps := caps, delay := delay, within := within,
        life := lifeXM.trans (lifeMC.trans lifeCD), cap := capXM.trans (capMC.trans capCD),
        orderedX := orderedX, invariantP := (orderedCD orderedC).1, cappedX := cappedX,
        next := nextBound, nextNat := nextNat }
    have shapeD : Shape (queueX x electra) (getCurrentEpoch x.state) n deposited :=
      shapeCached.carry queueCD lifeCD
    obtain ⟨r, shapeMiddle, lifePM, credits⟩ := pass_step_targets facts shapeD consolidatedOk
    refine ⟨r, ?_, fun {events} replayed T => ?_⟩
    · have trace := processEpoch_trace epochOk
      change EpochTrace _ (EpochStage.prefixStages ++ [.payments, .effectiveBalances,
        .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
        .proposerLookahead, .ptcWindow]) _ _ at trace
      obtain ⟨middle', head, tailTrace⟩ := EpochTrace.append_iff.mp trace
      have midEq : middle' = middle := by
        have h1 : epochBeforePayments config checks cached = .ok middle' :=
          (epochBeforePayments_eq_run config checks cached).trans
            (EpochTrace.run_ok_iff.mpr head)
        rw [h1] at cutOk
        exact Except.ok.inj cutOk
      subst midEq
      obtain ⟨lifeTail, -, queueTail, -⟩ := prefix_rel mFork (by
        intro k member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact fun h => by cases h) tailTrace
      have shapeEpoched := shapeMiddle.carry queueTail lifeTail
      have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + r)
          advanced := by
        rw [← afterEq]
        exact shapeEpoched.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = recorded ++ crossings :=
        Except.ok.inj (replayed.symm.trans (Step.balanceEvents_epoch_slot ok cachedOk nextOk
          boundary recordOk slotOk crossingOk))
      have rewardsNo := rewards_noConsolidations (pre := (stages.scored, [])) (by simp) rewardReplay
      have f1 : rewardEvents.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by simpa using rewardsNo e member
      have f2 : crossings.filter (fun e => decide (e.source = .consolidations)) = [] :=
        List.filter_eq_nil_iff.mpr fun e member => by
          simp [upgradeBalanceReplay_crossing crossingOk e member]
      rw [eventsEq, recordedEq]
      simp only [List.append_assoc, List.filter_append, f1, f2]
      simpa [List.filter_cons, creditedAt, PinDrift.Internal.keyCredit, actualBalanceAt] using
        credits T
  · simp only [epochIfLast, boundary, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    refine ⟨0, ?_, fun {events} replayed T => ?_⟩
    · have shapeAdvanced : Shape (queueX x electra) (getCurrentEpoch x.state) (n + 0)
          advanced := by
        rw [← afterEq]
        exact shapeCached.carry rfl (.of_data rfl)
      exact upgrades_shape (advanced := ⟨m.fork, advanced⟩) mFork early shapeAdvanced upgrades
    · have eventsEq : events = crossings := by
        simpa [Step.balanceEvents, cachedOk, nextOk, boundary, slotOk, crossingOk, pure,
          Except.pure,
          bind, Except.bind] using replayed.symm
      subst eventsEq
      have none : (events.filter (·.source = .consolidations)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e member
        simp [upgradeBalanceReplay_crossing crossingOk e member]
      simp [none]

/-- A block keeps the shape of the queue: it only appends entries that are new since X. -/
private theorem block_step {f : Fork} {e0 : Epoch} {L : List PendingConsolidation} {n : ℕ}
    (electra : .pectra ≤ f)
    (delay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {engine : ExecutionEngine preset f} {signed : SignedBeaconBlock preset f}
    {s t : BeaconState preset f}
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    (started : e0 ≤ getCurrentEpoch s) (shape : Shape L e0 n s) : Shape L e0 n t := by
  have grown := ConsolidationQueueRise.appendStep_processBlock (Nat.le_trans (by decide) electra)
    delay (applySignedBlock_ok ok).2.1
  exact shape.grow electra grown.2.2 grown.2.1 started

/-- The consolidation credits of a run from X to the targets in `T` are within the caps.

The caps are those of the entries it reads whose target is in `T`. -/
private theorem run_credits_targets {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (electra : .pectra ≤ x.fork) (high : ℕ)
    (within : high + 2 ≤ (getCurrentEpoch x.state).toNat +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ n, Shape (queueX x electra) (getCurrentEpoch x.state) n y.state ∧
      ∀ T : Finset ℕ,
        (T.sum fun i => ((events.filter (·.source = .consolidations)).map
          (PinDrift.Internal.keyCredit i)).sum) ≤
          ((((queueX x electra).take n).filter fun c => c.targetIndex.toNat ∈ T).map
            (capBound x high)).sum := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    refine ⟨0, ⟨[], ?_, fun c member => by simp at member⟩, fun T => by simp⟩
    rw [fundingSources_eq electra]
    simp [queueX]
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    obtain ⟨n, shape, bound⟩ := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
      (by omega) priorOk
    have inFork : .pectra ≤ middle.fork :=
      Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    have started : getCurrentEpoch x.state ≤ getCurrentEpoch middle.state :=
      currentEpoch_le_of_chainSteps pre.chainSteps
    have beforeFork : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have growth : ∀ {r : ℕ} {T : Finset ℕ},
        ((((queueX x electra).take n).filter fun c => c.targetIndex.toNat ∈ T).map
          (capBound x high)).sum +
        (((((queueX x electra).drop n).take r).filter fun c => c.targetIndex.toNat ∈ T).map
          (capBound x high)).sum =
        ((((queueX x electra).take (n + r)).filter fun c => c.targetIndex.toNat ∈ T).map
          (capBound x high)).sum := by
      intro r T
      rw [List.take_add, List.filter_append, List.map_append, List.sum_append]
    have stepResult : ∃ r, Shape (queueX x electra) (getCurrentEpoch x.state) (n + r) last.state ∧
        ∀ {added : List (BalanceEvent preset)}, step.balanceEvents = .ok added → ∀ T : Finset ℕ,
          (T.sum fun i => ((added.filter (·.source = .consolidations)).map
            (PinDrift.Internal.keyCredit i)).sum) ≤
            (((((queueX x electra).drop n).take r).filter fun c => c.targetIndex.toNat ∈ T).map
              (capBound x high)).sum := by
      cases step with
      | block engine signed due ok =>
        refine ⟨0, block_step inFork (by omega) ok started shape, fun {added} addedOk T => ?_⟩
        have none : (added.filter (·.source = .consolidations)) = [] :=
          List.filter_eq_nil_iff.mpr fun e member => by
            simpa using PinDrift.Internal.blockReplay_noConsolidations inFork early engine _ _
              (Step.balanceEvents_block early addedOk) e member
        simp [none]
      | slot ok =>
        obtain ⟨r, shapeLast, credits⟩ := slot_step_targets shared pre genesis caps delay electra
          high within ok early endEpoch shape
        exact ⟨r, shapeLast, fun {added} addedOk => credits addedOk⟩
    obtain ⟨r, shapeLast, credits⟩ := stepResult
    refine ⟨n + r, shapeLast, fun T => ?_⟩
    have bound := bound T
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      have := credits addedOk T
      have growth' := growth (r := r) (T := T)
      simp only [List.filter_append, List.map_append, List.sum_append, Finset.sum_add_distrib]
      omega
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      have growth' := growth (r := r) (T := T)
      omega

/-- The caps of the entries of a queue, as the caps of their sources that X lets move. -/
private theorem capBound_sum (x : ForkedBeaconState preset) (high : ℕ)
    (queue : List PendingConsolidation) :
    (queue.map (capBound x high)).sum =
      ((((queue.filterMap fun c => x.state.validators.data[c.sourceIndex.toNat]?).filter
        fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map
          fun v => (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum) := by
  induction queue with
  | nil => simp
  | cons c rest ih =>
    cases lookup : x.state.validators.data[c.sourceIndex.toNat]? with
    | none => simpa [capBound, lookup] using ih
    | some v =>
      by_cases due : v.slashed = false ∧ v.withdrawableEpoch.toNat ≤ high + 1
      · simp [capBound, lookup, due, ih]
      · have : ¬ (!v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)) = true := by
          simpa [Bool.not_eq_true'] using due
        simp [capBound, lookup, due, this, ih]

/-! ## Credits to exiting keys, by pass -/

/-- No deposit credits a key that is exited and not withdrawable at each deposit event of a run.

`exitedAt` is that fact at the state before each deposit event of a slot step.

A block deposit needs none: from Electra it raises no balance. -/
theorem Run.exiting_deposit_credit_zero_of_exited {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) (i : ℕ)
    (exitedAt : ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w),
      tail.Contains (Step.slot ok) → ∀ {es : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
        ∀ e ∈ es, e.source = .deposits → ∃ v : Validator,
          e.before.state.validators.data[i]? = some v ∧ v.exitEpoch.toNat < 2 ^ 64 - 1 ∧
          (getCurrentEpoch e.before.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 := by
  have located := (PinDrift.Internal.run_located tail electra early high replayed).1
  apply List.sum_eq_zero
  intro n member
  obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
  simp only [decide_eq_true_eq] at sourceEq
  rcases located e inEvents sourceEq with unconditional | ⟨u, w, ok, es, contains, replayedEs,
      inStep, keeps⟩
  · have := unconditional i
    simp only [PinDrift.Internal.keyCredit]
    omega
  · obtain ⟨v, read, exited, held⟩ := exitedAt ok contains replayedEs e inStep sourceEq
    have same := keeps i v read exited held
    simp [PinDrift.Internal.keyCredit, actualBalanceAt, same]

/-- The deposit bound along a run.

Along C's run, no deposit credits a key that exits at the run's start. -/
private theorem Run.exiting_deposit_credit_zero_of_kept {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    -- This is the withdrawable-kept fact at the state before each deposit event of a slot step.
    --
    -- It also says that the epoch of each event's state is at most the run's last epoch.
    --
    -- A block deposit needs no such fact.
    --
    -- From Electra it raises no balance.
    (kept : ∀ {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w),
      tail.Contains (Step.slot ok) → ∀ {es : List (BalanceEvent preset)},
        (Step.slot ok : Step config checks u w).balanceEvents = .ok es →
        ∀ e ∈ es, e.source = .deposits →
          RegistryLifecycle x.state e.before.state ∧ WithdrawableKept x.state e.before.state ∧
          getCurrentEpoch e.before.state ≤ getCurrentEpoch y.state)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    -- An assigned exit epoch stays fixed.
    --
    -- Once the exit is set, the withdrawable epoch can only rise.
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    -- The key stays not withdrawable through the run's end.
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 :=
  PinDrift.Internal.Run.exiting_deposit_credit_zero_of_exited tail electra early high replayed i
    (by
      intro u w ok contains es replayedEs e inStep sourceEq
      obtain ⟨life, withdrawal, epoch⟩ := kept ok contains replayedEs e inStep sourceEq
      obtain ⟨w, read, lifecycle⟩ := life.validators i v found
      have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
        rw [far] at exited
        exact absurd exited (Nat.lt_irrefl _)
      have sameExit := lifecycle.exitEpoch assigned
      have later := UInt64.le_iff_toNat_le.mp (withdrawal i v w found read assigned).1
      have now := UInt64.le_iff_toNat_le.mp epoch
      exact ⟨w, read, by rw [sameExit]; exact exited, by omega⟩)

/-- Along C's run from Fulu, no deposit credits a key that exits at the run's start.

The key stays not withdrawable through the run's end.

The withdrawable epoch cannot drop before any deposit event of a slot step. -/
theorem Run.exiting_deposit_credit_zero {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (fulu : .fusaka ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (i : ℕ) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < v.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 :=
  Run.exiting_deposit_credit_zero_of_kept tail (Nat.le_trans (by decide) fulu) early high replayed
    (fun {_ _} ok contained {_} replayedEs e member source =>
      let kept := PinDrift.Internal.Run.events_kept shared genesis tail fulu early ok contained
        replayedEs
        e member source
      ⟨kept.1, kept.2.1, kept.2.2.1⟩)
    i v found exited held

/-- A step that starts a key's exit credits no deposit to it.

A slot step's pending deposits come after its registry updates, which postpone the key.

The exit and withdrawable epochs at the step's end are those at the input of its deposits. -/
private theorem Step.charge_deposit_credit_zero {a b : ForkedBeaconState preset}
    (step : Step config checks a b) (fulu : .fusaka ≤ a.fork) (early : b.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : ℕ) (inside : i < a.state.validators.data.size) (w : Validator)
    (found : b.state.validators.data[i]? = some w) (exited : w.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch b.state).toNat < w.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 := by
  refine PinDrift.Internal.Run.exiting_deposit_credit_zero_of_exited (Run.nil.snoc step)
    (Nat.le_trans (by decide) fulu) early (getCurrentEpoch b.state).toNat
    (DirectSafety.Apriori.Internal.single_balanceEvents step replayed) i ?_
  intro u w' ok contains es replayedEs e member source
  cases contains with
  | last =>
    obtain ⟨kept, -, same, stay, -⟩ :=
      PinDrift.Internal.Step.deposit_input ok fulu early replayedEs e member source
    obtain ⟨v, readV⟩ : ∃ v, e.before.state.validators.data[i]? = some v :=
      ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside kept.life.size_le)⟩
    obtain ⟨w'', read, exit, wd⟩ := stay i v readV
    rw [found, Option.some.injEq] at read
    subst read
    have epochLe := UInt64.le_iff_toNat_le.mp
      (Step.slot ok : Step config checks a b).chainStep.currentEpoch_le
    refine ⟨v, readV, by rw [← exit]; exact exited, ?_⟩
    rw [same, ← wd]
    omega
  | earlier member _ => cases member

/-- Along a run from the step that starts a key's exit, no deposit credits the key.

The key is exited and not withdrawable at the run's end.

The step is counted by the replay. -/
theorem Run.charge_deposit_credit_zero {g a b y : ForkedBeaconState preset}
    (shared : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (step : Step config checks a b) (post : Run config checks b y) (fulu : .fusaka ≤ a.fork)
    (early : y.fork < .glamsterdam) (high : ℕ)
    (counted : (getCurrentEpoch a.state).toNat ≤ high + 1) {events : List (BalanceEvent preset)}
    (replayed : ((Run.nil.snoc step).append post).balanceEvents high = .ok events)
    (i : ℕ) (inside : i < a.state.validators.data.size) (w : Validator)
    (found : b.state.validators.data[i]? = some w) (exited : w.exitEpoch.toNat < 2 ^ 64 - 1)
    (held : (getCurrentEpoch y.state).toNat < w.withdrawableEpoch.toNat) :
    ((events.filter (·.source = .deposits)).map (PinDrift.Internal.keyCredit i)).sum = 0 := by
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  obtain ⟨es, replayedS⟩ := step.balanceEvents_ok bEarly
  obtain ⟨later, replayedP⟩ := post.balanceEvents_ok early high
  have one : (Run.nil.snoc step : Run config checks a b).balanceEvents high = .ok es := by
    simp [Run.balanceEvents, counted, replayedS, pure, Except.pure]
    rfl
  rw [DirectSafety.Apriori.Internal.balanceEvents_append _ _ high one replayedP] at replayed
  obtain rfl := Except.ok.inj replayed
  have heldB : (getCurrentEpoch b.state).toNat < w.withdrawableEpoch.toNat :=
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps))
      held
  have first := Step.charge_deposit_credit_zero step fulu bEarly replayedS i inside w found exited
    heldB
  have second := PinDrift.Internal.Run.exiting_deposit_credit_zero (shared.append (Run.nil.snoc
    step)) genesis post
    (Nat.le_trans fulu step.chainStep.fork_le) early high replayedP i w found exited held
  simp only [List.filter_append, List.map_append, List.sum_append]
  omega

/-- The consolidation credits to the keys in `T` along the run.

They are at most the caps at X of the due entries of X's queue whose target is in `T`.

Each entry credits only its target, so the sum over the entries splits by target. -/
theorem Run.consolidation_credits_le_X_targets {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (withinDelay : high + 2 ≤
      (getCurrentEpoch x.state).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (T : Finset ℕ) :
    (T.sum fun i => ((events.filter (·.source = .consolidations)).map (PinDrift.Internal.keyCredit
      i)).sum) ≤
      ((((((x.state.pendingConsolidations electra).data.toList.filter fun c =>
          c.targetIndex.toNat ∈ T).filterMap fun c =>
        x.state.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map fun v =>
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat).sum) := by
  obtain ⟨n, -, bound⟩ := run_credits_targets shared genesis caps delay electra high withinDelay
    tail early endEpoch replayed
  rw [← capBound_sum]
  refine Nat.le_trans (bound T) ?_
  have split := List.take_append_drop n (x.state.pendingConsolidations electra).data.toList
  conv_rhs => rw [← split, List.filter_append, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-! ## A validator created in a step has no exit assigned -/

/-- Every validator from position `n` on has no exit epoch assigned. -/
private def ExitFarFrom (n : ℕ) {f : Fork} (s : BeaconState preset f) : Prop :=
  ∀ i v, n ≤ i → s.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH

/-- A state with the same registry has no exit assigned from position `n` either. -/
private theorem ExitFarFrom.of_data {n : ℕ} {f g : Fork} {s : BeaconState preset f}
    {t : BeaconState preset g} (same : t.validators.data = s.validators.data)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  intro i v large found
  rw [same] at found
  exact holds i v large found

/-- A registry that does not reach position `n` has no validator from there on. -/
private theorem ExitFarFrom.of_size {n : ℕ} {f : Fork} {s : BeaconState preset f}
    (small : s.validators.data.size ≤ n) : ExitFarFrom n s := by
  intro i v large found
  have := (Array.getElem?_eq_some_iff.mp found).1
  omega

/-- A write that keeps the exit epoch of its validator keeps the later validators unassigned. -/
private theorem ExitFarFrom.of_set {n position : ℕ} {f : Fork} {s t : BeaconState preset f}
    {old v : Validator} (found : getValidatorAt s position = .ok old)
    (set : s.setValidatorAt position v = .ok t) (same : v.exitEpoch = old.exitEpoch)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro i w large got
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at got
  split at got
  · rename_i place
    subst place
    cases got
    rw [same]
    exact holds position old large (getValidatorAt_eq_ok_iff.mp found)
  · exact holds i w large got

/-- A pending deposit appends a validator with no exit epoch. -/
private theorem ExitFarFrom.of_apply {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks s deposit = .ok t) (holds : ExitFarFrom n s) :
    ExitFarFrom n t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨index, raised⟩ | ⟨_, added⟩
  · exact holds
  · exact holds.of_data (congrArg (·.data) (increaseBalance_validators raised))
  · intro i v large found
    rw [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push] at found
    split at found
    · cases found
      rfl
    · exact holds i v large found

/-- Applying the pending deposits assigns no exit from position `n` on. -/
private theorem ExitFarFrom.of_deposits {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} (ok : Consensus.processPendingDeposits config checks s electra = .ok t)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  obtain ⟨_, _, _, _, next, _, _, _, _, _, _, _, _, folded, rfl⟩ :=
    processPendingDeposits_applied ok
  have kept : ExitFarFrom n next :=
    foldlM_ok_invariant (g := Consensus.applyPendingDeposit config checks)
      (fun u : BeaconState preset f => ExitFarFrom n u)
      (fun _ _ _ before step => ExitFarFrom.of_apply step before) holds folded
  exact kept

/-- The effective-balance updates write only effective balances. -/
private theorem ExitFarFrom.of_updates {n : ℕ} {f : Fork}
    {s t : BeaconState preset f} (ok : Consensus.processEffectiveBalanceUpdates s = .ok t)
    (holds : ExitFarFrom n s) : ExitFarFrom n t := by
  unfold Consensus.processEffectiveBalanceUpdates at ok
  refine foldlM_ok_invariant (fun u : BeaconState preset f => ExitFarFrom n u)
    (fun _ _ _ before step => ?_) holds ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨validator, found, _, _, _, _, set⟩ := step
  exact before.of_set found set rfl

/-- An epoch appends validators only in its pending deposits, after the registry updates.

So a validator that the epoch creates has no exit epoch. -/
private theorem ExitFarFrom.of_epoch {n : ℕ} {f : Fork} {s t : BeaconState preset f}
    (electra : .pectra ≤ f) (ok : Consensus.processEpoch config checks s = .ok t)
    (small : s.validators.data.size ≤ n) : ExitFarFrom n t := by
  obtain ⟨justified, scored, rewarded, registered, slashed, reset, deposited, consolidated,
    settled, updated, justifiedOk, scoredOk, rewardedOk, registeredOk, slashedOk, resetOk,
    depositedOk, consolidatedOk, settledOk, updatedOk, rest⟩ :=
    EpochTrace.through_effectiveBalances (processEpoch_trace ok)
  have keeps {k : EpochStage} {a b : BeaconState preset f}
      (other : k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
        k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances)
      (computed : EpochStage.action config checks k a = .ok b) : b.validators = a.validators :=
    (EpochStage.action_cases.mp computed).records other |>.1
  -- The first six stages keep the size of the registry.
  have size : reset.validators.data.size = s.validators.data.size := by
    have one : justified.validators.data.size = s.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .justification) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        justifiedOk)
    have two : scored.validators.data.size = justified.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .inactivity) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        scoredOk)
    have three := (processRewardsAndPenalties_sameSizes
      (EpochStage.action_cases.mp rewardedOk)).1
    have four := (sameSizes_processRegistryUpdates (EpochStage.action_cases.mp registeredOk)).1
    have five := (sameSizes_processSlashings (EpochStage.action_cases.mp slashedOk)).1
    have six : reset.validators.data.size = slashed.validators.data.size :=
      congrArg (·.data.size) (keeps (k := .eth1Reset) ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩
        resetOk)
    omega
  have atReset : ExitFarFrom n reset := .of_size (by omega)
  -- Pending deposits append validators with no exit.
  have atDeposited : ExitFarFrom n deposited := by
    have edge := EpochStage.action_cases.mp depositedOk
    simp only [EpochStage.Edge, electra, ↓reduceDIte] at edge
    exact atReset.of_deposits edge
  have atConsolidated : ExitFarFrom n consolidated :=
    atDeposited.of_data (congrArg (·.data)
      ((EpochStage.action_cases.mp consolidatedOk).validators_eq ⟨nofun, nofun, nofun⟩))
  have atSettled : ExitFarFrom n settled :=
    atConsolidated.of_data (congrArg (·.data) ((EpochStage.action_cases.mp settledOk).validators_eq
      ⟨nofun, nofun, nofun⟩))
  have atUpdated : ExitFarFrom n updated :=
    atSettled.of_updates (EpochStage.action_cases.mp updatedOk)
  -- The seven later stages keep the validators.
  have same : t.validators = updated.validators :=
    EpochTrace.transport (fun a b : BeaconState preset f => b.validators = a.validators)
      (fun _ => rfl) (fun one two => two.trans one)
      (fun k member a b computed => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        exact keeps (by rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩) computed) rest
  exact atUpdated.of_data (congrArg (·.data) same)

/-- From Electra, a step before Gloas leaves every validator that it creates with no exit epoch. -/
private theorem ExitFarFrom.of_chainStep {a b : ForkedBeaconState preset}
    (step : ChainStep config checks a b) (electra : .pectra ≤ a.fork)
    (early : a.fork < .glamsterdam) : ExitFarFrom a.state.validators.data.size b.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slotOk
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have atEpoched : ExitFarFrom a.state.validators.data.size epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · exact ExitFarFrom.of_epoch electra epochedOk (by rw [cachedEq])
      · cases epochedOk
        exact .of_size (by rw [cachedEq])
    have atAdvanced : ExitFarFrom a.state.validators.data.size { epoched with slot := next } :=
      atEpoched.of_data rfl
    exact (processUpgrades_induction (config := config) (checks := checks)
      (forked := ⟨a.fork, { epoched with slot := next }⟩) (after := b)
      (property := fun post => ExitFarFrom a.state.validators.data.size post.state ∧
        .pectra ≤ post.fork)
      (fun {pre post} kept ok =>
        ⟨kept.1.of_data (upgradeNext_validators_of_electra kept.2 ok),
          Nat.le_trans kept.2 (Nat.le_of_lt post.property)⟩)
      ⟨atAdvanced, electra⟩ upgrades).1
  | block engine signed validate ok =>
    obtain ⟨input, last, started, operated, -, synced⟩ :=
      processBlock_operationsInput (applySignedBlock_ok ok).2.1
    have same := OperationsInput.validators_eq early started
    have fresh := processOperations_new_validator_epochs_unassigned operated
    intro i v large found
    have lastFound : last.validators.data[i]? = some v := by
      split at synced
      · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
        exact found
      · cases synced
        exact found
    exact (fresh i v (by rw [same]; exact large) lastFound).2

/-- Along a run from Electra, a validator can gain an exit epoch only through a departure charge.

The charge is at that exit epoch. -/
theorem Run.charge_of_exit {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (i : ℕ) (unset : ∀ v, x.state.validators.data[i]? = some v → v.exitEpoch = FAR_FUTURE_EPOCH)
    (v : Validator) (found : y.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ c ∈ tail.departureCharges, c.index = i ∧ c.epoch = v.exitEpoch.toNat := by
  cases initial : x.state.validators.data[i]? with
  | some w => exact tail.departure_charge_of_assigned i w v initial found (unset w initial) assigned
  | none =>
    obtain ⟨m, n, pre, step, post, rfl, absent, arrived⟩ := Run.split_at_flip tail
      (fun z => i < z.state.validators.data.size)
      (Nat.not_lt.mpr (Array.getElem?_eq_none_iff.mp initial))
      (Array.getElem?_eq_some_iff.mp found).1
    have electraM : .pectra ≤ m.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    have earlyM : m.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early)
    have read := Array.getElem?_eq_getElem arrived
    have pending := ExitFarFrom.of_chainStep step.chainStep electraM earlyM i _
      (Nat.le_of_not_lt absent) read
    obtain ⟨c, member, index, epoch⟩ :=
      post.departure_charge_of_assigned i _ v read found pending assigned
    exact ⟨c, by rw [Run.departureCharges_append]; exact List.mem_append_right _ member, index,
      epoch⟩

/-! ## The floor path of a new key's effective balance -/

/-! ## A potential that retains a decreasing floor -/

/-- One epoch keeps the fraction of the potential that the floor keeps, up to a rounding error. -/
private theorem chain_step (φ0 φj φj1 d0 dj dj1 e j : ℕ) (pos : 0 < φj) (anti : φj1 ≤ φj)
    -- The floor `φj` never rises, and stays within three halves of its start `φ0`.
    (band : 2 * φ0 ≤ 3 * φj) (ih : 2 * d0 * φj ≤ 2 * dj * φ0 + 3 * e * j)
    -- The potential `dj` keeps the fraction `φj1 / φj` of itself, less the error `e`.
    (step : dj * φj1 ≤ dj1 * φj + e) :
    -- Then `d0` keeps the fraction `φj1 / φ0` of itself after `j + 1` epochs.
    --
    -- It loses `3 e (j + 1) / 2` over `φ0`.
    2 * d0 * φj1 ≤ 2 * dj1 * φ0 + 3 * e * (j + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc 2 * d0 * φj1 * φj = (2 * d0 * φj) * φj1 := by ring
    _ ≤ (2 * dj * φ0 + 3 * e * j) * φj1 := Nat.mul_le_mul_right _ ih
    _ = 2 * φ0 * (dj * φj1) + 3 * e * j * φj1 := by ring
    _ ≤ 2 * φ0 * (dj1 * φj + e) + 3 * e * j * φj := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ step
        · exact Nat.mul_le_mul_left _ anti
    _ = 2 * dj1 * φ0 * φj + 2 * φ0 * e + 3 * e * j * φj := by ring
    _ ≤ 2 * dj1 * φ0 * φj + 3 * φj * e + 3 * e * j * φj := by
        have := Nat.mul_le_mul_right e band
        omega
    _ = (2 * dj1 * φ0 + 3 * e * (j + 1)) * φj := by ring

/-! ## One epoch of a key against the floor path -/

/-- The effective balance `EB` is within the band above the least of the balance and the cap.

The least of the balance and `K` is at most the least of the balance and the cap. -/
private theorem eb_le_min_band (b' cap K band EB : ℕ) (hcap : K ≤ cap)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap) :
    EB ≤ min b' cap + band ∧ min b' K ≤ min b' cap := by
  refine ⟨?_, min_le_min_left _ hcap⟩
  rcases le_total b' cap with h | h
  · rw [min_eq_left h]
    exact hyst
  · rw [min_eq_right h]
    omega

/-- An epoch that starts at or above `K` keeps the potential, since the floor only falls. -/
private theorem big_arith (c K band X φt φt1 : ℕ) (hc : c ≤ K) (hφ : φt1 ≤ φt) :
    (c + band) * φt1 ≤ (K + band) * φt + (K + band) + X * φt := by
  have := Nat.mul_le_mul (Nat.add_le_add_right hc band) hφ
  nlinarith

/-- One epoch of a key keeps the fraction of its potential that the floor keeps. -/
private theorem step_arith (b' b cap K band pass X φt φt1 pen EB : ℕ)
    (hcap : K ≤ cap)
    -- The epoch loses at most its pass.
    (seg : min b' cap ≤ b + pass + X)
    -- The pass is charged at the effective balance `EB`.
    --
    -- That balance lies within the band above the balance, and below the cap.
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap)
    -- The pass rate is at most `EB * (pen + 1) / φt`.
    (pr : pass * φt ≤ EB * (pen + 1))
    -- Here `φt = φt1 + pen` is the floor before the epoch, and `φt1` the floor after it.
    (ph : φt = φt1 + pen) (hφ : 1 ≤ φt1) :
    -- The potential is the least of the balance and `K`, plus the downward band.
    --
    -- The error is `K + band`, from the rounding.
    (min b' K + band) * φt1 ≤ (min b K + band) * φt + (K + band) + X * φt := by
  obtain ⟨hEB, hcle⟩ := eb_le_min_band b' cap K band EB hcap hyst hcapEB
  set C := min b' cap with hC
  -- the key's balance after the epoch, scaled
  have bound : C * φt ≤ b * φt + (C + band) * (pen + 1) + X * φt := by
    have h1 : C * φt ≤ (b + pass + X) * φt := Nat.mul_le_mul_right _ seg
    have h2 : pass * φt ≤ (C + band) * (pen + 1) :=
      pr.trans (Nat.mul_le_mul_right _ hEB)
    nlinarith
  by_cases big : K ≤ b
  · rw [min_eq_right big]
    exact big_arith _ _ _ _ _ _ (min_le_right _ _) (by omega)
  · have small : b < K := Nat.lt_of_not_ge big
    have : min b K = b := min_eq_left small.le
    rw [this]
    -- c ≤ C, and the bound on C·φt1
    set c := min b' K with hc
    have hcK : c ≤ K := min_le_right _ _
    have key : C * φt ≤ b * φt + (C + band) * (pen + 1) + X * φt := bound
    -- (C + band) * (pen + 1) = (C + band) * pen + (C + band)
    have e1 : (C + band) * (pen + 1) = (C + band) * pen + (C + band) := by ring
    -- C * φt - (C+band) pen = C * φt1 - band * pen
    have e2 : C * φt = C * φt1 + C * pen := by rw [ph]; ring
    have lower : (C + band) * φt1 ≤ (b + band) * φt + (C + band) + X * φt := by
      rw [ph] at key ⊢
      nlinarith
    -- replace C by c: C could exceed K, then use the shape of the loss
    by_cases cK : C ≤ K
    · have hcC : c = C := le_antisymm hcle (le_min (min_le_left _ _) cK)
      rw [hcC]
      have : (C + band) ≤ (K + band) := by omega
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      have h3 : C * φt1 ≤ b * φt + C + band * (pen + 1) + X * φt := by
        rw [ph] at key
        nlinarith
      have h4 : K * φt1 + C ≤ C * φt1 + K := by
        have : K * (φt1 - 1) ≤ C * (φt1 - 1) := Nat.mul_le_mul_right _ above.le
        have e1 : K * (φt1 - 1) + K = K * φt1 := by
          have := Nat.mul_le_mul_left K hφ
          rw [Nat.mul_sub]; omega
        have e2 : C * (φt1 - 1) + C = C * φt1 := by
          have := Nat.mul_le_mul_left C hφ
          rw [Nat.mul_sub]; omega
        omega
      have h5 : (c + band) * φt1 ≤ (K + band) * φt1 := Nat.mul_le_mul_right _ (by omega)
      rw [ph]
      nlinarith

/-- One epoch of a key, with the initial penalty of a slashing in it.

The penalty is at most `EB / Q`, and the epoch is charged `Bq` for it, with `K + band ≤ Q * Bq`.

The floor after the epoch stays at least `6 Q` and within three halves of the floor before. -/
private theorem step_arith_slash (b' b cap K band pass X sl Q Bq φt φt1 pen EB : ℕ)
    (hcap : K ≤ cap) (hQ : 2 ≤ Q) (hB : K + band ≤ Q * Bq)
    (seg : min b' cap ≤ b + pass + X + sl) (hsl : Q * sl ≤ EB)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap)
    (pr : pass * φt ≤ EB * (pen + 1))
    (ph : φt = φt1 + pen) (hφ : 6 * Q ≤ φt1) (hband : 2 * φt ≤ 3 * φt1) :
    (min b' K + band) * φt1 ≤
      (min b K + band) * φt + (K + band) + (X + (if sl = 0 then 0 else Bq)) * φt := by
  by_cases noSlash : sl = 0
  · subst noSlash
    simp only [ite_true, Nat.add_zero, Nat.add_zero] at seg ⊢
    have := step_arith b' b cap K band pass X φt φt1 pen EB hcap (by simpa using seg) hyst
      hcapEB pr ph (by omega)
    simpa using this
  · simp only [noSlash, ite_false]
    obtain ⟨hEB, hcle⟩ := eb_le_min_band b' cap K band EB hcap hyst hcapEB
    set C := min b' cap with hC
    by_cases cK : C ≤ K
    · -- the penalty is at most `Bq`, and the case is that without slashing
      have slB : sl ≤ Bq := by
        have : Q * sl ≤ Q * Bq := by omega
        exact Nat.le_of_mul_le_mul_left this (by omega)
      have := step_arith b' b cap K band pass (X + sl) φt φt1 pen EB hcap
        (by omega) hyst hcapEB pr ph (by omega)
      have h2 : (X + sl) * φt ≤ (X + Bq) * φt := Nat.mul_le_mul_right _ (by omega)
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      by_cases big : K ≤ b
      · rw [min_eq_right big]
        exact big_arith _ _ _ _ _ _ (min_le_right _ _) (by omega)
      · have small : b < K := Nat.lt_of_not_ge big
        have : min b K = b := min_eq_left small.le
        rw [this]
        have hc : min b' K ≤ K := min_le_right _ _
        obtain ⟨h, hh⟩ : ∃ h, Q * φt1 = h + Q + φt := by
          refine ⟨Q * φt1 - Q - φt, ?_⟩
          have : 3 * (Q * φt1) ≥ 2 * Q * φt := by nlinarith
          have : Q * φt1 ≥ Q + φt := by nlinarith
          omega
        have h1 : Q * C * φt ≤ Q * b * φt + Q * (C + band) * (pen + 1) + Q * X * φt +
            (C + band) * φt := by
          have a1 : C * φt ≤ (b + pass + X + sl) * φt := Nat.mul_le_mul_right _ seg
          have a2 : pass * φt ≤ (C + band) * (pen + 1) := pr.trans (Nat.mul_le_mul_right _ hEB)
          have a3 : Q * sl ≤ C + band := hsl.trans hEB
          have a4 : Q * (sl * φt) ≤ (C + band) * φt := by
            rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ a3
          have a5 : Q * (pass * φt) ≤ Q * ((C + band) * (pen + 1)) := Nat.mul_le_mul_left _ a2
          have a6 : Q * (C * φt) ≤ Q * ((b + pass + X + sl) * φt) := Nat.mul_le_mul_left _ a1
          have a7 : Q * ((b + pass + X + sl) * φt) =
              Q * (b * φt) + Q * (pass * φt) + Q * (X * φt) + Q * (sl * φt) := by ring
          have a8 : Q * C * φt = Q * (C * φt) := by ring
          have a9 : Q * b * φt = Q * (b * φt) := by ring
          have a10 : Q * (C + band) * (pen + 1) = Q * ((C + band) * (pen + 1)) := by ring
          have a11 : Q * X * φt = Q * (X * φt) := by ring
          rw [a8, a9, a10, a11]
          omega
        have e1 : Q * C * φt = Q * C * φt1 + Q * C * pen := by rw [ph]; ring
        have e2 : Q * (C + band) * (pen + 1) =
            Q * C * pen + Q * C + Q * band * pen + Q * band := by ring
        have e3 : C * (Q * φt1) = C * h + C * Q + C * φt := by rw [hh]; ring
        have e4 : (C + band) * φt = C * φt + band * φt := by ring
        have hC : C * h ≤ Q * b * φt + Q * band * pen + Q * band + Q * X * φt + band * φt := by
          linarith [h1, e1, e2, e3, e4]
        have h2 : K * h ≤ C * h := Nat.mul_le_mul_right _ above.le
        have e5 : K * (Q * φt1) = K * h + K * Q + K * φt := by rw [hh]; ring
        have e6 : Q * band * φt = Q * band * φt1 + Q * band * pen := by rw [ph]; ring
        have h3 : Q * K * φt1 + Q * band * φt1 ≤
            Q * b * φt + Q * band * φt + Q * (K + band) + Q * X * φt + (K + band) * φt := by
          have e7 : (K + band) * φt = K * φt + band * φt := by ring
          have e8 : Q * (K + band) = Q * K + Q * band := by ring
          linarith [hC, h2, e5, e6, e7, e8]
        have h4 : (K + band) * φt ≤ Q * Bq * φt := Nat.mul_le_mul_right _ hB
        have h5 : (min b' K + band) * φt1 ≤ (K + band) * φt1 := Nat.mul_le_mul_right _ (by omega)
        have h6 : Q * ((K + band) * φt1) ≤
            Q * ((b + band) * φt + (K + band) + (X + Bq) * φt) := by
          have e9 : Q * ((K + band) * φt1) = Q * K * φt1 + Q * band * φt1 := by ring
          have e10 : Q * ((b + band) * φt + (K + band) + (X + Bq) * φt) =
              Q * b * φt + Q * band * φt + Q * (K + band) + Q * X * φt + Q * Bq * φt := by ring
          rw [e9, e10]
          omega
        have h7 := Nat.le_of_mul_le_mul_left h6 (by omega)
        omega

/-! ## The state before a new key is scheduled -/

/-- A key that is activated by the end of a run is scheduled two epochs before its activation. -/
theorem Run.start_state {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (window : preset.SeedLookaheadAtLeastThree) (i : ℕ)
    -- The key is not active by the epoch after the start of the run.
    (pending : ∀ v, x.state.validators.data[i]? = some v →
      (getCurrentEpoch x.state).toNat + 1 < v.activationEpoch.toNat)
    (activated : ∃ vy, y.state.validators.data[i]? = some vy ∧
      vy.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ vy.activationEpoch ≤ getCurrentEpoch y.state)
    -- The key may have exited, so long as its activation is before its exit.
    (ordered : ∀ vy, y.state.validators.data[i]? = some vy →
      vy.activationEpoch.toNat < vy.exitEpoch.toNat) :
    -- At the state `z` that the run reaches in that epoch, the key holds its activation epoch `A`.
    --
    -- Activity up to `A` is fixed at `z`, since the seed lookahead is at least three epochs.
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks x z) (post : Run config checks z y)
      (v0 vy : Validator), tail = pre.append post ∧ z.state.validators.data[i]? = some v0 ∧
      y.state.validators.data[i]? = some vy ∧ v0.activationEpoch = vy.activationEpoch ∧
      (getCurrentEpoch z.state).toNat + 2 = vy.activationEpoch.toNat ∧
      vy.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat := by
  obtain ⟨vy, foundY, -, activeY⟩ := activated
  have lowY := UInt64.le_iff_toNat_le.mp activeY
  have highY := ordered vy foundY
  have exitBound := vy.exitEpoch.toNat_lt
  have fixedWindow : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := window
  -- Activity at the epoch `A` of the key, as the end state reads it.
  have activeAtA : isActiveAt y.state vy.activationEpoch i = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨vy, foundY, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨UInt64.le_refl _, UInt64.lt_iff_toNat_lt.mpr highY⟩
  have kept (h : ForkedBeaconState preset) (run : Run config checks h y)
      (le : vy.activationEpoch.toNat ≤ (getCurrentEpoch h.state).toNat +
        preset.MAX_SEED_LOOKAHEAD.toNat) :
      isActiveAt h.state vy.activationEpoch i = true := by
    have bound : vy.activationEpoch ≤ activityFixedEpoch h.state := by
      rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
      omega
    rw [← activeKept_of_chainSteps run.chainSteps _ bound]
    exact activeAtA
  -- The key is not active by the epoch after the start of the run.
  have later : (getCurrentEpoch x.state).toNat + 1 < vy.activationEpoch.toNat := by
    by_contra early
    have atX := kept x tail (by omega)
    obtain ⟨vx, foundX, activeX⟩ := isActiveAt_eq_true_iff.mp atX
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeX
    have := pending vx foundX
    have := UInt64.le_iff_toNat_le.mp activeX.1
    omega
  have startEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  obtain ⟨z, pre, post, epoch, split⟩ :=
    Run.exists_epoch_split tail (vy.activationEpoch.toNat - 2) (by omega) (by omega)
  have atZ := kept z post (by omega)
  obtain ⟨v0, foundZ, activeZ⟩ := isActiveAt_eq_true_iff.mp atZ
  have assigned := Consensus.Internal.assigned_of_active activeZ
  obtain ⟨w, foundW, life⟩ := post.registryLifecycle.validators i v0 foundZ
  have same : w = vy := Option.some.inj (foundW.symm.trans foundY)
  subst same
  exact ⟨z, pre, post, v0, w, split, foundZ, foundY, (life.activationEpoch assigned).symm,
    by omega, lowY⟩

/-! ## The pass rate against the floor path -/

section FloorPath

open DirectSafety.Apriori

/-- The base-reward part of the pass rate fits the base-reward part of the floor's penalty.

The pass reads the root of a total at least that of the floor.

The floor's penalty is read at a weight at least the floor.

The constants satisfy `a * d + b * d ≤ c * b`, which leaves room for the rounding. -/
private theorem pass_first (a b c d BRF EB φ w s T : ℕ) (hb : 0 < b) (hd : 0 < d) (hs : 0 < s)
    (sT : s ≤ T) (sφ : s ≤ φ) (hw : φ ≤ w) (hBRF : 1 ≤ BRF) (ratio : a * d + b * d ≤ c * b) :
    a * BRF * EB / (b * T) * φ ≤ EB * (c * BRF * w / (d * s)) := by
  set Q1 := a * BRF * EB / (b * T) with hQ1
  set P := c * BRF * w / (d * s) with hP
  have h1 : Q1 * (b * T) ≤ a * BRF * EB := Nat.div_mul_le_self _ _
  have h2 : c * BRF * w < (P + 1) * (d * s) := by
    have := Nat.lt_mul_div_succ (c * BRF * w) (Nat.mul_pos hd hs)
    rw [← hP] at this
    linarith
  have step1 : Q1 * φ * (b * d * s) ≤ a * d * BRF * EB * φ := by
    calc Q1 * φ * (b * d * s) = (Q1 * (b * s)) * φ * d := by ring
      _ ≤ (Q1 * (b * T)) * φ * d := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ sT)
      _ ≤ (a * BRF * EB) * φ * d := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ h1
      _ = a * d * BRF * EB * φ := by ring
  have step2 : b * EB * (d * s) ≤ b * d * BRF * EB * φ := by
    have : d * s ≤ d * (BRF * φ) :=
      Nat.mul_le_mul_left _ (sφ.trans (Nat.le_mul_of_pos_left _ hBRF))
    calc b * EB * (d * s) ≤ b * EB * (d * (BRF * φ)) := Nat.mul_le_mul_left _ this
      _ = b * d * BRF * EB * φ := by ring
  have step3 : (a * d + b * d) * BRF * EB * φ ≤ b * EB * (c * BRF * w) := by
    calc (a * d + b * d) * BRF * EB * φ ≤ (c * b) * BRF * EB * φ := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact ratio
      _ ≤ (c * b) * BRF * EB * w := Nat.mul_le_mul_left _ hw
      _ = b * EB * (c * BRF * w) := by ring
  have step4 : b * EB * (c * BRF * w) ≤ b * EB * (P * (d * s)) + b * EB * (d * s) := by
    have : c * BRF * w ≤ P * (d * s) + d * s := by linarith
    calc b * EB * (c * BRF * w) ≤ b * EB * (P * (d * s) + d * s) := Nat.mul_le_mul_left _ this
      _ = b * EB * (P * (d * s)) + b * EB * (d * s) := by ring
  have key : Q1 * φ * (b * d * s) ≤ EB * P * (b * d * s) := by
    have e : (a * d + b * d) * BRF * EB * φ = a * d * BRF * EB * φ + b * d * BRF * EB * φ := by ring
    have e2 : b * EB * (P * (d * s)) = EB * P * (b * d * s) := by ring
    omega
  exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos (Nat.mul_pos hb hd) hs)

/-- The leak part of the pass rate fits the leak part of the floor's penalty.

The divisor of the penalty is at most the divisor of the pass.

The score of the pass is at most that of the penalty, and the rounding costs one. -/
private theorem pass_second (bias IPQ IPD EB score S' φ w : ℕ) (hIPD : 0 < IPD)
    (div : IPD ≤ bias * IPQ) (sc : score + bias ≤ S') (hw : φ ≤ w) :
    EB * (score + bias) / (bias * IPQ) * φ ≤ EB * (w * S' / IPD + 1) := by
  set Q2 := EB * (score + bias) / (bias * IPQ) with hQ2
  set R := w * S' / IPD with hR
  have h0 : Q2 ≤ EB * (score + bias) / IPD := Nat.div_le_div_left div hIPD
  have h1 : (EB * (score + bias) / IPD) * IPD ≤ EB * (score + bias) := Nat.div_mul_le_self _ _
  have h2 : w * S' < (R + 1) * IPD := by
    have := Nat.lt_mul_div_succ (w * S') hIPD
    rw [← hR] at this
    linarith
  have key : Q2 * φ * IPD ≤ EB * (R + 1) * IPD := by
    calc Q2 * φ * IPD ≤ (EB * (score + bias) / IPD) * φ * IPD :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h0)
      _ = ((EB * (score + bias) / IPD) * IPD) * φ := by ring
      _ ≤ (EB * (score + bias)) * φ := Nat.mul_le_mul_right _ h1
      _ ≤ (EB * S') * w := Nat.mul_le_mul (Nat.mul_le_mul_left _ sc) hw
      _ = EB * (w * S') := by ring
      _ ≤ EB * ((R + 1) * IPD) := Nat.mul_le_mul_left _ h2.le
      _ = EB * (R + 1) * IPD := by ring
  exact Nat.le_of_mul_le_mul_right key hIPD

/-- The floor path falls by the penalty of its epoch. -/
private theorem floor_succ (x : ForkedBeaconState preset) (high t : ℕ) :
    stakeFloorAt config x high (t + 1) = stakeFloorAt config x high t -
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by
  rfl

/-- The pass rate of a key against the fall of the floor path.

The rate times the floor is at most the key's effective balance times the fall, plus one. -/
private theorem passRate_mul_le {x z : ForkedBeaconState preset} (high t i : ℕ)
    (total : Gwei) (totalOk : getTotalActiveBalance z.state = .ok total)
    -- The floor lies below the total active balance read by the pass.
    (floor : stakeFloorAt config x high t ≤ total.toNat)
    -- It also lies below the weight of the penalty.
    (floorLe : stakeFloorAt config x high t ≤
      stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    -- The floor after the epoch is positive, so its fall is the penalty.
    (positive : 0 < stakeFloorAt config x high (t + 1))
    (divisor : 0 < inactivityPenaltyDivisor preset config)
    (factor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat)
    -- The score of the key at the pass, plus the bias, is within that of the penalty.
    (scored : (if altair : .altair ≤ z.fork then
        (((z.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤
        startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) :
    PinDrift.Internal.passPenaltyRate config z i * stakeFloorAt config x high t ≤
      effectiveAt z i *
        (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) + 1) := by
  have succ := floor_succ (config := config) x high t
  have pen : stakeFloorAt config x high t - stakeFloorAt config x high (t + 1) =
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high t) t := by omega
  rw [pen]
  have fpos : 0 < stakeFloorAt config x high t := by omega
  have rootPos : 0 < (stakeFloorAt config x high t).sqrt := Nat.sqrt_pos.mpr fpos
  have roots := Nat.sqrt_le_sqrt floor
  have quotient : inactivityPenaltyDivisor preset config ≤ config.INACTIVITY_SCORE_BIAS.toNat *
      (EthLib.Consensus.parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat := by
    unfold inactivityPenaltyDivisor
    apply Nat.mul_le_mul_left
    simp only [EthLib.Consensus.parameters]
    split_ifs <;> omega
  have first := pass_first (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat)
    WEIGHT_DENOMINATOR.toNat (3 + BASE_REWARDS_PER_EPOCH.toNat) BASE_REWARDS_PER_EPOCH.toNat
    preset.BASE_REWARD_FACTOR.toNat (effectiveAt z i) (stakeFloorAt config x high t)
    (stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (stakeFloorAt config x high t).sqrt total.toNat.sqrt (by decide) (by decide) rootPos
    roots (Nat.sqrt_le_self _) floorLe factor (by decide)
  have second := pass_second config.INACTIVITY_SCORE_BIAS.toNat
    (EthLib.Consensus.parameters preset z.fork).INACTIVITY_PENALTY_QUOTIENT.toNat
    (inactivityPenaltyDivisor preset config) (effectiveAt z i) _
    (startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1))
    (stakeFloorAt config x high t)
    (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) divisor quotient scored floorLe
  unfold PinDrift.Internal.passPenaltyRate epochPenalty
  dsimp only
  rw [← getTotalActiveBalance_toNat totalOk]
  rw [add_mul]
  linarith

end FloorPath

/-! ## One epoch of a new key -/

section Epoch

open DirectSafety.Apriori DirectSafety.Apriori.Internal

/-- One epoch with no pass, and the penalty of a slashing in it. -/
private theorem same_arith (b' b cap K band X sl Q Bq EB : ℕ)
    (hcap : K ≤ cap) (hQ : 2 ≤ Q) (hB : K + band ≤ Q * Bq)
    (seg : min b' cap ≤ b + X + sl) (hsl : Q * sl ≤ EB)
    (hyst : EB ≤ b' + band) (hcapEB : EB ≤ cap) :
    min b' K ≤ b + X + (if sl = 0 then 0 else Bq) := by
  by_cases z : sl = 0
  · subst z
    simp only [ite_true] at *
    have : min b' K ≤ min b' cap := min_le_min_left _ hcap
    omega
  · simp only [z, ite_false]
    obtain ⟨hEB, hcle⟩ := eb_le_min_band b' cap K band EB hcap hyst hcapEB
    set C := min b' cap with hC
    by_cases cK : C ≤ K
    · have slB : sl ≤ Bq := by
        have : Q * sl ≤ Q * Bq := by omega
        exact Nat.le_of_mul_le_mul_left this (by omega)
      omega
    · have above : K < C := Nat.lt_of_not_ge cK
      have : min b' K = K := by
        apply min_eq_right
        have := min_le_left b' cap
        omega
      rw [this]
      have : Q * sl ≤ Q * (Bq + (C - K)) := by
        have h1 : Q * (C - K) ≥ C - K := Nat.le_mul_of_pos_left _ (by omega)
        have : Q * (Bq + (C - K)) = Q * Bq + Q * (C - K) := by ring
        omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega

/-- The charge for the slashing of a key: the rounded-up initial penalty of the least stake. -/
private def newBq (preset : Preset) : ℕ :=
  (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
    (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) /
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat

/-- The standing hypotheses of the floor of a new key.

They are the guard and the facts that it reads.

They also hold the preset facts that the floor reads. -/
private structure Ctx (config : Config) (checks : SignatureChecks) {preset : Preset}
    (g x : ForkedBeaconState preset) (high : ℕ) where
  shared : Run config checks g x
  genesis : Genesis (config := config) (checks := checks) g
  parameters : DirectSafety.Parameters preset
  caps : CapOrder preset
  aligned : MaxEffectiveBalancesAligned preset
  twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat
  electra : .pectra ≤ x.fork
  fulu : .fusaka ≤ x.fork
  guard : aprioriGuardAt config x high
  delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  vector : 4 ≤ preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat
  big : 9 * (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
    stakeFloorAt config x high 0
  factor : 1 ≤ preset.BASE_REWARD_FACTOR.toNat
  quotientTwo :
    2 ≤ (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  margin : 2400 * (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
      preset.MAX_EFFECTIVE_BALANCE.toNat /
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
      preset.downwardBand - 1) + 2400 * preset.downwardBand + 2400 * newBq preset ≤
    1591 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
  room : 600 * (high + 2 - (getCurrentEpoch x.state).toNat) ≤ stakeFloorAt config x high 0
  bands : preset.IncrementWithinUpwardBand

/-- Along the window, the floor stays within three halves of its start.

The start floor is below the stake at the start, which the funded stake covers.

The funded stake is below the first ceiling, which is below the last.

The guard asks that twice the last ceiling be at most three times the last floor. -/
private theorem Ctx.ratio {g x : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (early : x.fork < .glamsterdam) {s : ℕ}
    (inside : s ≤ high + 1 - (getCurrentEpoch x.state).toNat) :
    2 * stakeFloorAt config x high 0 ≤ 3 * stakeFloorAt config x high s := by
  have ratio := PinDrift.Internal.ratio_of_guard c.electra c.guard
  have first : stakeFloorAt config x high 0 ≤ stakeCeilingAt config x high 0 :=
    (floor_initial_le_reference x high).trans
      ((funding_active_le x early (c.shared.pubkeysDistinct c.genesis)).trans
        (funded_le_ceiling_initial c.electra))
  have anti : stakeFloorAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high s := PinDrift.Internal.stakeFloorAt_anti inside
  have mono : stakeCeilingAt config x high 0 ≤
      stakeCeilingAt config x high (high + 1 - (getCurrentEpoch x.state).toNat) :=
    PinDrift.Internal.stakeCeilingAt_mono c.electra (Nat.zero_le _)
  omega

/-- The debits of key `i` in a list of events: its sync debits and its partial payments. -/
private def keyDebits (i : ℕ) (events : List (BalanceEvent preset)) : ℕ :=
  (events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit i.toUInt64)).sum

/-- The debits of a key add up over two lists of events. -/
private theorem keyDebits_append (i : ℕ) (a b : List (BalanceEvent preset)) :
    keyDebits i (a ++ b) = keyDebits i a + keyDebits i b := by
  simp only [keyDebits, List.map_append, List.sum_append]
  omega

/-- A slashed key is charged the rounded-up initial penalty at the minimum stake plus a band. -/
private def slashedCharge (preset : Preset) (s : ForkedBeaconState preset) (i : ℕ) : ℕ :=
  if ∃ w, s.state.validators.data[i]? = some w ∧ w.slashed = true then newBq preset else 0

/-- The potential claim at an epoch start `m`, along a run `rm` from the start `z` of the climb.

The potential of the key keeps the fraction of the floor that the floor keeps since `z`.

The potential counts the debits of the key and its slashing charge along `rm`. -/
private def EpochClaim (x z : ForkedBeaconState preset) (high i : ℕ) {m : ForkedBeaconState preset}
    (rm : Run config checks z m) : Prop :=
  ∃ events, rm.balanceEvents high = .ok events ∧
    2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      2 * (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
          keyDebits i events + slashedCharge preset m i) *
        stakeFloorAt config x high
          ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat)

/-- The facts on the cap and the slashing charge that each step of the floor of a key reads.

The slashing quotient is positive.

The cap lies above `MAX_EFFECTIVE_BALANCE` and above the key's effective balance.

The charge covers the minimum stake plus the downward band after division by the quotient. -/
private theorem Ctx.step_facts {g x m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m)
    {i : ℕ} {val : Validator} (found : m.state.validators.data[i]? = some val) :
    0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        (withdrawalMaxEffectiveBalance preset m.fork val).toNat ∧
      effectiveAt m i ≤ (withdrawalMaxEffectiveBalance preset m.fork val).toNat ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand ≤
        (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat *
          ((preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat) := by
  have positiveQ :
      0 < (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
    have := c.quotientTwo
    omega
  refine ⟨positiveQ,
    UInt64.le_iff_toNat_le.mp (Internal.minimum_cap c.caps val),
    ?_, le_smul_ceilDiv (β := Nat) positiveQ⟩
  have := Run.effectiveBalance_capped (c.shared.append hm) c.genesis c.caps val
      (Array.mem_of_getElem? found)
  have e : effectiveAt m i = val.effectiveBalance.toNat := by simp [effectiveAt, found]
  rw [e]
  exact UInt64.le_iff_toNat_le.mp this

/-- A step is charged `Bq` for a slashing only when the key is slashed in it. -/
private theorem charge_le (P : Prop) [Decidable P] (a Q Bq : ℕ) :
    (if (if P then a / Q else 0) = 0 then 0 else Bq) ≤ (if P then Bq else 0) := by
  by_cases h : P <;> by_cases e : a / Q = 0 <;> simp [h, e]

/-- The floor of a new key over one epoch that a slot step ends.

The potential of a key is the least of its balance and `MAX_EFFECTIVE_BALANCE`, plus the band.

The potential at the start keeps the fraction of the floor, less the rounding error.

It is charged the key's sync debits, its partial payments, and its slashing, once. -/
private theorem Ctx.cross {g x m n z : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m)
    (pre : Run config checks m z) (ok : advanceSlotAcross config checks z = .ok n)
    (early : n.fork < .glamsterdam)
    (within : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (same : getCurrentEpoch z.state = getCurrentEpoch m.state)
    (step : (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    {events : List (BalanceEvent preset)}
    (replayed : (pre.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat =
      .ok events) :
    (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
        (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) +
        ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
          i.toUInt64)).sum +
          (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
            then (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
              (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
                1) /
              (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
            else 0)) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := by
  classical
  have mz := fork_le_of_chainSteps pre.chainSteps
  have hxm := fork_le_of_chainSteps hm.chainSteps
  have zn : z.fork ≤ n.fork := (Step.slot ok).chainStep.fork_le
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt (Nat.le_trans mz zn) early
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans c.fulu hxm
  have shared' := c.shared.append hm
  have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hm.chainSteps)
  obtain ⟨positiveQ, capLe, capEB, hB⟩ := c.step_facts hm found
  obtain ⟨z', pre', post', -, hz', ineq⟩ := PinDrift.Internal.epochFloor shared' c.genesis c.caps
    c.delay
    c.vector positiveQ (pre.snoc (Step.slot ok)) fuluM early
    (Or.inr ⟨z, pre, ok, rfl, same, step⟩) i val found activated exit slashedCond
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat le_rfl replayed
  have zForkLe : z'.fork ≤ n.fork := fork_le_of_chainSteps post'.chainSteps
  have z'Early : z'.fork < .glamsterdam := Nat.lt_of_le_of_lt zForkLe early
  have z'x : Run config checks x z' := hm.append pre'
  have z'epoch : (getCurrentEpoch z'.state).toNat = (getCurrentEpoch m.state).toNat :=
    congrArg UInt64.toNat hz'
  have nz' := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post'.chainSteps)
  have insideM : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have effEq : effectiveAt z' i = effectiveAt m i :=
    run_same_epoch_effective pre' hz' i insideM
  have altairX : .altair ≤ x.fork := Nat.le_trans (by decide) c.fulu
  have altairZ : .altair ≤ z'.fork :=
    Nat.le_trans altairX (Nat.le_trans hxm (fork_le_of_chainSteps pre'.chainSteps))
  have pass : (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
        ∃ total, getTotalActiveBalance z'.state = .ok total then
          PinDrift.Internal.passPenaltyRate config z' i else 0) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      effectiveAt m i * (stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) -
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) + 1) := by
    by_cases h : ∃ total, getTotalActiveBalance z'.state = .ok total
    · obtain ⟨total, totalOk⟩ := h
      have lt : getCurrentEpoch m.state < getCurrentEpoch n.state :=
        UInt64.lt_iff_toNat_lt.mpr (by omega)
      rw [ite_eq_left ⟨lt, total, totalOk⟩]
      have bounds := PinDrift.Internal.total_within_guard c.shared c.genesis c.parameters c.caps
        c.aligned c.twoSlots
        c.electra c.guard z'x z'Early (by omega) totalOk
      have ixeq : ix x z' = (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat := by
        simp only [ix]
        omega
      rw [ixeq] at bounds
      have positive : 0 < stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) :=
        c.guard.2.2.2.2.2.2.2.2.2.2.2.1 _ (by unfold driftHorizon; omega)
      have divisor : 0 < inactivityPenaltyDivisor preset config := c.guard.2.2.2.2.2.2.1
      have scored : (if altair : .altair ≤ z'.fork then
          (((z'.state.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
            config.INACTIVITY_SCORE_BIAS.toNat ≤ startInactivityScore config x +
          config.INACTIVITY_SCORE_BIAS.toNat * ((getCurrentEpoch m.state).toNat -
            (getCurrentEpoch x.state).toNat + 1) := by
        rw [dite_eq_left altairZ]
        have grow : config.INACTIVITY_SCORE_BIAS.toNat ≤ config.INACTIVITY_SCORE_BIAS.toNat *
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        cases found' : (z'.state.inactivityScores altairZ).data[i]? with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          omega
        | some score =>
          have := runScores_le z'x altairX z'Early (Or.inl c.electra) altairZ found'
          simp only [Option.map_some, Option.getD_some]
          have e : (getCurrentEpoch z'.state).toNat - (getCurrentEpoch x.state).toNat =
              (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat := by omega
          rw [e] at this
          rw [Nat.mul_add, Nat.mul_one]
          omega
      have := passRate_mul_le (config := config) (x := x) (z := z') high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) i total totalOk
        bounds.1 (by omega) positive divisor c.factor scored
      rw [effEq] at this
      exact this
    · rw [ite_eq_right (fun h' => h h'.2)]
      simp
  rw [PinDrift.Internal.mspq_fusaka fuluM] at ineq
  set K := preset.MAX_EFFECTIVE_BALANCE.toNat with hK
  set Q := (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
    with hQ
  set band := preset.downwardBand with hband
  set t := (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat with ht
  set Bq := (K + band + Q - 1) / Q with hBq
  have hanti : stakeFloorAt config x high (t + 1) ≤ stakeFloorAt config x high t :=
    PinDrift.Internal.stakeFloorAt_anti (Nat.le_succ t)
  have hzero : stakeFloorAt config x high t ≤ stakeFloorAt config x high 0 :=
    PinDrift.Internal.stakeFloorAt_anti (Nat.zero_le t)
  have nWithin := step
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans hxm (Nat.le_trans mz zn)) early
  have ratio := c.ratio xEarly (s := t + 1) (by omega)
  have roomT := c.room
  have hφ : 6 * Q ≤ stakeFloorAt config x high (t + 1) := by
    have := c.big
    omega
  have hband' : 2 * stakeFloorAt config x high t ≤ 3 * stakeFloorAt config x high (t + 1) := by
    omega
  have bound := step_arith_slash (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    (if getCurrentEpoch m.state < getCurrentEpoch n.state ∧
        ∃ total, getTotalActiveBalance z'.state = .ok total then PinDrift.Internal.passPenaltyRate
          config z' i else 0)
    ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
      i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (stakeFloorAt config x high t) (stakeFloorAt config x high (t + 1))
    (stakeFloorAt config x high t - stakeFloorAt config x high (t + 1)) (effectiveAt m i)
    capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp])
    hyst capEB pass (by omega) hφ hband'
  have charge := charge_le
    (val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true)
    (effectiveAt m i) Q Bq
  have mul := Nat.mul_le_mul_right (stakeFloorAt config x high t)
    (Nat.add_le_add_left charge ((events.map (PinDrift.Internal.syncDebit i)).sum +
      (events.map (floorPartialDebit i.toUInt64)).sum))
  linarith

/-- The floor of a new key over a run inside one epoch.

The least of its balance and `MAX_EFFECTIVE_BALANCE` at the start is at most its balance at the end.

It is charged the key's sync debits, its partial payments, and its slashing, once. -/
private theorem Ctx.inside {g x m n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m) (seg : Run config checks m n)
    (early : n.fork < .glamsterdam)
    (same : getCurrentEpoch n.state = getCurrentEpoch m.state)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    {events : List (BalanceEvent preset)}
    (replayed : seg.balanceEvents (getCurrentEpoch m.state).toNat = .ok events) :
    min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt n i +
      ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
        i.toUInt64)).sum +
        (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
          then (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
              1) / (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
          else 0)) := by
  classical
  have hxm := fork_le_of_chainSteps hm.chainSteps
  have mn := fork_le_of_chainSteps seg.chainSteps
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt mn early
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans c.fulu hxm
  have shared' := c.shared.append hm
  obtain ⟨positiveQ, capLe, capEB, hB⟩ := c.step_facts hm found
  obtain ⟨z', pre', post', -, -, ineq⟩ := PinDrift.Internal.epochFloor shared' c.genesis c.caps
    c.delay
    c.vector positiveQ seg fuluM early (Or.inl same) i val found activated exit slashedCond
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat le_rfl replayed
  rw [PinDrift.Internal.mspq_fusaka fuluM] at ineq
  have noPass : ¬ (getCurrentEpoch m.state < getCurrentEpoch n.state ∧
      ∃ total, getTotalActiveBalance z'.state = .ok total) := by
    intro h
    rw [same] at h
    exact UInt64.lt_irrefl _ h.1
  rw [ite_eq_right noPass] at ineq
  set K := preset.MAX_EFFECTIVE_BALANCE.toNat with hK
  set Q := (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
    with hQ
  set band := preset.downwardBand with hband
  set Bq := (K + band + Q - 1) / Q with hBq
  have bound := same_arith (actualBalanceAt m i) (actualBalanceAt n i)
    (withdrawalMaxEffectiveBalance preset m.fork val).toNat K band
    ((events.map (PinDrift.Internal.syncDebit i)).sum + (events.map (floorPartialDebit
      i.toUInt64)).sum)
    (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
      then effectiveAt m i / Q else 0)
    Q Bq (effectiveAt m i) capLe c.quotientTwo hB (by omega)
    (by split <;> [exact Nat.mul_div_le _ _; simp]) hyst capEB
  have charge := charge_le
    (val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true)
    (effectiveAt m i) Q Bq
  omega

/-- Right after an epoch transition, the effective balance of a key is within the band.

The band lies above its balance. -/
private theorem Ctx.hyst_start {g x m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hm : Run config checks x m)
    (hyst : Hysteresis m.state) {i : ℕ} {val : Validator}
    (found : m.state.validators.data[i]? = some val) :
    effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand := by
  have matched := (run_justified_separated (c.shared.append hm) c.genesis).1.balancesMatch
  have lt : i < m.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have lt' : i < m.state.balances.data.size := by
    unfold BalancesMatch at matched
    omega
  have bal : m.state.balances.data[i]? = some m.state.balances.data[i] :=
    Array.getElem?_eq_getElem lt'
  have := hyst.down i val _ found bal
  simp only [effectiveAt, actualBalanceAt, found, bal, Option.map_some, Option.getD_some]
  exact this

/-- The arithmetic of the last step of the floor of a new key.

The potential keeps `2/3` of its start, less the rounding, and the rounding is below the room.

The preset fact `margin` then leaves the floor of the pin. -/
private theorem final_arith (K band Bq B S C φ0 φk J J' T : ℕ)
    (h1 : 2 * (K + band) * φk ≤ 2 * (B + band + C) * φ0 + 3 * (K + band) * J)
    (h2 : 2 * φ0 ≤ 3 * φk) (hJ : J ≤ J') (room : 400 * J' ≤ φ0) (pos : 0 < φ0)
    (hC : C ≤ S + Bq)
    (margin : 2400 * T + 2400 * band + 2400 * Bq ≤ 1591 * (K + band)) : T ≤ B + S := by
  have a1 : 6 * (K + band) * φk ≤ 6 * (B + band + C) * φ0 + 9 * (K + band) * J := by nlinarith
  have a2 : 4 * (K + band) * φ0 ≤ 6 * (K + band) * φk := by nlinarith
  have a3 : 9 * (K + band) * J * 400 ≤ 9 * (K + band) * φ0 := by
    have : J * 400 ≤ φ0 := by omega
    nlinarith
  have a4 : 1600 * (K + band) * φ0 ≤ 2400 * (B + band + C) * φ0 + 9 * (K + band) * φ0 := by
    nlinarith
  have a5 : 1600 * (K + band) ≤ 2400 * (B + band + C) + 9 * (K + band) := by
    have := Nat.le_of_mul_le_mul_right (a := 1600 * (K + band))
      (b := 2400 * (B + band + C) + 9 * (K + band)) (c := φ0) (by nlinarith) pos
    exact this
  omega

/-- A key slashed on the climb is not due its delayed penalty within the window.

It was unslashed at the start `z` of the climb, so its withdrawal waits a whole slashings vector. -/
private theorem Ctx.slashed_window {g x z m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z) (rm : Run config checks z m)
    (i : ℕ) (v0 val : Validator)
    (found0 : z.state.validators.data[i]? = some v0)
    (found : m.state.validators.data[i]? = some val)
    (unslashed0 : v0.slashed = false) (epoch : ℕ) (inside : epoch ≤ high + 1) :
    val.slashed = true →
      epoch + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat := by
  intro flag
  have lower := rm.newly_slashed_withdrawableEpoch c.caps
    c.delay i v0 val found0 found unslashed0 flag
  have window := c.guard.2.2.2.2.2.2.2.2.2.2.1
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  unfold driftHorizon at window
  omega

/-- The slashing charge of a run adds the charge of its slashing. -/
private theorem slashedCharge_run {m n : ForkedBeaconState preset} (seg : Run config checks m n)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val) :
    slashedCharge preset n i = slashedCharge preset m i +
      (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true
        then newBq preset else 0) := by
  classical
  unfold slashedCharge
  by_cases flag : val.slashed = true
  · obtain ⟨w', wFound', wFlag⟩ := seg.slashedPersistence i val found flag
    have : ∃ w, n.state.validators.data[i]? = some w ∧ w.slashed = true := ⟨w', wFound', wFlag⟩
    have fm : ∃ w, m.state.validators.data[i]? = some w ∧ w.slashed = true := ⟨val, found, flag⟩
    simp [this, fm, flag]
  · have flag' : val.slashed = false := by simpa using flag
    have fm : ¬ ∃ w, m.state.validators.data[i]? = some w ∧ w.slashed = true := by
      rintro ⟨w', h, hf⟩
      rw [found] at h
      cases h
      exact flag hf
    simp [fm, flag']

/-- The potential claim passes the slot step that ends an epoch.

The step is the cross of one epoch, so the claim holds for the next epoch start, one epoch on. -/
private theorem Ctx.advance {g x z m p n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z) (rm : Run config checks z m)
    (ins : Run config checks m p) (ok : advanceSlotAcross config checks p = .ok n)
    (early : n.fork < .glamsterdam) (within : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (same : getCurrentEpoch p.state = getCurrentEpoch m.state)
    (step : (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat + 1)
    (i : ℕ) (val : Validator) (found : m.state.validators.data[i]? = some val)
    (activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exit : ∀ w, n.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat)
    (slashedCond : val.slashed = true → (getCurrentEpoch n.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 < val.withdrawableEpoch.toNat)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    (claim : EpochClaim (config := config) (checks := checks) x z high i rm) :
    EpochClaim (config := config) (checks := checks) x z high i
      (rm.append (ins.snoc (Step.slot ok))) := by
  classical
  obtain ⟨events, replay, ih⟩ := claim
  have mp := fork_le_of_chainSteps ins.chainSteps
  have pn : p.fork ≤ n.fork := (Step.slot ok).chainStep.fork_le
  have hm : Run config checks x m := hz.append rm
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt (Nat.le_trans mp pn) early
  have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hm.chainSteps)
  have zm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rm.chainSteps)
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  -- the events of the segment
  obtain ⟨eseg, hseg⟩ := (ins.snoc (Step.slot ok)).balanceEvents_ok early high
  have local_ : (ins.snoc (Step.slot ok)).balanceEvents (getCurrentEpoch m.state).toNat =
      .ok eseg := by
    rw [← balanceEvents_eq_of_endpoint_le (ins.snoc (Step.slot ok)) within (by omega)]
    exact hseg
  have whole := balanceEvents_append rm (ins.snoc (Step.slot ok)) high replay hseg
  have crossed := Ctx.cross c hm ins ok early within same step i val found activated exit
    slashedCond hyst local_
  have charge := slashedCharge_run (ins.snoc (Step.slot ok)) i val found
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hm.chainSteps) (Nat.le_trans mp pn))
      early
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have pos : 0 < stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    c.guard.2.2.2.2.2.2.2.2.2.2.2.1 _ (by unfold driftHorizon; omega)
  have hanti : stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    PinDrift.Internal.stakeFloorAt_anti (Nat.le_succ _)
  have hzero : stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) ≤
        stakeFloorAt config x high 0 := PinDrift.Internal.stakeFloorAt_anti (Nat.zero_le _)
  have ratio := c.ratio xEarly (s := (getCurrentEpoch m.state).toNat -
    (getCurrentEpoch x.state).toNat) (by omega)
  have band : 2 * stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := by omega
  have e1 : (getCurrentEpoch n.state).toNat - (getCurrentEpoch x.state).toNat =
      (getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1 := by omega
  refine ⟨events ++ eseg, whole, ?_⟩
  rw [e1, charge, keyDebits_append]
  have crossed' : (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat +
        preset.downwardBand) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
        (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) +
        (keyDebits i eseg + (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? = some w ∧
            w.slashed = true then newBq preset else 0)) *
          stakeFloorAt config x high
            ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) := crossed
  have mono : (keyDebits i events + slashedCharge preset m i) *
      stakeFloorAt config x high
        ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1) ≤
      (keyDebits i events + slashedCharge preset m i) *
        stakeFloorAt config x high
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) :=
    Nat.mul_le_mul_left _ hanti
  have stepIneq := chain_step (stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high
      ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat + 1))
    (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
    (min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      keyDebits i events + slashedCharge preset m i)
    (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
      (keyDebits i events + keyDebits i eseg) +
      (slashedCharge preset m i + (if val.slashed = false ∧ ∃ w, n.state.validators.data[i]? =
        some w ∧ w.slashed = true then newBq preset else 0)))
    (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand)
    ((getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat) pos hanti band ih
    (by nlinarith [crossed', mono])
  have e2 : (getCurrentEpoch n.state).toNat - (getCurrentEpoch z.state).toNat =
      (getCurrentEpoch m.state).toNat - (getCurrentEpoch z.state).toNat + 1 := by omega
  rw [e2]
  exact stepIneq

/-- The potential claim carries over the slot step that ends the epoch of a climb state.

The new epoch start also lies within the band of hysteresis, since the step ran the transition. -/
private theorem Ctx.inv_step {g x z y q p' m : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (ok : advanceSlotAcross config checks q = .ok p') (rest : Run config checks p' y)
    (rm : Run config checks z m) (ins : Run config checks m q)
    (cm : getCurrentEpoch m.state = getCurrentEpoch q.state)
    (hyst : effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand)
    (claim : EpochClaim (config := config) (checks := checks) x z high i rm)
    (stepQ : (getCurrentEpoch p'.state).toNat = (getCurrentEpoch q.state).toNat + 1) :
    EpochClaim (config := config) (checks := checks) x z high i
      (rm.append (ins.snoc (Step.slot ok))) ∧
    effectiveAt p' i ≤ actualBalanceAt p' i + preset.downwardBand := by
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  have pEarly : p'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have cmN : (getCurrentEpoch m.state).toNat = (getCurrentEpoch q.state).toNat :=
    congrArg UInt64.toNat cm
  obtain ⟨val, found, life⟩ := rm.registryLifecycle.validators i v0 found0
  have activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [life.activationEpoch activated0]
    exact activated0
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps ins.chainSteps)
      (Step.slot ok).chainStep.fork_le) pEarly
  have slashedCond := c.slashed_window hz rm i v0 val found0 found unslashed0
    (getCurrentEpoch p'.state).toNat (by omega)
  have sameQ : getCurrentEpoch q.state = getCurrentEpoch m.state := cm.symm
  have stepP : (getCurrentEpoch p'.state).toNat = (getCurrentEpoch m.state).toNat + 1 := by
    omega
  have exit' : ∀ w, p'.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat := fun w hw => by
    have := exitLate p' rest w hw
    omega
  have claim' := Ctx.advance c hz rm ins ok pEarly (by omega) sameQ stepP i val found
    activated exit' slashedCond hyst claim
  obtain ⟨val', found', -⟩ := (rm.append (ins.snoc (Step.slot ok))).registryLifecycle.validators
    i v0 found0
  have lt : getCurrentEpoch q.state < getCurrentEpoch p'.state :=
    UInt64.lt_iff_toNat_lt.mpr (by omega)
  have fuluQ : .fusaka ≤ q.fork :=
    Nat.le_trans c.fulu (fork_le_of_chainSteps (hz.append (rm.append ins)).chainSteps)
  exact ⟨claim', Ctx.hyst_start c (hz.append (rm.append (ins.snoc (Step.slot ok))))
    (DirectSafety.Apriori.Internal.hysteresis_of_crossing_slot ok c.bands fuluQ pEarly
      (UInt64.lt_iff_toNat_lt.mp lt)) found'⟩

/-- The potential claim holds at the start of the epoch of every state of the climb.

The climb runs from `z`, where the key holds the maximum effective balance and is unslashed.

The key never exits before the end `y` of the climb.

The state `p` reaches `y`, so it ends no later than `y`. -/
private theorem Ctx.inv {g x z y : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    {p : ForkedBeaconState preset} (rp : Run config checks z p) :
    ∀ (_rest : Run config checks p y), ∃ (m : ForkedBeaconState preset)
      (rm : Run config checks z m) (ins : Run config checks m p),
      rp = rm.append ins ∧ getCurrentEpoch m.state = getCurrentEpoch p.state ∧
      effectiveAt m i ≤ actualBalanceAt m i + preset.downwardBand ∧
      EpochClaim (config := config) (checks := checks) x z high i rm := by
  induction rp with
  | nil =>
    intro _
    refine ⟨z, .nil, .nil, rfl, rfl, hystZ, [], rfl, ?_⟩
    have unflagged : ¬ ∃ w, z.state.validators.data[i]? = some w ∧ w.slashed = true := by
      rintro ⟨w, h, hf⟩
      rw [found0] at h
      cases h
      rw [unslashed0] at hf
      cases hf
    have charge : slashedCharge preset z i = 0 := by simp [slashedCharge, unflagged]
    rw [charge, min_eq_right bal0]
    simp [keyDebits]
  | @snoc q p' pre step ih =>
    intro rest
    obtain ⟨m, rm, ins, eq, cm, hyst, claim⟩ := ih ((Run.nil.snoc step).append rest)
    by_cases same : getCurrentEpoch p'.state = getCurrentEpoch q.state
    · refine ⟨m, rm, ins.snoc step, ?_, cm.trans same.symm, hyst, claim⟩
      rw [eq]
      rfl
    · have bound := ChainStep.epoch_le_succ step.chainStep
      have order := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
      have differ : (getCurrentEpoch p'.state).toNat ≠ (getCurrentEpoch q.state).toNat :=
        fun h => same (UInt64.toNat_inj.mp h)
      cases step with
      | @block fork before after engine signed due ok =>
        exfalso
        apply same
        simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
      | slot ok =>
        obtain ⟨claim', hystP⟩ := Ctx.inv_step c hz early within i v0 found0 unslashed0 activated0
          exitLate ok rest rm ins cm hyst claim (by omega)
        refine ⟨p', rm.append (ins.snoc (Step.slot ok)), .nil, ?_, rfl, hystP, claim'⟩
        rw [eq]
        rfl

/-- The arithmetic of the climb: the potential claim gives the floor of the pin.

The claim starts at the epoch `cz` and ends at the epoch `ck`, within the window. -/
private theorem Ctx.arith {g x : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (xEarly : x.fork < .glamsterdam) (cz ck : ℕ)
    (xz : (getCurrentEpoch x.state).toNat ≤ cz) (zk : cz ≤ ck) (inside : ck ≤ high + 1)
    (B kd sc : ℕ) (hsc : sc ≤ newBq preset)
    (claim : 2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat) ≤
      2 * (B + preset.downwardBand + (kd + sc)) *
        stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) * (ck - cz)) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ B + kd := by
  have cxIn : (getCurrentEpoch x.state).toNat ≤ high + 1 := by omega
  have ratio0 := c.ratio xEarly (s := cz - (getCurrentEpoch x.state).toNat) (by omega)
  have ratioK := c.ratio xEarly (s := ck - (getCurrentEpoch x.state).toNat) (by omega)
  have hzero : stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) ≤
      stakeFloorAt config x high 0 := PinDrift.Internal.stakeFloorAt_anti (Nat.zero_le _)
  have roomT := c.room
  have unitJ : 1 ≤ high + 2 - (getCurrentEpoch x.state).toNat := by omega
  have phi : 2 * stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat) ≤
      3 * stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat) := by omega
  exact final_arith preset.MAX_EFFECTIVE_BALANCE.toNat preset.downwardBand (newBq preset) B kd
    (kd + sc) (stakeFloorAt config x high (cz - (getCurrentEpoch x.state).toNat))
    (stakeFloorAt config x high (ck - (getCurrentEpoch x.state).toNat)) (ck - cz)
    (high + 2 - (getCurrentEpoch x.state).toNat) _ claim phi (by omega) (by omega) (by omega)
    (by omega) c.margin

/-- The least of a key's balance and the maximum, plus the debits, stays above the floor of the pin.

The state `p` lies on the climb, before its end `y`, so the key cannot yet have exited.

The least stake of the key is `2/3` of the maximum less the slashing quotient and the band. -/
private theorem Ctx.claimAt {g x z y p : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (rp : Run config checks z p) (rest : Run config checks p y)
    (lt : (getCurrentEpoch p.state).toNat < (getCurrentEpoch y.state).toNat) :
    ∃ events, rp.balanceEvents high = .ok events ∧
      2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i events := by
  classical
  obtain ⟨m, rm, ins, eq, cm, hyst, events, replay, ih⟩ :=
    c.inv hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate rp rest
  have pEarly : p.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps ins.chainSteps) pEarly
  have hm : Run config checks x m := hz.append rm
  obtain ⟨val, found, life⟩ := rm.registryLifecycle.validators i v0 found0
  have activated : val.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [life.activationEpoch activated0]
    exact activated0
  have cmN : (getCurrentEpoch m.state).toNat = (getCurrentEpoch p.state).toNat :=
    congrArg UInt64.toNat cm
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  obtain ⟨eins, hins⟩ := ins.balanceEvents_ok pEarly high
  have local_ : ins.balanceEvents (getCurrentEpoch m.state).toNat = .ok eins := by
    rw [← balanceEvents_eq_of_endpoint_le (high := high)
      (localHigh := (getCurrentEpoch m.state).toNat) ins (by omega) (by omega)]
    exact hins
  have exit' : ∀ w, p.state.validators.data[i]? = some w →
      (getCurrentEpoch m.state).toNat + 1 < w.exitEpoch.toNat := fun w hw => by
    have := exitLate p rest w hw
    omega
  have slashedCond := c.slashed_window hz rm i v0 val found0 found unslashed0
    (getCurrentEpoch p.state).toNat (by omega)
  have inside := Ctx.inside c hm ins pEarly cm.symm i val found activated exit' slashedCond hyst
    local_
  have charge := slashedCharge_run ins i val found
  have whole := balanceEvents_append rm ins high replay hins
  refine ⟨events ++ eins, by rw [eq]; exact whole, ?_⟩
  -- the arithmetic of the climb
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  have zm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rm.chainSteps)
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps)
      (Nat.le_trans (fork_le_of_chainSteps rm.chainSteps) (fork_le_of_chainSteps ins.chainSteps)))
      pEarly
  have e2 : min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt p i +
      (keyDebits i eins + (if val.slashed = false ∧ ∃ w, p.state.validators.data[i]? = some w ∧
        w.slashed = true then newBq preset else 0)) := by
    have := inside
    unfold keyDebits
    unfold newBq
    simpa using this
  have step : min (actualBalanceAt m i) preset.MAX_EFFECTIVE_BALANCE.toNat +
      preset.downwardBand + keyDebits i events + slashedCharge preset m i ≤
      actualBalanceAt p i + preset.downwardBand + keyDebits i (events ++ eins) +
        slashedCharge preset p i := by
    rw [keyDebits_append, charge]
    omega
  have chargeLe : slashedCharge preset p i ≤ newBq preset := by
    unfold slashedCharge
    split <;> omega
  have h1 : 2 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
      stakeFloorAt config x high
        ((getCurrentEpoch p.state).toNat - (getCurrentEpoch x.state).toNat) ≤
      2 * (actualBalanceAt p i + preset.downwardBand +
        (keyDebits i (events ++ eins) + slashedCharge preset p i)) *
        stakeFloorAt config x high
          ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) +
      3 * (preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand) *
        ((getCurrentEpoch p.state).toNat - (getCurrentEpoch z.state).toNat) := by
    rw [← cmN]
    refine ih.trans ?_
    have := Nat.mul_le_mul_right (stakeFloorAt config x high
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat))
      (Nat.mul_le_mul_left 2 step)
    have e : actualBalanceAt p i + preset.downwardBand + keyDebits i (events ++ eins) +
        slashedCharge preset p i = actualBalanceAt p i + preset.downwardBand +
          (keyDebits i (events ++ eins) + slashedCharge preset p i) := by omega
    rw [e] at this
    omega
  exact c.arith xEarly (getCurrentEpoch z.state).toNat (getCurrentEpoch p.state).toNat xz
    (by omega) (by omega) _ _ _ chargeLe h1

/-- A prefix of a list of events debits a key at most as much as the list. -/
private theorem keyDebits_le_of_prefix (i : ℕ) {a b : List (BalanceEvent preset)} (h : a <+: b) :
    keyDebits i a ≤ keyDebits i b := by
  obtain ⟨t, rfl⟩ := h
  rw [keyDebits_append]
  omega

/-- A state of the climb that precedes its end has the floor of the pin.

The debits are those of the run that contains it. -/
private theorem Ctx.floorRun {g x z y p w : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (rp : Run config checks z p) (rest : Run config checks p w) (restY : Run config checks p y)
    (lt : (getCurrentEpoch p.state).toNat < (getCurrentEpoch y.state).toNat)
    {Ef : List (BalanceEvent preset)} (hEf : (rp.append rest).balanceEvents high = .ok Ef) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
  obtain ⟨events, replay, bound⟩ := c.claimAt hz early within i v0 found0 unslashed0 activated0
    bal0 hystZ exitLate rp restY lt
  obtain ⟨before, beforeOk, prefix_⟩ := Run.balanceEvents_prefix rp rest high Ef hEf
  rw [replay] at beforeOk
  cases beforeOk
  have := keyDebits_le_of_prefix i prefix_
  omega

/-- The end of the climb, the first state of the last epoch, has the floor of the pin too. -/
private theorem Ctx.claimEnd {g x z y zz n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (pre0 : Run config checks z zz) (ok : advanceSlotAcross config checks zz = .ok n)
    (rest0 : Run config checks n y)
    (stepN : (getCurrentEpoch n.state).toNat = (getCurrentEpoch zz.state).toNat + 1)
    {Ef : List (BalanceEvent preset)}
    (hEf : (pre0.snoc (Step.slot ok)).balanceEvents high = .ok Ef) :
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 ≤ actualBalanceAt n i + keyDebits i Ef := by
  obtain ⟨m, rm, ins, eq, cm, hyst, claim⟩ := c.inv hz early within i v0 found0 unslashed0
    activated0 bal0 hystZ exitLate pre0 ((Run.nil.snoc (Step.slot ok)).append rest0)
  obtain ⟨claim', -⟩ := Ctx.inv_step c hz early within i v0 found0 unslashed0 activated0
    exitLate ok rest0 rm ins cm hyst claim stepN
  obtain ⟨events, replay, ineq⟩ := claim'
  have same : pre0.snoc (Step.slot ok) = rm.append (ins.snoc (Step.slot ok)) := by
    rw [eq]
    rfl
  rw [same, replay] at hEf
  cases hEf
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps hz.chainSteps)
  have zk := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
    (pre0.snoc (Step.slot ok)).chainSteps)
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps)
      (fork_le_of_chainSteps (pre0.snoc (Step.slot ok)).chainSteps)) nEarly
  have restEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have chargeLe : slashedCharge preset n i ≤ newBq preset := by
    unfold slashedCharge
    split <;> omega
  have := c.arith xEarly (getCurrentEpoch z.state).toNat (getCurrentEpoch n.state).toNat xz zk
    (by omega) (min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat) (keyDebits i Ef) _
    chargeLe
    (by
      have e : min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
          (keyDebits i Ef + slashedCharge preset n i) =
          min (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat + preset.downwardBand +
            keyDebits i Ef + slashedCharge preset n i := by omega
      rw [e]
      exact ineq)
  have := Nat.min_le_left (actualBalanceAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat
  omega

/-- The state inside a slot step has the registry and the balances of the state after its upgrades.

The upgrades after Electra and before Gloas keep both. -/
private theorem mid_data {s n : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : n.fork < .glamsterdam)
    (upgrades : processUpgrades config checks s = .ok n) :
    n.state.validators.data = s.state.validators.data ∧
      n.state.balances.data = s.state.balances.data := by
  have target : .pectra ≤ n.fork := Nat.le_trans electra (processUpgrades_fork_le upgrades)
  obtain ⟨validators, balances, -⟩ := processUpgrades_retained_data electra early upgrades target
  exact ⟨validators, balances⟩

/-- Every state on the balance path of the climb has the key, and the floor of the pin. -/
private theorem Ctx.floors {g x z y zz n : ForkedBeaconState preset} {high : ℕ}
    (c : Ctx config checks g x high) (hz : Run config checks x z)
    (early : y.fork < .glamsterdam) (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ℕ) (v0 : Validator) (found0 : z.state.validators.data[i]? = some v0)
    (unslashed0 : v0.slashed = false) (activated0 : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (bal0 : preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i)
    (hystZ : effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand)
    (exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y) (w : Validator),
      n.state.validators.data[i]? = some w → (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat)
    (pre0 : Run config checks z zz) (ok : advanceSlotAcross config checks zz = .ok n)
    (rest0 : Run config checks n y)
    (stepN : (getCurrentEpoch n.state).toNat = (getCurrentEpoch zz.state).toNat + 1)
    {Ef : List (BalanceEvent preset)}
    (hEf : (pre0.snoc (Step.slot ok)).balanceEvents high = .ok Ef) :
    ∀ p ∈ (pre0.snoc (Step.slot ok)).balancePath,
      (∃ val, p.state.validators.data[i]? = some val) ∧
        2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
          preset.MAX_EFFECTIVE_BALANCE.toNat /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
          preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
  have nY := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  -- a state of the run before the last step
  have runState : ∀ (p : ForkedBeaconState preset) (rp : Run config checks z p)
      (rest : Run config checks p zz), pre0 = rp.append rest →
      (∃ val, p.state.validators.data[i]? = some val) ∧
        2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
          preset.MAX_EFFECTIVE_BALANCE.toNat /
            (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
          preset.downwardBand - 1 ≤ actualBalanceAt p i + keyDebits i Ef := by
    intro p rp rest eq
    have pz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
    obtain ⟨val, found, -⟩ := rp.registryLifecycle.validators i v0 found0
    refine ⟨⟨val, found⟩, ?_⟩
    refine c.floorRun hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate rp
      (rest.snoc (Step.slot ok)) ((rest.snoc (Step.slot ok)).append rest0) (by omega) ?_
    rw [eq] at hEf
    exact hEf
  intro p member
  simp only [Run.balancePath, List.mem_append] at member
  rcases member with member | member
  · rcases Run.mem_balancePath_split pre0 member with ⟨rp, rest, eq⟩ |
      ⟨q, n', rq, ok', rest, adv, eq, -, hp, upgrades⟩
    · exact runState p rp rest eq
    · have step := runState n' (rq.snoc (Step.slot ok')) rest eq
      have qFork : x.fork ≤ q.fork :=
        Nat.le_trans (fork_le_of_chainSteps hz.chainSteps) (fork_le_of_chainSteps rq.chainSteps)
      have n'Early : n'.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps)
          (Nat.lt_of_le_of_lt (fork_le_of_chainSteps (Run.nil.snoc (Step.slot ok)).chainSteps)
            nEarly)
      have data := mid_data (config := config) (checks := checks) (s := ⟨q.fork, adv⟩)
        (Nat.le_trans c.electra qFork) n'Early upgrades
      subst hp
      obtain ⟨⟨val, found⟩, bound⟩ := step
      refine ⟨⟨val, ?_⟩, ?_⟩
      · simpa [data.1] using found
      · have : actualBalanceAt ⟨q.fork, adv⟩ i = actualBalanceAt n' i := by
          simp only [actualBalanceAt, data.2]
        rw [this]
        exact bound
  · obtain ⟨adv, advOk, upgrades⟩ := bind_ok_iff.mp ok
    simp only [Step.balancePath, advOk, Except.toOption, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · exact runState _ pre0 .nil rfl
    · have zzFork : .pectra ≤ zz.fork := Nat.le_trans c.electra
        (Nat.le_trans (fork_le_of_chainSteps hz.chainSteps) (fork_le_of_chainSteps pre0.chainSteps))
      have data := mid_data (config := config) (checks := checks) (s := ⟨zz.fork, adv⟩) zzFork
        nEarly upgrades
      obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      refine ⟨⟨val, ?_⟩, ?_⟩
      · simpa [data.1] using found
      · have := c.claimEnd hz early within i v0 found0 unslashed0 activated0 bal0 hystZ exitLate
          pre0 ok rest0 stepN hEf
        have e : actualBalanceAt ⟨zz.fork, adv⟩ i = actualBalanceAt n i := by
          simp only [actualBalanceAt, data.2]
        rw [e]
        exact this
    · obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      exact ⟨⟨val, found⟩, c.claimEnd hz early within i v0 found0 unslashed0 activated0 bal0 hystZ
        exitLate pre0 ok rest0 stepN hEf⟩

end Epoch

/-- The last step of the floor of a new key, in naturals.

The effective balance is at least the least of three bounds.

It is therefore at least the stake of the pin, less the increment.

The debits are added back. -/
private theorem final_floor (A inc S effZ effN K : ℕ) (hA : A ≤ K) (hZ : K ≤ effZ)
    (h : min effZ (min K (A - 1 - S + 1 - inc)) ≤ effN) : A - inc ≤ effN + S := by
  rw [min_eq_right ((min_le_left _ _).trans hZ)] at h
  simp only [Nat.min_def] at h
  split_ifs at h <;> omega

/-! ## The effective balance of a new key -/

/-- A key that has an activation epoch two epochs ahead holds the largest effective balance there.

It is funded: its balance is at least its effective balance, which is at least the maximum.

Its effective balance is at most its balance and the downward band, and it is unslashed. -/
theorem Run.funded_at_start {g x z : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (pre : Run config checks x z) (zEarly : z.fork < .glamsterdam)
    (i : ℕ) {v0 : Validator} (found0 : z.state.validators.data[i]? = some v0)
    (actNeFar : v0.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (act : (getCurrentEpoch z.state).toNat + 2 = v0.activationEpoch.toNat) :
    v0.slashed = false ∧ preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z i ∧
      effectiveAt z i ≤ actualBalanceAt z i + preset.downwardBand ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ effectiveAt z i := by
  have electraZ : .pectra ≤ z.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have actBound := v0.activationEpoch.toNat_lt
  have finite : getCurrentEpoch z.state < FAR_FUTURE_EPOCH :=
    UInt64.lt_iff_toNat_lt.mpr (by
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega)
  have plusOne : (getCurrentEpoch z.state + 1).toNat = (getCurrentEpoch z.state).toNat + 1 := by
    rw [UInt64.toNat_add]
    have : (1 : UInt64).toNat = 1 := rfl
    rw [this]
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    exact Nat.mod_eq_of_lt (by omega)
  have lessAct : getCurrentEpoch z.state + 1 < v0.activationEpoch :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [plusOne]; omega)
  obtain ⟨funded, maxLe, unslashed⟩ := (Internal.run_eligible_balance (shared.append pre) genesis
    caps aligned zEarly finite).2 electraZ i v0 found0
    (Or.inl actNeFar)
    (UInt64.lt_iff_toNat_lt.mpr (by have := UInt64.lt_iff_toNat_lt.mp lessAct; omega))
  obtain ⟨bal, hbal, effLe⟩ := funded (by
    have := UInt64.lt_iff_toNat_lt.mp lessAct
    omega)
  refine ⟨unslashed, ?_, ?_, ?_⟩
  · have := UInt64.le_iff_toNat_le.mp (UInt64.le_trans maxLe effLe)
    simpa [actualBalanceAt, hbal] using this
  · have := UInt64.le_iff_toNat_le.mp effLe
    simp only [effectiveAt, actualBalanceAt, found0, hbal, Option.map_some, Option.getD_some]
    omega
  · have := UInt64.le_iff_toNat_le.mp maxLe
    simpa [effectiveAt, found0] using this

open DirectSafety.Apriori.Internal in
/-- A key created on the run keeps its effective balance near two thirds of the maximum. -/
theorem Run.new_key_effective_floor {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (fulu : .fusaka ≤ x.fork) (high : ℕ)
    -- Under the guard at the split, the key's effective balance at the end of the window is large.
    (guard : DirectSafety.Apriori.aprioriGuardAt config x high)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (window : preset.SeedLookaheadAtLeastThree)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (bands : preset.IncrementWithinUpwardBand) (facts : PinPresetFacts preset)
    (i : ℕ)
    -- The key is scheduled at the split.
    --
    -- It is not active by the epoch after the split, and it is active at the end.
    (pending : ∀ v, x.state.validators.data[i]? = some v →
      (getCurrentEpoch x.state).toNat + 1 < v.activationEpoch.toNat)
    (active : isActiveAt y.state (getCurrentEpoch y.state) i = true)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    -- The effective balance is at least two thirds of `MAX_EFFECTIVE_BALANCE`.
    --
    -- The bound loses the initial slashing penalty, the downward band and an increment.
    2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      -- The key's sync debits and its partial payments are added back.
      effectiveAt y i + (events.map (PinDrift.Internal.syncDebit i)).sum +
        (events.map (floorPartialDebit i.toUInt64)).sum := by
  -- The potential, the least of balance and maximum plus the band, follows the floor path.
  classical
  obtain ⟨wa, foundA, activeA⟩ := isActiveAt_eq_true_iff.mp active
  have assignedA := Consensus.Internal.assigned_of_active activeA
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeA
  have exitGt := UInt64.lt_iff_toNat_lt.mp activeA.2
  have lowA := UInt64.le_iff_toNat_le.mp activeA.1
  obtain ⟨z, pre, post, v0, vy, split, found0, foundY, sameAct, actEq, actLe⟩ :=
    PinDrift.Internal.Run.start_state tail window i pending
      ⟨wa, foundA, assignedA, activeA.1⟩ fun vy found => by
      obtain rfl := Option.some.inj (found.symm.trans foundA)
      omega
  obtain rfl := Option.some.inj (foundY.symm.trans foundA)
  have farToNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have exitBound := vy.exitEpoch.toNat_lt
  have xz := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have zy := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have zEarly : z.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have electraZ : .pectra ≤ z.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have fuluZ : .fusaka ≤ z.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have actNeFar : v0.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro h
    rw [sameAct] at h
    have := congrArg UInt64.toNat h
    omega
  have actZ : (getCurrentEpoch z.state).toNat + 2 = v0.activationEpoch.toNat := by
    rw [sameAct]
    exact actEq
  obtain ⟨unslashed, bal0, hystZ, effZ⟩ :=
    PinDrift.Internal.Run.funded_at_start shared genesis caps aligned electra pre zEarly i found0
      actNeFar actZ
  have exitLate : ∀ (n : ForkedBeaconState preset) (_rest : Run config checks n y)
      (w : Validator), n.state.validators.data[i]? = some w →
      (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat := by
    intro n rest w found
    obtain ⟨later, foundL, life⟩ := rest.registryLifecycle.validators i w found
    have same : later = vy := Option.some.inj (foundL.symm.trans foundY)
    subst same
    by_cases assigned : w.exitEpoch = FAR_FUTURE_EPOCH
    · rw [assigned, farToNat]
      omega
    · rw [← life.exitEpoch assigned]
      exact exitGt
  obtain ⟨room, big⟩ := PinDrift.Internal.first_floor_of_guard shared genesis aligned
    (Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps tail.chainSteps) early) electra guard facts
  have c : Ctx config checks g x high :=
    { shared := shared, genesis := genesis, parameters := parameters, caps := caps,
      aligned := aligned, twoSlots := twoSlots, electra := electra, fulu := fulu, guard := guard,
      delay := delay, vector := facts.vector, big := big, factor :=
        (PinDrift.Internal.PinPresetFacts.reward facts),
      quotientTwo := facts.quotient, margin := facts.margin, room := room,
      bands := bands }
  -- the last epoch starts with a slot step
  obtain ⟨zz, n, pre0, ok, rest0, splitPost, hzz, hn⟩ :=
    Run.cross_split post ((getCurrentEpoch y.state).toNat - 1) (by omega) (by omega)
  have nY := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest0.chainSteps)
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) early
  obtain ⟨Ef, hEf⟩ := (pre0.snoc (Step.slot ok)).balanceEvents_ok nEarly high
  have floors := c.floors pre early within i v0 found0 unslashed actNeFar bal0 hystZ exitLate pre0
    ok rest0 (by omega) hEf
  -- the debits of the climb are debits of the run
  have tailEq : tail = (pre.append (pre0.snoc (Step.slot ok))).append rest0 := by
    rw [split, splitPost, Run.append_assoc]
  obtain ⟨ePre, hePre⟩ := pre.balanceEvents_ok (Nat.lt_of_le_of_lt (fork_le_of_chainSteps
    (pre0.snoc (Step.slot ok)).chainSteps) nEarly) high
  have whole := balanceEvents_append pre (pre0.snoc (Step.slot ok)) high hePre hEf
  rw [tailEq] at replayed
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix
    (pre.append (pre0.snoc (Step.slot ok))) rest0 high events replayed
  rw [whole] at beforeOk
  cases beforeOk
  have debits : keyDebits i Ef ≤ keyDebits i events := by
    have := keyDebits_le_of_prefix i isPrefix
    rw [keyDebits_append] at this
    omega
  -- the balance floor along the climb, and the effective balance by hysteresis
  have nIn : i < z.state.validators.data.size := (Array.getElem?_eq_some_iff.mp found0).1
  have hBal := Run.effective_floor_of_balance_floor (pre0.snoc (Step.slot ok)) nEarly fuluZ
    (Nat.lt_of_lt_of_le (by norm_num) facts.incrementSize) i nIn
    (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - 1 - keyDebits i events) preset.MAX_EFFECTIVE_BALANCE.toNat
    (fun p member => by
      have := (floors p member).2
      omega)
    (fun p member => by
      obtain ⟨⟨val, found⟩, -⟩ := floors p member
      have := UInt64.le_iff_toNat_le.mp
        (Internal.minimum_cap caps (h := p.fork) val)
      simpa [PinTerms.capAt, found] using this)
  have sameEff : effectiveAt y i = effectiveAt n i := by
    have inside : i < n.state.validators.data.size := by
      obtain ⟨val, found, -⟩ := (pre0.snoc (Step.slot ok)).registryLifecycle.validators i v0 found0
      exact (Array.getElem?_eq_some_iff.mp found).1
    exact run_same_epoch_effective rest0 (UInt64.toNat_inj.mp (by omega)) i inside
  rw [sameEff]
  have kd : keyDebits i events = (events.map (PinDrift.Internal.syncDebit i)).sum +
      (events.map (floorPartialDebit i.toUInt64)).sum := rfl
  have fin := final_floor
    (2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand) preset.EFFECTIVE_BALANCE_INCREMENT.toNat (keyDebits i events)
    (effectiveAt z i) (effectiveAt n i) preset.MAX_EFFECTIVE_BALANCE.toNat
    ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (by omega))) effZ hBal
  omega

end PinDrift.Internal

end

end EthLib.Consensus.Models.Network
