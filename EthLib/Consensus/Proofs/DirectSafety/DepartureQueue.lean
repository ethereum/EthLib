module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.PartialWithdrawalQueue
public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Departure queue accounting

A queue call records its assigned epoch as well as the balance that it spends.

Partial withdrawals spend exit capacity without assigning a validator's exit.

Before Gloas, the departure charges of a run fit the queue capacity of a window of epochs.

The balance queues are specified by [EIP-7251].

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

/-- One successful balance-queue call, including the queue before and after it. -/
structure DepartureQueueCall where
  earliest : Epoch
  available : Gwei
  first : Epoch
  rate : Gwei
  amount : Gwei
  epoch : Epoch
  left : Gwei
  computed : churnQueue earliest first rate available amount = .ok (epoch, left)

/-- The capacity still usable through a fixed last epoch. -/
private def departureQueuePotential (high cap : Nat) (epoch : Epoch) (left : Gwei) : Nat :=
  if epoch.toNat ≤ high then left.toNat + (high - epoch.toNat) * cap else 0

/-- A call exits at or after the open queue epoch and at or after its first epoch. -/
private theorem DepartureQueueCall.epoch_ge (call : DepartureQueueCall) :
    call.earliest.toNat ≤ call.epoch.toNat ∧ call.first.toNat ≤ call.epoch.toNat := by
  have placed := UInt64.le_iff_toNat_le.mp (churnQueue_spend call.computed).1
  rw [Base.Uint64.toNat_max] at placed
  exact ⟨by omega, by omega⟩

/-- A call cannot move the open queue epoch backwards. -/
private theorem DepartureQueueCall.epoch_mono (call : DepartureQueueCall) :
    call.earliest.toNat ≤ call.epoch.toNat := call.epoch_ge.1

/-- Spending beyond the horizon counts nothing and leaves no usable capacity inside it. -/
private theorem DepartureQueueCall.window_spend (call : DepartureQueueCall) (high cap : Nat)
    (rateBound : call.rate.toNat ≤ cap) :
    (if call.epoch.toNat ≤ high then call.amount.toNat else 0) +
      departureQueuePotential high cap call.epoch call.left ≤
        departureQueuePotential high cap call.earliest call.available := by
  have ordered := call.epoch_mono
  by_cases inside : call.epoch.toNat ≤ high
  · have before : call.earliest.toNat ≤ high := by omega
    obtain ⟨_, spent⟩ := churnQueue_window_le cap [(call.first, call.rate, call.amount)]
      call.earliest call.available call.epoch call.left
      (by intro c member; simpa using List.mem_singleton.mp member ▸ rateBound)
      (by simpa using call.computed)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at spent
    simp only [departureQueuePotential, inside, before, ↓reduceIte]
    have distance : high - call.earliest.toNat =
        (call.epoch.toNat - call.earliest.toNat) + (high - call.epoch.toNat) := by omega
    rw [distance, Nat.add_mul]
    omega
  · simp only [departureQueuePotential, inside, ↓reduceIte, Nat.zero_add]
    exact Nat.zero_le _

/-- A concrete sequence uses each call's output queue as the next call's input queue. -/
inductive DepartureQueueTrace : Epoch → Gwei → List DepartureQueueCall → Epoch → Gwei → Prop
  | nil (epoch : Epoch) (left : Gwei) : DepartureQueueTrace epoch left [] epoch left
  | cons (call : DepartureQueueCall) {rest : List DepartureQueueCall} {epoch : Epoch}
      {left : Gwei} (tail : DepartureQueueTrace call.epoch call.left rest epoch left) :
      DepartureQueueTrace call.earliest call.available (call :: rest) epoch left

/-- Filtering calls by completion epoch preserves the queue budget through that epoch. -/
private theorem DepartureQueueTrace.window_le {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left) (high cap : Nat)
    (rates : ∀ call ∈ calls, call.rate.toNat ≤ cap) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map fun call => call.amount.toNat).sum +
      departureQueuePotential high cap epoch left ≤
        departureQueuePotential high cap earliest available := by
  induction trace with
  | nil => simp
  | cons call tail ih =>
    have step := call.window_spend high cap (rates call (by simp))
    have rest := ih (fun c member => rates c (List.mem_cons_of_mem _ member))
    by_cases inside : call.epoch.toNat ≤ high
    · simp only [List.filter_cons, decide_eq_true inside, ↓reduceIte,
        List.map_cons, List.sum_cons]
      rw [ite_eq_left inside] at step
      omega
    · simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_right inside] at step
      omega

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A transition charges each registry index at most once. -/
private theorem departureCharges_step_indices {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : (step.departureCharges.map (·.index)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  unfold Step.departureCharges
  apply List.Pairwise.filterMap
    (R := fun a b : Validator × Nat => a.2 ≠ b.2)
  · intro a b different c one d two
    dsimp only at one two
    split at one
    · cases one
    · split at one
      · cases Option.some.inj one
        split at two
        · cases two
        · split at two
          · cases Option.some.inj two
            exact different
          · cases two
      · cases one
  · have unique : (x.state.validators.data.toList.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' _
    exact List.pairwise_map.mp unique

/-- A run charges each registry index at most once. -/
theorem departureCharges_run_indices {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) : (tail.departureCharges.map (·.index)).Nodup := by
  induction tail with
  | nil => simp [Run.departureCharges]
  | snoc pre step ih =>
    rw [Run.departureCharges, List.map_append, List.nodup_append]
    refine ⟨ih, departureCharges_step_indices step, ?_⟩
    intro i earlier j latest
    obtain ⟨one, oneMember, rfl⟩ := List.mem_map.mp earlier
    obtain ⟨two, twoMember, rfl⟩ := List.mem_map.mp latest
    obtain ⟨v, found, assigned, _⟩ := pre.departure_charge_exit one oneMember
    have single := (Run.nil.snoc step).departure_charge_ne_of_assigned
      one.index v found assigned two (by simpa [Run.departureCharges] using twoMember)
    exact Ne.symm single

/-- Calls carry the charged registry index, or no index for partial withdrawals.

A call with no index comes from a partial withdrawal request, and carries the entry it queues.

That entry holds the amount of the call, withdrawable from the epoch of the call plus the delay.
-/
structure IndexedDepartureCall (preset : Preset) (config : Config) where
  index : Option Nat
  call : DepartureQueueCall
  entry : Option PendingPartialWithdrawal
  tagged : index = none ↔ entry.isSome
  pushed : ∀ pending, entry = some pending → pending.amount = call.amount ∧
    pending.withdrawableEpoch.toNat =
      call.epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat

/-- Every call starts no earlier than the chosen epoch. -/
def DepartureCallsFrom (start : Nat) (calls : List (IndexedDepartureCall preset config)) :
    Prop :=
  ∀ called ∈ calls, start ≤ called.call.first.toNat

private theorem DepartureCallsFrom.mono {start later : Nat}
    {calls : List (IndexedDepartureCall preset config)}
    (firsts : DepartureCallsFrom later calls) (ordered : start ≤ later) :
    DepartureCallsFrom start calls := fun called member => ordered.trans (firsts called member)

private theorem DepartureCallsFrom.append {start : Nat}
    {first second : List (IndexedDepartureCall preset config)}
    (one : DepartureCallsFrom start first) (two : DepartureCallsFrom start second) :
    DepartureCallsFrom start (first ++ second) := by
  intro called member
  exact (List.mem_append.mp member).elim (one called) (two called)

/-- The calls append their entries, in order, to the queue of partial withdrawals. -/
private def PartialsAppended {fork : Fork} (electra : .pectra ≤ fork)
    (s t : BeaconState preset fork) (calls : List (IndexedDepartureCall preset config)) : Prop :=
  (t.pendingPartialWithdrawals electra).data.toList =
    (s.pendingPartialWithdrawals electra).data.toList ++ calls.filterMap (·.entry)

private theorem PartialsAppended.append {fork : Fork} {electra : .pectra ≤ fork}
    {s t u : BeaconState preset fork} {first second : List (IndexedDepartureCall preset config)}
    (one : PartialsAppended electra s t first) (two : PartialsAppended electra t u second) :
    PartialsAppended electra s u (first ++ second) := by
  rw [PartialsAppended, two, one, List.filterMap_append, List.append_assoc]

private theorem PartialsAppended.of_kept {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork}
    (kept : (t.pendingPartialWithdrawals electra).data =
      (s.pendingPartialWithdrawals electra).data) :
    PartialsAppended (config := config) electra s t [] := by
  rw [PartialsAppended, kept, List.filterMap_nil, List.append_nil]

private theorem PartialsAppended.kept_left {fork : Fork} {electra : .pectra ≤ fork}
    {s t u : BeaconState preset fork} {calls : List (IndexedDepartureCall preset config)}
    (kept : (t.pendingPartialWithdrawals electra).data = (s.pendingPartialWithdrawals electra).data)
    (two : PartialsAppended electra t u calls) : PartialsAppended electra s u calls := by
  rw [PartialsAppended, two, kept]

private theorem PartialsAppended.kept_right {fork : Fork} {electra : .pectra ≤ fork}
    {s t u : BeaconState preset fork} {calls : List (IndexedDepartureCall preset config)}
    (one : PartialsAppended electra s t calls)
    (kept : (u.pendingPartialWithdrawals electra).data =
      (t.pendingPartialWithdrawals electra).data) :
    PartialsAppended electra s u calls := by
  rw [PartialsAppended, kept, one]

/-- Every consolidation call takes its initial epoch and churn rate from a listed state. -/
def ConsolidationCallSites (preset : Preset) (config : Config)
    (calls : List (IndexedDepartureCall preset config)) (sites : List (ForkedBeaconState preset)) :
    Prop :=
  ∀ called ∈ calls, ∃ site ∈ sites,
    computeActivationExitEpoch preset (getCurrentEpoch site.state) = .ok called.call.first ∧
      getConsolidationChurnLimit config site.state = .ok called.call.rate

/-- Index uniqueness turns matching tagged calls into an injection of charges into calls. -/
private theorem departureCharges_inject {charges : List DepartureCharge}
    {calls : List (IndexedDepartureCall preset config)} (unique : (charges.map (·.index)).Nodup)
    (matched : ∀ charge ∈ charges, ∃ called ∈ calls,
      called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
      called.call.amount.toNat = charge.amount) :
    ∃ injection : Fin charges.length → Fin calls.length,
      Function.Injective injection ∧
      ∀ i, (calls[injection i]).index = some charges[i].index ∧
        (calls[injection i]).call.epoch.toNat = charges[i].epoch ∧
        (calls[injection i]).call.amount.toNat = charges[i].amount := by
  classical
  have position (i : Fin charges.length) : ∃ j : Fin calls.length,
      calls[j].index = some charges[i].index ∧
      calls[j].call.epoch.toNat = charges[i].epoch ∧
      calls[j].call.amount.toNat = charges[i].amount := by
    obtain ⟨called, member, index, epoch, amount⟩ := matched charges[i] (List.getElem_mem _)
    obtain ⟨j, inside, atIndex⟩ := List.getElem_of_mem member
    refine ⟨⟨j, inside⟩, ?_⟩
    change calls[j].index = _ ∧ calls[j].call.epoch.toNat = _ ∧ calls[j].call.amount.toNat = _
    rw [atIndex]
    exact ⟨index, epoch, amount⟩
  choose injection paired using position
  refine ⟨injection, ?_, paired⟩
  intro i j same
  have indices : charges[i].index = charges[j].index :=
    Option.some.inj ((paired i).1.symm.trans (same ▸ (paired j).1))
  apply Fin.ext
  exact unique.eq_of_getElem_eq (by simp) (by simp)
    (by simpa using indices)

/-- An injection preserving amounts and completion epochs bounds every filtered charge sum. -/
private theorem departureCharges_le_calls {charges : List DepartureCharge}
    {calls : List (IndexedDepartureCall preset config)} (unique : (charges.map (·.index)).Nodup)
    (matched : ∀ charge ∈ charges, ∃ called ∈ calls,
      called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
      called.call.amount.toNat = charge.amount) (high : Nat) :
    ((charges.filter fun c => c.epoch ≤ high).map (·.amount)).sum ≤
      ((calls.filter fun c => c.call.epoch.toNat ≤ high).map fun c => c.call.amount.toNat).sum := by
  classical
  obtain ⟨injection, injective, paired⟩ := departureCharges_inject unique matched
  have bound := Finset.sum_le_sum_of_injOn
    (f := fun i : Fin charges.length => if charges[i].epoch ≤ high then charges[i].amount else 0)
    (g := fun j : Fin calls.length =>
      if calls[j].call.epoch.toNat ≤ high then calls[j].call.amount.toNat else 0)
    (s := Finset.univ) (t := Finset.univ) injection
    (fun _ _ _ _ same => injective same) (by simp)
    (fun i _ => by rw [(paired i).2.1, (paired i).2.2])
    (fun _ _ _ => Nat.zero_le _)
  have sums {α : Type} (xs : List α) (epoch amount : α → Nat) :
      (∑ i : Fin xs.length, if epoch xs[i] ≤ high then amount xs[i] else 0) =
        ((xs.filter fun x => epoch x ≤ high).map amount).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn (fun i : Fin xs.length =>
      if epoch xs[i.val] ≤ high then amount xs[i.val] else 0)).sum = _
    rw [List.ofFn_getElem_eq_map xs (fun x => if epoch x ≤ high then amount x else 0)]
    simpa using List.sum_map_ite (fun x => epoch x ≤ high) amount (fun _ => 0) xs
  rw [sums charges (·.epoch) (·.amount),
    sums calls (fun c => c.call.epoch.toNat) (fun c => c.call.amount.toNat)] at bound
  exact bound

/-- A first call that opens a fresh queue epoch spends at most the cap per epoch from `start`. -/
private theorem DepartureQueueTrace.window_le_of_reset {call : DepartureQueueCall}
    {rest : List DepartureQueueCall} {epoch : Epoch} {left : Gwei}
    (tail : DepartureQueueTrace call.epoch call.left rest epoch left) (start high cap : Nat)
    (rates : ∀ c ∈ call :: rest, c.rate.toNat ≤ cap)
    (reset : call.earliest < max call.earliest call.first)
    (opened : start ≤ max call.earliest.toNat call.first.toNat) :
    (((call :: rest).filter fun c => c.epoch.toNat ≤ high).map fun c => c.amount.toNat).sum ≤
      (high + 1 - start) * cap := by
  have later := tail.window_le high cap (fun c member => rates c (List.mem_cons_of_mem _ member))
  by_cases inside : call.epoch.toNat ≤ high
  · obtain ⟨placed, spent, _⟩ := churnQueue_spend call.computed
    have placed := UInt64.le_iff_toNat_le.mp placed
    rw [ite_eq_left reset, Uint64.toNat_max] at spent
    rw [Uint64.toNat_max] at placed
    have one : call.left.toNat + call.amount.toNat ≤ (call.epoch.toNat + 1 - start) * cap := by
      calc
        _ = (call.epoch.toNat - max call.earliest.toNat call.first.toNat + 1) *
            call.rate.toNat := by rw [spent, Nat.add_mul, Nat.one_mul]; omega
        _ ≤ _ := Nat.mul_le_mul (by omega) (rates call (by simp))
    have distance : (call.epoch.toNat + 1 - start) + (high - call.epoch.toNat) =
        high + 1 - start := by omega
    have combined := Nat.add_le_add_right one ((high - call.epoch.toNat) * cap)
    rw [← Nat.add_mul, distance] at combined
    simp only [departureQueuePotential, inside, ↓reduceIte] at later
    simp only [List.filter_cons, decide_eq_true inside, ↓reduceIte,
      List.map_cons, List.sum_cons]
    omega
  · simp only [departureQueuePotential, inside, ↓reduceIte] at later
    simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
    omega

/-- A first-epoch bound discards capacity in idle epochs before the chosen window.

The capacity of each epoch counts only from the later of the start and the earliest open epoch. -/
private theorem DepartureQueueTrace.window_le_from {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left) (start high cap : Nat)
    (rates : ∀ call ∈ calls, call.rate.toNat ≤ cap)
    (firsts : ∀ call ∈ calls, start ≤ call.first.toNat) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map fun call => call.amount.toNat).sum ≤
      (if earliest.toNat ≤ high then available.toNat else 0) +
        (high + 1 - max start earliest.toNat) * cap := by
  cases trace with
  | nil => simp
  | cons call tail =>
    by_cases before : start ≤ call.earliest.toNat
    · have rest := tail.window_le high cap
        (fun c member => rates c (List.mem_cons_of_mem _ member))
      by_cases inside : call.epoch.toNat ≤ high
      · have initialInside := call.epoch_mono.trans inside
        have bound := (DepartureQueueTrace.cons call tail).window_le high cap rates
        have initial : departureQueuePotential high cap call.earliest call.available ≤
            (if call.earliest.toNat ≤ high then call.available.toNat else 0) +
              (high + 1 - max start call.earliest.toNat) * cap := by
          simp only [departureQueuePotential, initialInside, ↓reduceIte]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right cap (by omega)) _
        exact (Nat.le_add_right _ _).trans (bound.trans initial)
      · simp only [departureQueuePotential, inside, ↓reduceIte] at rest
        simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
        omega
    · have first := firsts call (by simp)
      have reset : call.earliest < max call.earliest call.first := by
        rw [UInt64.lt_iff_toNat_lt, Uint64.toNat_max]
        omega
      rw [Nat.max_eq_left (by omega : call.earliest.toNat ≤ start)]
      exact (tail.window_le_of_reset start high cap rates reset (by omega)).trans
        (Nat.le_add_left _ _)

/-- Tagged calls cover all newly assigned exits of existing registry entries. -/
private def DepartureCoverage {f h : Fork} (s : BeaconState preset f) (t : BeaconState preset h)
    (calls : List (IndexedDepartureCall preset config)) : Prop :=
  ∀ i old next, s.validators.data[i]? = some old → t.validators.data[i]? = some next →
    old.exitEpoch = FAR_FUTURE_EPOCH → next.exitEpoch ≠ FAR_FUTURE_EPOCH →
    ∃ called ∈ calls, called.index = some i ∧ called.call.epoch = next.exitEpoch ∧
      called.call.amount = old.effectiveBalance

/-- Accessor-level matching covers every existing index in a pre-Gloas registry. -/
private theorem DepartureCoverage.of_accessor {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {calls : List (IndexedDepartureCall preset config)}
    (early : f < .glamsterdam)
    (covered : ∀ other old next, getValidator s other = .ok old →
      getValidator t other = .ok next → old.exitEpoch = FAR_FUTURE_EPOCH →
      next.exitEpoch ≠ FAR_FUTURE_EPOCH → ∃ called ∈ calls,
        called.index = some other.toNat ∧ called.call.epoch = next.exitEpoch ∧
          called.call.amount = old.effectiveBalance) : DepartureCoverage s t calls := by
  intro i old next before after unset assigned
  have inside := (Array.getElem?_eq_some_iff.mp before).1
  have small : i < 2 ^ 64 := Nat.lt_trans inside
    (Nat.lt_of_le_of_lt (s.validators.bound early) (UInt64.toNat_lt _))
  have converted : i.toUInt64.toNat = i := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  have found : getValidator s i.toUInt64 = .ok old := by
    simp only [getValidator, converted, before]
  have read : getValidator t i.toUInt64 = .ok next := by
    simp only [getValidator, converted, after]
  simpa only [converted] using covered i.toUInt64 old next found read unset assigned

/-- Coverage composes while assigned epochs and pre-scheduling effective balances persist. -/
private theorem DepartureCoverage.append {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    {first second : List (IndexedDepartureCall preset config)}
    (one : DepartureCoverage s t first) (two : DepartureCoverage t u second)
    (lifeOne : RegistryLifecycle s t) (lifeTwo : RegistryLifecycle t u)
    (balances : ∀ (i : Nat) (old next : Validator), s.validators.data[i]? = some old →
      t.validators.data[i]? = some next → next.effectiveBalance = old.effectiveBalance) :
    DepartureCoverage s u (first ++ second) := by
  intro i old last before after unset assigned
  obtain ⟨middle, middleFound, _⟩ := lifeOne.validators i old before
  by_cases pending : middle.exitEpoch = FAR_FUTURE_EPOCH
  · obtain ⟨called, member, index, epoch, amount⟩ :=
      two i middle last middleFound after pending assigned
    exact ⟨called, List.mem_append_right _ member, index, epoch,
      amount.trans (balances i old middle before middleFound)⟩
  · obtain ⟨called, member, index, epoch, amount⟩ :=
      one i old middle before middleFound unset pending
    obtain ⟨later, laterFound, kept⟩ := lifeTwo.validators i middle middleFound
    have same := Option.some.inj (laterFound.symm.trans after)
    subst later
    exact ⟨called, List.mem_append_left _ member, index,
      epoch.trans (kept.exitEpoch pending).symm, amount⟩

/-- Effective-balance preservation supplies the balance premise of coverage composition. -/
private theorem DepartureCoverage.append_of_effectiveKept {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    {first second : List (IndexedDepartureCall preset config)}
    (one : DepartureCoverage s t first) (two : DepartureCoverage t u second)
    (lifeOne : RegistryLifecycle s t) (lifeTwo : RegistryLifecycle t u)
    (balances : ∀ i, i < s.validators.data.size →
      effectiveAt ⟨h, t⟩ i = effectiveAt ⟨f, s⟩ i) :
    DepartureCoverage s u (first ++ second) := by
  apply one.append two lifeOne lifeTwo
  intro i old next before after
  have kept := balances i (Array.getElem?_eq_some_iff.mp before).1
  apply UInt64.toNat_inj.mp
  simpa only [effectiveAt, before, after, Option.map_some, Option.getD_some] using kept

/-- An operation that preserves exit epochs generates no departure charge. -/
private theorem DepartureCoverage.of_exit_epochs {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h}
    (epochs : ∀ (i : Nat) (old next : Validator), s.validators.data[i]? = some old →
      t.validators.data[i]? = some next → next.exitEpoch = old.exitEpoch) :
    DepartureCoverage (config := config) s t [] := by
  intro i old next before after unset assigned
  exact False.elim (assigned ((epochs i old next before after).trans unset))

/-- An unchanged registry needs no departure call. -/
private theorem DepartureCoverage.of_data {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data) :
    DepartureCoverage (config := config) s t [] := by
  apply DepartureCoverage.of_exit_epochs
  intro i old next before after
  rw [same, before] at after
  cases Option.some.inj after
  rfl

/-- Appending validators preserves the exit epochs of all existing entries. -/
private theorem DepartureCoverage.of_append {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {added : Array Validator}
    (same : t.validators.data = s.validators.data ++ added) :
    DepartureCoverage (config := config) s t [] := by
  apply DepartureCoverage.of_exit_epochs
  intro i old next before after
  have inside := (Array.getElem?_eq_some_iff.mp before).1
  rw [same, Array.getElem?_append_left inside, before] at after
  cases Option.some.inj after
  rfl

/-- Replacing one validator without changing its exit epoch creates no departure. -/
private theorem DepartureCoverage.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {position : Nat} {old next : Validator}
    (found : getValidatorAt s position = .ok old)
    (set : s.setValidatorAt position next = .ok t) (epoch : next.exitEpoch = old.exitEpoch) :
    DepartureCoverage (config := config) s t [] := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  apply DepartureCoverage.of_exit_epochs
  intro i before after read written
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at written
  split at written
  · rename_i same
    subst i
    have oldSame := Option.some.inj ((getValidatorAt_eq_ok_iff.mp found).symm.trans read)
    have nextSame := Option.some.inj written
    subst before after
    exact epoch
  · have same := Option.some.inj (read.symm.trans written)
    subst after
    rfl

/-- A suffix preserving exit epochs keeps coverage without requiring unchanged balances. -/
private theorem DepartureCoverage.suffix {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    {calls : List (IndexedDepartureCall preset config)}
    (covered : DepartureCoverage s t calls) (life : RegistryLifecycle s t)
    (epochs : ∀ (i : Nat) (old next : Validator), t.validators.data[i]? = some old →
      u.validators.data[i]? = some next → next.exitEpoch = old.exitEpoch) :
    DepartureCoverage s u calls := by
  intro i old last before after unset assigned
  obtain ⟨middle, middleFound, _⟩ := life.validators i old before
  have same := epochs i middle last middleFound after
  obtain ⟨called, member, index, epoch, amount⟩ :=
    covered i old middle before middleFound unset (same ▸ assigned)
  exact ⟨called, member, index, epoch.trans same.symm, amount⟩

/-- An uncharged suffix preserves earlier coverage even when effective balances change. -/
private theorem DepartureCoverage.suffix_of_empty {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    {calls : List (IndexedDepartureCall preset config)}
    (covered : DepartureCoverage s t calls) (empty : DepartureCoverage (config := config) t u [])
    (lifeOne : RegistryLifecycle s t) (lifeTwo : RegistryLifecycle t u) :
    DepartureCoverage s u calls := by
  apply covered.suffix lifeOne
  intro i old next before after
  by_cases pending : old.exitEpoch = FAR_FUTURE_EPOCH
  · by_cases assigned : next.exitEpoch = FAR_FUTURE_EPOCH
    · exact assigned.trans pending.symm
    · obtain ⟨_, member, _⟩ := empty i old next before after pending assigned
      cases member
  · obtain ⟨later, found, kept⟩ := lifeTwo.validators i old before
    have same := Option.some.inj (found.symm.trans after)
    subst later
    exact kept.exitEpoch pending

/-- A fold of operations assigning no exits needs no effective-balance preservation. -/
private theorem DepartureCoverage.empty_fold {f : Fork} {α ε : Type}
    {operation : BeaconState preset f → α → Except ε (BeaconState preset f)}
    (empty : ∀ a item b, operation a item = .ok b → DepartureCoverage (config := config) a b [])
    (life : ∀ a item b, operation a item = .ok b → RegistryLifecycle a b)
    {s t : BeaconState preset f} {items : List α}
    (ok : items.foldlM operation s = .ok t) : DepartureCoverage (config := config) s t [] := by
  have result := foldlM_ok_invariant
    (fun t => DepartureCoverage (config := config) s t [] ∧ RegistryLifecycle s t)
    (fun a item b before stepped =>
      ⟨before.1.suffix_of_empty (empty a item b stepped) before.2 (life a item b stepped),
        before.2.trans (life a item b stepped)⟩)
    ⟨DepartureCoverage.of_data rfl, .refl s⟩ ok
  exact result.1

/-- A fold composes concrete calls when each operation preserves pre-scheduling balances.

The local traces hold at the states that satisfy an invariant, which the operations keep. -/
private theorem DepartureCoverage.foldlM {f : Fork} {α ε : Type}
    {operation : BeaconState preset f → α → Except ε (BeaconState preset f)}
    (electra : .pectra ≤ f) (cap : Nat) (good : BeaconState preset f → Prop)
    (localTrace : ∀ s item t, operation s item = .ok t → good s →
      ∃ calls : List (IndexedDepartureCall preset config),
        DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
        DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
          (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
        DepartureCoverage s t calls ∧ (∀ called ∈ calls, called.call.rate.toNat ≤ cap) ∧
        PartialsAppended electra s t calls)
    (keep : ∀ s item t, operation s item = .ok t → good s → good t)
    (lifecycle : ∀ s item t, operation s item = .ok t → RegistryLifecycle s t)
    (effective : ∀ s item t, operation s item = .ok t →
      ∀ i, i < s.validators.data.size → effectiveAt ⟨f, t⟩ i = effectiveAt ⟨f, s⟩ i)
    (slots : ∀ s item t, operation s item = .ok t → t.slot = s.slot)
    {items : List α} {s t : BeaconState preset f} (start : good s)
    (ok : items.foldlM operation s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls, called.call.rate.toNat ≤ cap) ∧
      PartialsAppended electra s t calls := by
  induction items generalizing s with
  | nil =>
    cases ok
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, DepartureCoverage.of_data rfl, by simp,
      .of_kept rfl⟩
  | cons item items ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, stepped, rest⟩ := ok
    obtain ⟨first, firstFrom, firstTrace, firstCoverage, firstRates, firstAppended⟩ :=
      localTrace s item middle stepped start
    obtain ⟨later, laterFrom, laterTrace, laterCoverage, laterRates, laterAppended⟩ :=
      ih (keep s item middle stepped start) rest
    have epoch : getCurrentEpoch middle = getCurrentEpoch s := by
      simp only [getCurrentEpoch, slots _ _ _ stepped]
    rw [epoch] at laterFrom
    refine ⟨first ++ later, firstFrom.append laterFrom, ?_, ?_, ?_,
      firstAppended.append laterAppended⟩
    · rw [List.map_append]
      have append {a b c : Epoch} {x y z : Gwei} {xs ys : List DepartureQueueCall}
          (one : DepartureQueueTrace a x xs b y) (two : DepartureQueueTrace b y ys c z) :
          DepartureQueueTrace a x (xs ++ ys) c z := by
        induction one with
        | nil => exact two
        | cons call tail ih => exact .cons call (ih two)
      exact append firstTrace laterTrace
    · exact firstCoverage.append_of_effectiveKept laterCoverage (lifecycle _ _ _ stepped)
        (RegistryLifecycle.foldlM lifecycle rest) (effective _ _ _ stepped)
    · intro called member
      exact (List.mem_append.mp member).elim (firstRates called) (laterRates called)

/-- Registry coverage supplies the matching premise for every charge of a concrete step. -/
private theorem DepartureCoverage.step_charges {x y : ForkedBeaconState preset}
    (step : Step config checks x y) {calls : List (IndexedDepartureCall preset config)}
    (covered : DepartureCoverage x.state y.state calls) :
    ∀ charge ∈ step.departureCharges, ∃ called ∈ calls,
      called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
        called.call.amount.toNat = charge.amount := by
  intro charge member
  obtain ⟨⟨old, i⟩, before, produced⟩ := List.mem_filterMap.mp member
  have found : x.state.validators.data[i]? = some old := by
    simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using before
  dsimp only at produced
  split at produced
  · cases produced
  · rename_i next after
    split at produced
    · rename_i assigned
      have conditions : old.exitEpoch = FAR_FUTURE_EPOCH ∧
          next.exitEpoch ≠ FAR_FUTURE_EPOCH := by simpa using assigned
      cases Option.some.inj produced
      obtain ⟨called, member, index, epoch, amount⟩ :=
        covered i old next found after conditions.1 conditions.2
      exact ⟨called, member, index, congrArg UInt64.toNat epoch, congrArg UInt64.toNat amount⟩
    · cases produced

/-- An exit scheduling operation supplies a call with exactly its input and output queues. -/
private theorem exitQueueCall_of_computed {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {amount : Gwei} {epoch : Epoch}
    (ok : computeExitEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ call : DepartureQueueCall,
      call.earliest = s.earliestExitEpoch electra ∧
      call.available = s.exitBalanceToConsume electra ∧
      call.amount = amount ∧ call.epoch = epoch ∧
      call.left = t.exitBalanceToConsume electra ∧
      exitChurnLimit config s = .ok call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨first, firstOk, rate, rateOk, ⟨placed, left⟩, queued, rfl, rfl⟩ := ok
  exact ⟨⟨_, _, first, rate, amount, placed, left, queued⟩,
    rfl, rfl, rfl, rfl, rfl, rateOk, firstOk⟩

/-- A consolidation scheduling operation supplies its exact balance-queue call. -/
private theorem consolidationQueueCall_of_computed {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {amount : Gwei} {epoch : Epoch}
    (ok : computeConsolidationEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ call : DepartureQueueCall,
      call.earliest = s.earliestConsolidationEpoch electra ∧
      call.available = s.consolidationBalanceToConsume electra ∧
      call.amount = amount ∧ call.epoch = epoch ∧
      call.left = t.consolidationBalanceToConsume electra ∧
      getConsolidationChurnLimit config s = .ok call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨first, firstOk, rate, rateOk, ⟨placed, left⟩, queued, rfl, rfl⟩ := ok
  exact ⟨⟨_, _, first, rate, amount, placed, left, queued⟩,
    rfl, rfl, rfl, rfl, rfl, rateOk, firstOk⟩

/-- An initiated exit spends its old effective balance and retains the assigned queue epoch. -/
private theorem initiateExit_call {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) :
    t = s ∨ ∃ (v : Validator) (call : DepartureQueueCall),
      getValidator s index = .ok v ∧ v.exitEpoch = FAR_FUTURE_EPOCH ∧
      call.amount = v.effectiveBalance ∧
      call.earliest = s.earliestExitEpoch electra ∧
      call.available = s.exitBalanceToConsume electra ∧
      call.epoch = t.earliestExitEpoch electra ∧
      call.left = t.exitBalanceToConsume electra ∧
      exitChurnLimit config s = .ok call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first ∧
      ∃ next, getValidator t index = .ok next ∧ next.exitEpoch = call.epoch := by
  obtain ⟨v, found, unchanged | ⟨far, queued, epoch, withdrawable, scheduled, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact .inl unchanged.2
  · have called : computeExitEpochAndUpdateChurn config s electra v.effectiveBalance =
        .ok (queued, epoch) := by simpa only [exitQueue, electra, ↓reduceDIte] using scheduled
    obtain ⟨call, earliest, available, amount, placed, left, rate, firstOk⟩ :=
      exitQueueCall_of_computed electra called
    have queuedEpoch := (computeExitEpochAndUpdateChurn_earliest called).1
    have read := getValidator_setValidator_self set
    obtain ⟨inside, rfl⟩ := setValidator_ok set
    exact .inr ⟨v, call, found, far, amount, earliest, available,
      placed.trans queuedEpoch.symm, left, rate, firstOk, _, read, placed.symm⟩

/-- Initiating an exit leaves every other registry entry unchanged. -/
private theorem initiateExit_other {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index other : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) (different : other ≠ index) :
    getValidator t other = getValidator s other := by
  obtain ⟨v, _, unchanged | ⟨_, queued, epoch, _, scheduled, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]
  · have called : computeExitEpochAndUpdateChurn config s electra v.effectiveBalance =
        .ok (queued, epoch) := by simpa only [exitQueue, electra, ↓reduceDIte] using scheduled
    rw [getValidator_setValidator_of_ne set different]
    exact getValidator_of_validators_eq (computeExitEpochAndUpdateChurn_earliest called).2.1 _

/-- A newly assigned exit identifies the unique registry entry charged by its call. -/
private theorem initiateExit_charge {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index other : ValidatorIndex} {old next : Validator}
    (ok : initiateValidatorExit config s index = .ok t)
    (before : getValidator s other = .ok old) (after : getValidator t other = .ok next)
    (unset : old.exitEpoch = FAR_FUTURE_EPOCH) (assigned : next.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    other = index ∧ ∃ call : DepartureQueueCall,
      call.amount = old.effectiveBalance ∧ call.epoch = next.exitEpoch ∧
      call.earliest = s.earliestExitEpoch electra ∧
      call.available = s.exitBalanceToConsume electra ∧
      call.epoch = t.earliestExitEpoch electra ∧
      call.left = t.exitBalanceToConsume electra ∧
      exitChurnLimit config s = .ok call.rate := by
  have differentStates : t ≠ s := by
    intro same
    subst t
    have equal := Except.ok.inj (before.symm.trans after)
    exact assigned (equal ▸ unset)
  have sameIndex : other = index := by
    by_contra different
    have unchanged := initiateExit_other electra ok different
    have equal := Except.ok.inj (before.symm.trans (unchanged ▸ after))
    exact assigned (equal ▸ unset)
  subst other
  obtain same | ⟨v, call, found, _, amount, earliest, available, placed, left, rate,
    _, later, read, epoch⟩ := initiateExit_call electra ok
  · exact False.elim (differentStates same)
  · have oldSame := Except.ok.inj (found.symm.trans before)
    have nextSame := Except.ok.inj (read.symm.trans after)
    subst v later
    exact ⟨rfl, call, amount, epoch.symm, earliest, available, placed, left, rate⟩

/-- Partial withdrawals may spend exit capacity while leaving every validator unchanged.

A request that spends it queues the amount of its call, from the epoch of the call plus the delay.
-/
private theorem partialWithdrawal_call {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    t.validators = s.validators ∧
      (t = s ∨ ∃ call : DepartureQueueCall,
        call.earliest = s.earliestExitEpoch electra ∧
        call.available = s.exitBalanceToConsume electra ∧
        call.epoch = t.earliestExitEpoch electra ∧
        call.left = t.exitBalanceToConsume electra ∧
        exitChurnLimit config s = .ok call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first ∧
        ∃ withdrawable : Epoch, (t.pendingPartialWithdrawals electra).data =
            (s.pendingPartialWithdrawals electra).data.push ⟨index, call.amount, withdrawable⟩ ∧
          withdrawable.toNat =
            call.epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨balance, _, kept, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨queued, epoch⟩, called, withdrawable, delayed, pending, appended, rfl⟩ := ok
    obtain ⟨call, earliest, available, amountEq, placed, left, rate, firstOk⟩ :=
      exitQueueCall_of_computed electra called
    obtain ⟨queuedEpoch, registry, _⟩ := computeExitEpochAndUpdateChurn_earliest called
    -- The churn call changes only the exit queue, so the request appends to the old queue.
    have queue : queued.pendingPartialWithdrawals = s.pendingPartialWithdrawals := by
      simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at called
      obtain ⟨_, _, _, _, _, _, rfl, -⟩ := called
      rfl
    have sum := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp delayed)).2
    refine ⟨registry, .inr ⟨call, earliest, available, placed.trans queuedEpoch.symm,
      left, rate, firstOk, withdrawable, ?_, by rw [sum, ← placed]⟩⟩
    rw [amountEq]
    change pending.data = _
    rw [appendWithinLimit_data appended, queue]
  · cases ok
    exact ⟨rfl, .inl rfl⟩

/-- Scheduling a consolidation spends the source balance before changing its exit epoch. -/
private theorem queueConsolidation_call {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    ∃ call : DepartureQueueCall,
      call.amount = source.effectiveBalance ∧
      call.earliest = s.earliestConsolidationEpoch electra ∧
      call.available = s.consolidationBalanceToConsume electra ∧
      call.epoch = t.earliestConsolidationEpoch electra ∧
      call.left = t.consolidationBalanceToConsume electra ∧
      getConsolidationChurnLimit config s = .ok call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first ∧
      ∃ next, getValidator t sourceIndex = .ok next ∧ next.exitEpoch = call.epoch := by
  obtain ⟨_, _, _, _, _, called, _, set, _, rfl⟩ := queueConsolidation_steps ok
  obtain ⟨call, earliest, available, amount, placed, left, rate, firstOk⟩ :=
    consolidationQueueCall_of_computed electra called
  have queuedEpoch := (computeConsolidationEpochAndUpdateChurn_earliest called).1
  have read := getValidator_setValidator_self set
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  exact ⟨call, amount, earliest, available, placed.trans queuedEpoch.symm, left,
    rate, firstOk, _, read, placed.symm⟩

/-- Consolidation scheduling leaves registry entries other than its source unchanged. -/
private theorem queueConsolidation_other {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex other : ValidatorIndex}
    {source : Validator}
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t)
    (different : other ≠ sourceIndex) : getValidator t other = getValidator s other := by
  obtain ⟨_, _, _, changed, _, _, _, set, _, rfl⟩ := queueConsolidation_steps ok
  have kept := getValidator_setValidator_of_ne set different
  exact kept

/-- A consolidation charge comes from its unique source and uses that source's old balance. -/
private theorem queueConsolidation_charge {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex other : ValidatorIndex}
    {source old next : Validator}
    (sourceFound : getValidator s sourceIndex = .ok source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t)
    (before : getValidator s other = .ok old) (after : getValidator t other = .ok next)
    (unset : old.exitEpoch = FAR_FUTURE_EPOCH) (assigned : next.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    other = sourceIndex ∧ ∃ call : DepartureQueueCall,
      call.amount = old.effectiveBalance ∧ call.epoch = next.exitEpoch ∧
      call.earliest = s.earliestConsolidationEpoch electra ∧
      call.available = s.consolidationBalanceToConsume electra ∧
      call.epoch = t.earliestConsolidationEpoch electra ∧
      call.left = t.consolidationBalanceToConsume electra ∧
      getConsolidationChurnLimit config s = .ok call.rate := by
  have sameIndex : other = sourceIndex := by
    by_contra different
    have unchanged := queueConsolidation_other electra ok different
    have equal := Except.ok.inj (before.symm.trans (unchanged ▸ after))
    exact assigned (equal ▸ unset)
  subst other
  have sourceSame := Except.ok.inj (sourceFound.symm.trans before)
  subst source
  obtain ⟨call, amount, earliest, available, placed, left, rate, _, later, read, epoch⟩ :=
    queueConsolidation_call electra ok
  have nextSame := Except.ok.inj (read.symm.trans after)
  subst later
  exact ⟨rfl, call, amount, epoch.symm, earliest, available, placed, left, rate⟩

private theorem queueConsolidation_indexedTrace_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (sourceFound : getValidator s sourceIndex = .ok source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    ∃ called : IndexedDepartureCall preset config,
      (getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ called.call.first.toNat ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) [called.call]
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      getConsolidationChurnLimit config s = .ok called.call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first ∧
      called.entry = none ∧
      ∀ other old next, getValidator s other = .ok old → getValidator t other = .ok next →
        old.exitEpoch = FAR_FUTURE_EPOCH → next.exitEpoch ≠ FAR_FUTURE_EPOCH →
        called.index = some other.toNat ∧ called.call.epoch = next.exitEpoch ∧
          called.call.amount = old.effectiveBalance := by
  obtain ⟨call, amount, earliest, available, placed, left, rate, firstOk, later, read, epoch⟩ :=
    queueConsolidation_call electra ok
  refine ⟨⟨some sourceIndex.toNat, call, none, by simp, nofun⟩, ?_, ?_, rate, firstOk, rfl, ?_⟩
  · have first := (computeActivationExitEpoch_ok_iff.mp firstOk).2
    dsimp only
    omega
  · change DepartureQueueTrace _ _ [call] _ _
    rw [← earliest, ← available, ← placed, ← left]
    exact .cons call (.nil _ _)
  · intro other old next before after unset assigned
    have sameIndex :=
      (queueConsolidation_charge electra sourceFound ok before after unset assigned).1
    subst other
    have oldSame := Except.ok.inj (sourceFound.symm.trans before)
    have nextSame := Except.ok.inj (read.symm.trans after)
    subst old next
    exact ⟨rfl, epoch.symm, amount⟩

/-- Deposits append validators or change balances, without assigning existing validators exits. -/
private theorem deposit_coverage {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    DepartureCoverage (config := config) s t [] := by
  obtain ⟨_, _, _, _, credited⟩ := processDeposit_ok ok
  have applyCoverage {a b : BeaconState preset fork} {key credentials amount signature}
      (applied : applyDeposit config checks a key credentials amount signature = .ok b) :
      DepartureCoverage (config := config) a b [] := by
    rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | admitted, rfl⟩ | ⟨early, _⟩
    · exact DepartureCoverage.of_data rfl
    · exact DepartureCoverage.of_data rfl
    · apply DepartureCoverage.of_append
      simpa only [Array.push_eq_append] using addValidatorToRegistry_validators_eq_push admitted
    · exact absurd electra (Nat.not_le_of_lt early)
  exact (applyCoverage credited :)

/-- A withdrawal-credential change assigns no exit epoch. -/
private theorem credentials_coverage {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    DepartureCoverage (config := config) s t [] := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  exact DepartureCoverage.setValidatorAt found set rfl

/-- The effective-balance pass assigns no exits and therefore preserves earlier charge amounts. -/
private theorem effectiveBalances_coverage {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) :
    DepartureCoverage (config := config) s t [] := by
  apply DepartureCoverage.empty_fold ?_ ?_ ok
  · intro a index b stepped
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at stepped
    obtain ⟨_, found, _, _, _, _, set⟩ := stepped
    exact DepartureCoverage.setValidatorAt found set rfl
  · intro a index b stepped
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at stepped
    obtain ⟨_, found, _, _, _, _, set⟩ := stepped
    exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩

/-- Crediting a pending deposit does not assign an exit to an existing validator. -/
private theorem pendingDeposit_coverage {fork : Fork} {s t : BeaconState preset fork}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    DepartureCoverage (config := config) s t [] := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact DepartureCoverage.of_data rfl
  · exact DepartureCoverage.of_data (congrArg (·.data) (increaseBalance_validators raised))
  · apply DepartureCoverage.of_append
    simpa only [Array.push_eq_append] using addValidatorToRegistry_validators_eq_push added

/-- Pending deposits assign no exits, independently of pending-source provenance. -/
private theorem pendingDeposits_coverage {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks s electra = .ok t) :
    DepartureCoverage (config := config) s t [] := by
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result →
            DepartureCoverage (config := config) state result.1.state [] := fun ok =>
    -- The lifecycle of the registry carries the empty coverage across each deposit.
    (passPendingDeposits_of
      (fun s t => DepartureCoverage (config := config) s t [] ∧ RegistryLifecycle s t)
      (fun _ => ⟨.of_data rfl, .refl _⟩)
      (fun one two => ⟨one.1.suffix_of_empty two.1 one.2 two.2, one.2.trans two.2⟩)
      (fun credited => ⟨pendingDeposit_coverage credited,
        registryLifecycle_applyPendingDeposit credited⟩) ok).1
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact (pass ‹_› :)

private theorem preActivation_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : queuePreActivation s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, setBalance, _, setValidator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setValidator_ok setValidator
  obtain ⟨_, rfl⟩ := setBalance_ok setBalance
  rfl

private theorem compoundingExcess_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : Nat}
    (ok : queueCompoundingExcess s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold queueCompoundingExcess at ok
  split at ok
  · split at ok
    · exact queueExcess_departureQueues electra (liftAccessor_ok.mp ok)
    · cases ok; rfl
  · cases ok; rfl

/-- The Electra upgrade sets both departure queues and an empty queue of partial withdrawals.

Its two folds keep all five fields. -/
private theorem electra_departure_initialization {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    ∃ first exitEpoch exitRate consolidationRate,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      Uint64.addChecked (s.validators.data.foldl (init := first) fun latest validator =>
        if validator.exitEpoch = FAR_FUTURE_EPOCH then latest else max latest validator.exitEpoch)
        1 = .ok exitEpoch ∧
      departureQueues (by decide) t = (exitEpoch, exitRate, first, consolidationRate, #[]) := by
  simp only [upgradeToElectra, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at ok
  obtain ⟨first, firstOk, exitEpoch, exitOk, exitRate, _, consolidationRate, _, middle,
    queued, compounded⟩ := ok
  have one := foldlM_ok_invariant
    (fun u => departureQueues (by decide) u = (exitEpoch, exitRate, first, consolidationRate, #[]))
    (fun a i b kept step => (preActivation_departureQueues (by decide) step).trans kept)
    rfl queued
  have two := foldlM_ok_invariant
    (fun u => departureQueues (by decide) u = (exitEpoch, exitRate, first, consolidationRate, #[]))
    (fun a i b kept step => (compoundingExcess_departureQueues (by decide) step).trans kept)
    one compounded
  exact ⟨first, exitEpoch, exitRate, consolidationRate, firstOk, exitOk, two⟩

/-- Both initialized departure queues open strictly after the crossing epoch. -/
private theorem electra_departure_epochs {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    (getCurrentEpoch s).toNat < (t.earliestExitEpoch (by decide)).toNat ∧
    (getCurrentEpoch s).toNat < (t.earliestConsolidationEpoch (by decide)).toNat := by
  obtain ⟨first, exitEpoch, exitRate, consolidationRate, firstOk, exitOk, queues⟩ :=
    electra_departure_initialization ok
  have firstEq := (computeActivationExitEpoch_ok_iff.mp firstOk).2
  have latest : ∀ (vs : List Validator) (start : Epoch),
      start.toNat ≤ (vs.foldl (fun latest validator =>
        if validator.exitEpoch = FAR_FUTURE_EPOCH then latest else max latest validator.exitEpoch)
        start).toNat := by
    intro vs
    induction vs with
    | nil => intro start; exact Nat.le_refl _
    | cons v rest ih =>
      intro start
      have restLe := ih (if v.exitEpoch = FAR_FUTURE_EPOCH then start
        else max start v.exitEpoch)
      simp only [List.foldl_cons]
      apply Nat.le_trans _ restLe
      split
      · exact Nat.le_refl _
      · rw [Uint64.toNat_max]; exact Nat.le_max_left _ _
  have bound := latest s.validators.data.toList first
  rw [Array.foldl_toList] at bound
  have exitEq := (Uint64.addChecked_ok_iff.mp exitOk).2
  have exitField := congrArg Prod.fst queues
  have consolidationField := congrArg (fun q => q.2.2.1) queues
  change t.earliestExitEpoch (by decide) = exitEpoch at exitField
  change t.earliestConsolidationEpoch (by decide) = first at consolidationField
  rw [exitField, consolidationField]
  simp only [UInt64.reduceToNat] at exitEq
  have firstBefore : (getCurrentEpoch s).toNat < first.toNat := by omega
  refine ⟨firstBefore.trans_le ?_, firstBefore⟩
  rw [exitEq]
  exact bound.trans (Nat.le_add_right _ _)

/-- Processing pending transfers never replenishes either departure queue. -/
private theorem processPendingConsolidations_departureQueues {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    (ok : processPendingConsolidations s electra = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [processPendingConsolidations, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨epoch, _, ⟨passed, read⟩, processed, rfl⟩ := ok
  exact passPendingConsolidations_departureQueues electra processed

private theorem inactivity_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {altair : .altair ≤ fork}
    (ok : processInactivityUpdates config s altair = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold processInactivityUpdates at ok
  split at ok
  · cases ok; rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    rfl

/-- Before Gloas, every epoch stage except registry updates keeps both departure queues. -/
private theorem epochStage_departureQueues {fork : Fork} {stage : EpochStage}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (edge : EpochStage.Edge config checks stage s t) (other : stage ≠ .registry) :
    departureQueues electra t = departureQueues electra s := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  cases stage <;> simp only [EpochStage.Edge, electra, notGloas, capella, altair,
    ↓reduceDIte] at edge
  case registry => exact absurd rfl other
  case justification => exact justification_departureQueues electra edge
  case inactivity => exact inactivity_departureQueues electra edge
  case rewards => exact rewards_departureQueues electra edge
  case slashings => exact slashingPenalties_departureQueues electra edge
  case eth1Reset =>
    split at edge
    · unfold processEth1DataReset at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals rfl
    · exact edge ▸ rfl
  case pendingDeposits => exact pendingDeposits_departureQueues electra edge
  case pendingConsolidations => exact processPendingConsolidations_departureQueues electra edge
  case effectiveBalances => exact effectiveBalances_departureQueues electra edge
  case slashingsReset =>
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq edge
    rfl
  case randaoReset =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq edge
    rfl
  case history =>
    unfold processHistoricalSummariesUpdate at edge
    simp only [bind, Except.bind, pure, Except.pure] at edge
    repeat' (split at edge <;> try cases edge)
    all_goals rfl
  case participation =>
    subst edge
    rfl
  case syncCommittees =>
    unfold processSyncCommitteeUpdates at edge
    simp only [bind, Except.bind, pure, Except.pure] at edge
    repeat' (split at edge <;> try cases edge)
    all_goals rfl
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      rfl
    · exact edge ▸ rfl
  all_goals exact edge ▸ rfl

/-- Every epoch stage except registry updates assigns no exit and keeps the registry entries. -/
private theorem epochStage_coverage {fork : Fork} {stage : EpochStage}
    {s t : BeaconState preset fork} (edge : EpochStage.Edge config checks stage s t)
    (other : stage ≠ .registry) :
    DepartureCoverage (config := config) s t [] ∧ RegistryLifecycle s t := by
  cases stage
  case registry => exact absurd rfl other
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact ⟨pendingDeposits_coverage edge, registryLifecycle_processPendingDeposits edge⟩
    · exact edge ▸ ⟨.of_data rfl, .refl _⟩
  case effectiveBalances =>
    exact ⟨effectiveBalances_coverage edge, registryLifecycle_processEffectiveBalanceUpdates edge⟩
  all_goals
    have same := congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩)
    exact ⟨.of_data same, .of_data same⟩

/-- A registry update either preserves both queues or executes an ejection's exit call. -/
private theorem registryEntry_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {activation : Epoch} {index : Nat}
    (ok : updateRegistryEntryElectra config activation s index = .ok t) :
    departureQueues electra t = departureQueues electra s ∨
      ∃ validatorIndex, initiateValidatorExit config s validatorIndex = .ok t := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨epoch, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact .inl rfl
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨validatorIndex, _, exited⟩ := ok
      exact .inr ⟨validatorIndex, exited⟩
    · split at ok
      · obtain ⟨_, rfl⟩ := setValidatorAt_ok (liftAccessor_ok.mp ok)
        exact .inl rfl
      · cases ok
        exact .inl rfl

/-- Before Gloas every successful exit rate is bounded by the configured shared cap. -/
private theorem exitChurnLimit_le_cap {fork : Fork} {s : BeaconState preset fork} {rate : Gwei}
    (early : fork < .glamsterdam) (ok : exitChurnLimit config s = .ok rate) :
    rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [exitChurnLimit, notGloas, ↓reduceIte, getActivationExitChurnLimit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨whole, _, rfl⟩ := ok
  exact UInt64.le_iff_toNat_le.mp Std.min_le_left

/-- The exit churn limit of a state is at most a bound, whenever it is computed. -/
private def ExitRateBelow (config : Config) {fork : Fork} (exitCap : Nat)
    (s : BeaconState preset fork) : Prop :=
  ∀ rate : Gwei, exitChurnLimit config s = .ok rate → rate.toNat ≤ exitCap

/-- Before Gloas, every state keeps its exit churn limit below the shared cap. -/
private theorem ExitRateBelow.of_max {fork : Fork} (early : fork < .glamsterdam)
    (s : BeaconState preset fork) :
    ExitRateBelow config config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat s :=
  fun _ ok => exitChurnLimit_le_cap early ok

private theorem exitUpdate_consolidationFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {amount : Gwei} {epoch : Epoch}
    (ok : computeExitEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨_, _, _, _, ⟨_, _⟩, _, rfl, _⟩ := ok
  rfl

private theorem initiateExit_consolidationFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  obtain ⟨v, _, unchanged | ⟨_, queued, epoch, _, scheduled, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]
  · have called : computeExitEpochAndUpdateChurn config s electra v.effectiveBalance =
        .ok (queued, epoch) := by simpa only [exitQueue, electra, ↓reduceDIte] using scheduled
    obtain ⟨_, rfl⟩ := setValidator_ok set
    change (departureQueues electra queued).2.2 = (departureQueues electra s).2.2
    exact exitUpdate_consolidationFrame electra called

/-- A partial withdrawal request keeps the registry and makes at most one untagged exit call.

The call reads the state's own exit churn and activation epoch. -/
private theorem partial_exit_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    t.validators = s.validators ∧ ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, called.index = none ∧
        exitChurnLimit config s = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first := by
  obtain ⟨registry, same | ⟨call, earliest, available, placed, left, rate, firstOk,
    withdrawable, appended, delayed⟩⟩ := partialWithdrawal_call electra ok
  · subst t
    exact ⟨rfl, [], .nil _ _, .of_kept rfl, by simp⟩
  · refine ⟨registry, [⟨none, call, some ⟨index, call.amount, withdrawable⟩, by simp,
      fun pending same => by cases same; exact ⟨rfl, delayed⟩⟩], ?_, ?_, ?_⟩
    · change DepartureQueueTrace _ _ [call] _ _
      rw [← earliest, ← available, ← placed, ← left]
      exact .cons call (.nil _ _)
    · rw [PartialsAppended, appended, Array.toList_push]
      rfl
    · intro called member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl, rate, firstOk⟩

/-- An exit makes at most one call, tagged with the exiting validator.

The call reads the state's own exit churn and activation epoch. -/
private theorem initiate_exit_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      PartialsAppended electra s t calls ∧
      (∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first) ∧
      ∀ other old next, getValidator s other = .ok old → getValidator t other = .ok next →
        old.exitEpoch = FAR_FUTURE_EPOCH → next.exitEpoch ≠ FAR_FUTURE_EPOCH →
        ∃ called ∈ calls, called.index = some other.toNat ∧
          called.call.epoch = next.exitEpoch ∧ called.call.amount = old.effectiveBalance := by
  have kept : (t.pendingPartialWithdrawals electra).data =
      (s.pendingPartialWithdrawals electra).data :=
    congrArg (fun q => q.2.2) (initiateExit_consolidationFrame electra ok)
  obtain same | ⟨v, call, found, _, amount, earliest, available, placed, left, rate,
    firstOk, later, read, epoch⟩ := initiateExit_call electra ok
  · subst t
    refine ⟨[], .nil _ _, .of_kept rfl, by simp, ?_⟩
    intro other old next before after unset assigned
    have equal := Except.ok.inj (before.symm.trans after)
    exact False.elim (assigned (equal ▸ unset))
  · refine ⟨[⟨some index.toNat, call, none, by simp, nofun⟩], ?_,
      by rw [PartialsAppended, kept]; simp, ?_, ?_⟩
    · change DepartureQueueTrace _ _ [call] _ _
      rw [← earliest, ← available, ← placed, ← left]
      exact .cons call (.nil _ _)
    · intro called member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rate, firstOk⟩
    · intro other old next before after unset assigned
      have sameIndex := (initiateExit_charge electra ok before after unset assigned).1
      subst other
      have oldSame := Except.ok.inj (found.symm.trans before)
      have nextSame := Except.ok.inj (read.symm.trans after)
      subst old next
      exact ⟨_, List.mem_singleton_self _, rfl, epoch.symm, amount⟩

/-- A registry entry update makes exit calls only through an ejection.

Each call reads the state's own exit churn and activation epoch. -/
private theorem registry_entry_exit_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {activation : Epoch} {index : Nat}
    (ok : updateRegistryEntryElectra config activation s index = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨epoch, _, set⟩ := ok
    have covered := DepartureCoverage.setValidatorAt (config := config) found set rfl
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact ⟨[], .nil _ _, covered, .of_kept rfl, by simp⟩
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validatorIndex, _, exited⟩ := ok
    obtain ⟨calls, trace, appended, sites, covered⟩ := initiate_exit_site electra exited
    exact ⟨calls, trace, DepartureCoverage.of_accessor early covered, appended, sites⟩
  split at ok
  · have set := liftAccessor_ok.mp ok
    have covered := DepartureCoverage.setValidatorAt (config := config) found set rfl
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact ⟨[], .nil _ _, covered, .of_kept rfl, by simp⟩
  · cases ok
    exact ⟨[], .nil _ _, DepartureCoverage.of_data rfl, .of_kept rfl, by simp⟩

/-- A slashing makes the exit calls of its exit, and covers the slashed validator.

Each call reads the state's own exit churn and activation epoch. -/
private theorem slashing_exit_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first := by
  obtain ⟨exited, validator, withdrawable, marked, _, _, _, _, _, _, _, last, exitedOk,
    found, _, markedOk, _, _, _, lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  obtain ⟨calls, trace, appended, sites, covered⟩ := initiate_exit_site electra exitedOk
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at done
  subst t
  have registry := (increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered))
  have frame : departureQueues electra last = departureQueues electra exited := by
    rw [departureQueues_increase electra final, departureQueues_increase electra raised,
      departureQueues_decrease electra lowered]
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    rfl
  refine ⟨calls, ?_, DepartureCoverage.of_accessor early ?_,
    appended.kept_right (congrArg (fun q => q.2.2.2.2) frame), sites⟩
  · have epoch := congrArg Prod.fst frame
    have balance := congrArg (fun q => q.2.1) frame
    change last.earliestExitEpoch electra = exited.earliestExitEpoch electra at epoch
    change last.exitBalanceToConsume electra = exited.exitBalanceToConsume electra at balance
    rw [epoch, balance]
    exact trace
  · intro other old next before after unset assigned
    have readMarked := (getValidator_of_validators_eq registry other).symm.trans after
    by_cases same : other = index
    · subst other
      have sameNext := Except.ok.inj
        ((getValidator_setValidator_self markedOk).symm.trans readMarked)
      subst next
      exact covered index old validator before found unset assigned
    · have readExited := (getValidator_setValidator_of_ne markedOk same).symm.trans readMarked
      exact covered other old next before readExited unset assigned

/-- Calls that read the state's own exit churn and activation epoch start no earlier than it.

Their rates stay within the activation-exit cap. -/
private theorem exit_site_bounds {fork : Fork} {s : BeaconState preset fork}
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    {calls : List (IndexedDepartureCall preset config)}
    (sites : ∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first) :
    DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
      calls ∧ ∀ called ∈ calls,
      called.call.rate.toNat ≤ exitCap := by
  refine ⟨fun called member => ?_, fun called member => below _ (sites called member).1⟩
  have first := (computeActivationExitEpoch_ok_iff.mp (sites called member).2).2
  omega

/-- Consecutive queue traces compose without adding capacity at their shared state. -/
theorem DepartureQueueTrace.append {a b c : Epoch} {x y z : Gwei}
    {first second : List DepartureQueueCall}
    (one : DepartureQueueTrace a x first b y) (two : DepartureQueueTrace b y second c z) :
    DepartureQueueTrace a x (first ++ second) c z := by
  induction one with
  | nil => exact two
  | cons call tail ih => exact .cons call (ih two)

private structure SitePrefix {fork : Fork} (s t : BeaconState preset fork) : Prop where
  grows : s.validators.data.size ≤ t.validators.data.size
  active : ActiveStep s t
  effective : EffectiveKept s t

private theorem SitePrefix.refl {fork : Fork} (s : BeaconState preset fork) : SitePrefix s s :=
  ⟨Nat.le_refl _, .refl _, effectiveKept_refl _⟩

private theorem SitePrefix.trans {fork : Fork} {s t u : BeaconState preset fork}
    (one : SitePrefix s t) (two : SitePrefix t u) : SitePrefix s u :=
  ⟨Nat.le_trans one.grows two.grows, one.active.trans two.active,
    effectiveKept_trans one.effective two.effective one.grows⟩

private theorem SitePrefix.fold {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (kept : ∀ s a t, action s a = .ok t → SitePrefix s t)
    {s t : BeaconState preset fork} {items : List α}
    (ok : items.foldlM action s = .ok t) : SitePrefix s t :=
  foldlM_ok_invariant (SitePrefix s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s) ok

/-- A step that keeps the slot, the activity and the effective balances keeps the exit churn limit.

Before Gloas the limit reads only the total active balance of the current epoch. -/
private theorem ExitRateBelow.of_prefix {fork : Fork} {s t : BeaconState preset fork}
    {exitCap : Nat} (early : fork < .glamsterdam) (kept : SitePrefix s t)
    (below : ExitRateBelow config exitCap s) : ExitRateBelow config exitCap t := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, kept.active.1]
  have total := total_active_congr
    (kept.active.2.mono (getCurrentEpoch_le_activityFixedEpoch s)) epoch kept.effective
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  intro rate computed
  apply below rate
  rw [← computed]
  simp only [exitChurnLimit, notGloas, ↓reduceIte, getActivationExitChurnLimit,
    getBalanceChurnLimit, total]

/-- A state with the same registry and slot has the same exit churn limit. -/
private theorem ExitRateBelow.of_validators {fork : Fork} {s t : BeaconState preset fork}
    {exitCap : Nat} (early : fork < .glamsterdam)
    (validators : t.validators.data = s.validators.data) (slot : t.slot = s.slot)
    (below : ExitRateBelow config exitCap s) : ExitRateBelow config exitCap t :=
  ExitRateBelow.of_prefix early
    ⟨Nat.le_of_eq (congrArg Array.size validators).symm,
      ActiveStep.of_validators validators slot, effectiveKept_data validators⟩ below

private theorem exit_sites_fold {fork : Fork} {α ε : Type}
    {operation : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (electra : .pectra ≤ fork)
    (invariant : BeaconState preset fork → Prop)
    (localTrace : ∀ s item t, operation s item = .ok t →
      ∃ calls : List (IndexedDepartureCall preset config),
        DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
          (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
        DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
        ∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
          computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first)
    (lifecycle : ∀ s item t, operation s item = .ok t → RegistryLifecycle s t)
    (frame : ∀ s item t, operation s item = .ok t → invariant s →
      SitePrefix s t ∧ t.slot = s.slot ∧ invariant t)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM operation s = .ok t) (initial : invariant s) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  induction items generalizing s with
  | nil =>
    cases ok
    exact ⟨[], .nil _ _, .of_data rfl, .of_kept rfl, by simp⟩
  | cons item items ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, stepped, rest⟩ := ok
    obtain ⟨first, firstTrace, firstCoverage, firstAppended, firstSites⟩ :=
      localTrace s item middle stepped
    have framed := frame s item middle stepped initial
    obtain ⟨later, laterTrace, laterCoverage, laterAppended, laterSites⟩ := ih rest framed.2.2
    refine ⟨first ++ later, ?_, ?_, firstAppended.append laterAppended, ?_⟩
    · simpa only [List.map_append] using firstTrace.append laterTrace
    · exact firstCoverage.append_of_effectiveKept laterCoverage (lifecycle _ _ _ stepped)
        (RegistryLifecycle.foldlM lifecycle rest) framed.1.effective
    · intro called member
      rcases List.mem_append.mp member with member | member
      · exact ⟨s, .refl _, rfl, firstSites called member⟩
      · obtain ⟨site, beforeSite, slot, rate, first⟩ := laterSites called member
        exact ⟨site, framed.1.trans beforeSite, slot.trans framed.2.1, rate, first⟩
private theorem registry_entry_site_frame {fork : Fork} {s t : BeaconState preset fork}
    {activation : Epoch} {index : Nat}
    (later : (getCurrentEpoch s).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < activation.toNat)
    (ok : updateRegistryEntryElectra config activation s index = .ok t) :
    SitePrefix s t ∧ t.slot = s.slot := by
  have framed := frame_updateRegistryEntryElectra ok
  refine ⟨⟨framed.registryGrows, ?_, effectiveKept_registryElectra ok⟩, framed.slot⟩
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact activeStep_setValidatorAt found (fun _ _ => by simp only [isActiveValidator]) set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact activeStep_initiateValidatorExit exited
  split at ok
  · rename_i eligible
    simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
    exact activeStep_setValidatorAt found (fun _ le => isActiveValidator_eq_of_activation
      (.inl eligible.2) (activityFixedEpoch_lt_of_toNat_lt later) le) (liftAccessor_ok.mp ok)
  · cases ok
    exact .refl _
private theorem registry_fold_exit_sites {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {activation : Epoch}
    {indices : List Nat}
    (later : (getCurrentEpoch s).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < activation.toNat)
    (ok : indices.foldlM (updateRegistryEntryElectra config activation) s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  apply exit_sites_fold electra
    (fun state => (getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
      activation.toNat)
    (fun _ _ _ computed => registry_entry_exit_site electra early computed) ?_ ?_ ok later
  · intro a index b computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, found, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, set⟩ := computed
      exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, exited⟩ := computed
      exact registryLifecycle_initiateValidatorExit exited
    split at computed
    · rename_i eligible
      have far := activationEpoch_of_isEligibleForActivation eligible
      exact .setValidatorAt found (liftAccessor_ok.mp computed)
        ⟨fun set => absurd far set, fun _ => rfl⟩
    · cases computed
      exact .refl _
  · intro a index b computed bound
    have framed := registry_entry_site_frame bound computed
    refine ⟨framed.1, framed.2, ?_⟩
    simpa only [getCurrentEpoch, framed.2] using bound

private theorem proposer_exit_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashing_exit_site electra early slashed
private theorem voluntary_exit_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first := by
  obtain ⟨calls, trace, appended, sites, covered⟩ :=
    initiate_exit_site electra (processVoluntaryExit_initiates ok)
  exact ⟨calls, trace, DepartureCoverage.of_accessor early covered, appended, sites⟩
private theorem proposer_fold_exit_sites {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {slashings : List ProposerSlashing}
    (ok : slashings.foldlM (processProposerSlashing config checks) s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  apply exit_sites_fold electra (fun _ => True)
    (fun _ _ _ computed => proposer_exit_site electra early computed)
    (fun _ _ _ computed => registryLifecycle_processProposerSlashing computed) ?_ ok trivial
  intro a slashing b computed _
  have framed := frame_processProposerSlashing computed
  exact ⟨⟨framed.registryGrows, activeStep_processProposerSlashing computed,
    effectiveKept_proposerSlashing computed⟩, framed.slot, trivial⟩
private theorem voluntary_fold_exit_sites {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {exits : List SignedVoluntaryExit}
    (ok : exits.foldlM (processVoluntaryExit config checks) s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  apply exit_sites_fold electra (fun _ => True)
    (fun _ _ _ computed => voluntary_exit_site electra early computed)
    (fun _ _ _ computed => registryLifecycle_processVoluntaryExit computed) ?_ ok trivial
  intro a signed b computed _
  have framed := frame_processVoluntaryExit computed
  exact ⟨⟨framed.registryGrows, activeStep_processVoluntaryExit computed,
    effectiveKept_voluntaryExit computed⟩, framed.slot, trivial⟩
private theorem slashable_fold_exit_sites {fork : Fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {indices : List ValidatorIndex} {s t : BeaconState preset fork} {flag nextFlag : Bool}
    (ok : indices.foldlM (slashIfSlashable config) (s, flag) = .ok (t, nextFlag)) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  induction indices generalizing s flag with
  | nil =>
    cases ok
    exact ⟨[], .nil _ _, .of_data rfl, .of_kept rfl, by simp⟩
  | cons index rest ih =>
    obtain ⟨⟨middle, flag'⟩, stepped, remaining⟩ := bind_ok_iff.mp ok
    obtain ⟨later, tail, laterCoverage, laterAppended, laterSites⟩ := ih remaining
    have tailLifecycle : RegistryLifecycle middle t := by
      exact foldlM_ok_invariant (fun pair => RegistryLifecycle middle pair.1)
        (fun _ _ _ before step => before.trans (registryLifecycle_slashIfSlashable step))
        (.refl middle) remaining
    simp only [slashIfSlashable, bind_ok_iff] at stepped
    obtain ⟨_, _, stepped⟩ := stepped
    split at stepped
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at stepped
      obtain ⟨_, slashed, rfl, _⟩ := stepped
      obtain ⟨first, head, firstCoverage, firstAppended, firstSites⟩ :=
        slashing_exit_site electra early slashed
      have framed := frame_slashValidator slashed
      have kept : SitePrefix s _ := ⟨framed.registryGrows,
        activeStep_slashValidator slashed, effectiveKept_slash slashed⟩
      refine ⟨first ++ later, ?_, ?_, firstAppended.append laterAppended, ?_⟩
      · simpa only [List.map_append] using head.append tail
      · exact firstCoverage.append_of_effectiveKept laterCoverage
          (registryLifecycle_slashValidator slashed) tailLifecycle (effectiveKept_slash slashed)
      · intro called member
        rcases List.mem_append.mp member with member | member
        · exact ⟨s, .refl _, rfl, firstSites called member⟩
        · obtain ⟨site, beforeSite, slot, rate, first⟩ := laterSites called member
          exact ⟨site, kept.trans beforeSite, slot.trans framed.slot, rate, first⟩
    · cases stepped
      exact ⟨later, tail, laterCoverage, laterAppended, laterSites⟩
private theorem attester_exit_sites {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, flag⟩, foldedOk, ok⟩ := ok
  simp only [pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact slashable_fold_exit_sites electra early foldedOk
private theorem withdrawal_request_exit_site {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, exitChurnLimit config s = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first := by
  rcases withdrawalRequest_cases ok with same | ⟨index, _, _, exited⟩ |
    ⟨index, v, owed, _, withdrawn⟩
  · subst t
    exact ⟨[], .nil _ _, .of_data rfl, .of_kept rfl, by simp⟩
  · obtain ⟨calls, trace, appended, sites, covered⟩ := initiate_exit_site electra exited
    exact ⟨calls, trace, DepartureCoverage.of_accessor early covered, appended, sites⟩
  · obtain ⟨registry, calls, trace, appended, sites⟩ := partial_exit_site electra withdrawn
    refine ⟨calls, trace, ?_, appended, fun called member => (sites called member).2⟩
    intro i old next before after unset assigned
    have equal := Option.some.inj
      (before.symm.trans (by simpa only [registry] using after))
    exact False.elim (assigned (equal ▸ unset))
private theorem withdrawal_fold_exit_sites {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {requests : List WithdrawalRequest}
    (ok : requests.foldlM (processWithdrawalRequest config · electra ·) s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  apply exit_sites_fold electra (fun _ => True)
    (fun _ _ _ computed => withdrawal_request_exit_site electra early computed)
    (fun _ _ _ computed => registryLifecycle_processWithdrawalRequest computed) ?_ ok trivial
  intro a request b computed _
  have framed := frame_processWithdrawalRequest computed
  exact ⟨⟨framed.registryGrows, activeStep_processWithdrawalRequest computed,
    effectiveKept_withdrawalRequest computed⟩, framed.slot, trivial⟩

/-- Calls that read their activation epoch at a state with the slot of `s` start no earlier.

They start at or after the epoch of `s`. -/
private theorem callsFrom_of_sites {fork : Fork} {s : BeaconState preset fork}
    {calls : List (IndexedDepartureCall preset config)}
    (sites : ∀ called ∈ calls, ∃ site : BeaconState preset fork, site.slot = s.slot ∧
      computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first) :
    DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls := by
  intro called member
  obtain ⟨site, slot, first⟩ := sites called member
  have bound := (computeActivationExitEpoch_ok_iff.mp first).2
  have epoch : getCurrentEpoch site = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  rw [epoch] at bound
  omega

/-- Calls that read a state with the slot of `s` start no earlier than the epoch of `s`.

Their rates stay within the bound that each of their states keeps. -/
private theorem exit_sites_bounds {fork : Fork} {s : BeaconState preset fork} (exitCap : Nat)
    {calls : List (IndexedDepartureCall preset config)}
    (sites : ∀ called ∈ calls, ∃ site : BeaconState preset fork, site.slot = s.slot ∧
      ExitRateBelow config exitCap site ∧ exitChurnLimit config site = .ok called.call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first) :
    DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
      calls ∧ ∀ called ∈ calls,
      called.call.rate.toNat ≤ exitCap := by
  refine ⟨callsFrom_of_sites fun called member => ?_, fun called member => ?_⟩
  · obtain ⟨site, slot, -, -, first⟩ := sites called member
    exact ⟨site, slot, first⟩
  · obtain ⟨_, -, below, rate, -⟩ := sites called member
    exact below _ rate

/-- Attester slashings retain charge coverage through their slashable-validator fold. -/
private theorem attesterSlashing_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {slashing : AttesterSlashing preset fork}
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ exitCap) ∧
      PartialsAppended electra s t calls := by
  obtain ⟨calls, trace, covered, appended, sites⟩ := attester_exit_sites electra early ok
  obtain ⟨firsts, rates⟩ :=
    exit_sites_bounds (s := s) exitCap fun called member => by
      obtain ⟨site, kept, slot, rate, first⟩ := sites called member
      exact ⟨site, slot, ExitRateBelow.of_prefix early kept below, rate, first⟩
  exact ⟨calls, firsts, trace, covered, rates, appended⟩

/-- A proposer slashing retains the charged index of its exit call. -/
private theorem proposerSlashing_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {slashing : ProposerSlashing}
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ exitCap) ∧
      PartialsAppended electra s t calls := by
  obtain ⟨calls, trace, covered, appended, sites⟩ := proposer_exit_site electra early ok
  obtain ⟨firsts, rates⟩ := exit_site_bounds exitCap below sites
  exact ⟨calls, firsts, trace, covered, rates, appended⟩

/-- An Electra epoch calls the exit queue only in its registry updates.

Each queue trace, coverage and append of those updates is also one of the whole epoch. -/
private theorem epoch_registry_cut {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processEpoch config checks s = .ok t) :
    ∃ rewarded registered, processRegistryUpdates config rewarded = .ok registered ∧
      rewarded.slot = s.slot ∧ rewarded.validators = s.validators ∧
      ∀ calls : List (IndexedDepartureCall preset config),
        DepartureQueueTrace (rewarded.earliestExitEpoch electra)
          (rewarded.exitBalanceToConsume electra) (calls.map (·.call))
          (registered.earliestExitEpoch electra) (registered.exitBalanceToConsume electra) →
        DepartureCoverage rewarded registered calls →
        PartialsAppended electra rewarded registered calls →
        DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
          (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
        DepartureCoverage s t calls ∧ PartialsAppended electra s t calls := by
  -- Cut the schedule at registry updates, the only stage that calls the exit queue.
  obtain ⟨rewarded, registered, head, entriesOk, tail⟩ := processEpoch_registryCut ok
  -- The stages before registry updates keep the slot, the registry and both queues.
  have headKept : rewarded.slot = s.slot ∧ rewarded.validators = s.validators ∧
      departureQueues electra rewarded = departureQueues electra s := by
    apply head.transport (fun a b => b.slot = a.slot ∧ b.validators = a.validators ∧
        departureQueues electra b = departureQueues electra a) (fun _ => ⟨rfl, rfl, rfl⟩)
      (by
        intro _ _ _ one two
        exact ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.trans one.2.2⟩)
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    have other : k ≠ .registry := by rintro rfl; simp at member
    exact ⟨edge.slot_eq, edge.validators_eq ⟨other, by rintro rfl; simp at member,
      by rintro rfl; simp at member⟩, epochStage_departureQueues electra early edge other⟩
  -- The stages after it keep both queues and assign no exit.
  have tailKept : departureQueues electra t = departureQueues electra registered ∧
      DepartureCoverage (config := config) registered t [] ∧ RegistryLifecycle registered t := by
    apply tail.transport (fun a b => departureQueues electra b = departureQueues electra a ∧
        DepartureCoverage (config := config) a b [] ∧ RegistryLifecycle a b)
      (fun _ => ⟨rfl, .of_data rfl, .refl _⟩)
      (by
        intro _ _ _ one two
        exact ⟨two.1.trans one.1, one.2.1.suffix_of_empty two.2.1 one.2.2 two.2.2,
          one.2.2.trans two.2.2⟩)
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    have other : k ≠ .registry := by
      rintro rfl
      simp [EpochStage.middleStages, EpochStage.tailStages] at member
    exact ⟨epochStage_departureQueues electra early edge other, epochStage_coverage edge other⟩
  have registryLife := registryLifecycle_processRegistryUpdates entriesOk
  refine ⟨rewarded, registered, entriesOk, headKept.1, headKept.2.1, ?_⟩
  intro calls queued covered appended
  have firstEpoch := congrArg Prod.fst headKept.2.2
  have firstBalance := congrArg (fun q => q.2.1) headKept.2.2
  have lastEpoch := congrArg Prod.fst tailKept.1
  have lastBalance := congrArg (fun q => q.2.1) tailKept.1
  change rewarded.earliestExitEpoch electra = s.earliestExitEpoch electra at firstEpoch
  change rewarded.exitBalanceToConsume electra = s.exitBalanceToConsume electra at firstBalance
  change t.earliestExitEpoch electra = registered.earliestExitEpoch electra at lastEpoch
  change t.exitBalanceToConsume electra = registered.exitBalanceToConsume electra at lastBalance
  rw [firstEpoch, firstBalance] at queued
  rw [lastEpoch, lastBalance]
  refine ⟨queued, ?_,
    (appended.kept_left (congrArg (fun q => q.2.2.2.2) headKept.2.2)).kept_right
      (congrArg (fun q => q.2.2.2.2) tailKept.1)⟩
  intro i old next a b
  apply covered.suffix_of_empty tailKept.2.1 registryLife tailKept.2.2 i old next _ b
  simpa only [headKept.2.1] using a

/-- An Electra epoch spends departure capacity only in the registry's exit calls. -/
private theorem epoch_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    (ok : processEpoch config checks s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ exitCap) ∧
      PartialsAppended electra s t calls := by
  obtain ⟨rewarded, registered, entriesOk, slot, same, cut⟩ := epoch_registry_cut electra early ok
  simp only [processRegistryUpdates, electra, ↓reduceIte, bind_ok_iff, liftAccessor_ok] at entriesOk
  obtain ⟨activation, computed, entries⟩ := entriesOk
  simp only [liftArith, mapError_ok_iff] at computed
  have exactEpoch := (computeActivationExitEpoch_ok_iff.mp computed).2
  have later : (getCurrentEpoch rewarded).toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
      activation.toNat := by omega
  obtain ⟨calls, queued, covered, appended, sites⟩ :=
    registry_fold_exit_sites electra early later entries
  have belowRewarded : ExitRateBelow config exitCap rewarded :=
    ExitRateBelow.of_validators early (congrArg (·.data) same) slot below
  obtain ⟨firsts, rates⟩ :=
    exit_sites_bounds (s := rewarded) exitCap fun called member => by
      obtain ⟨site, kept, slot, rate, first⟩ := sites called member
      exact ⟨site, slot, ExitRateBelow.of_prefix early kept belowRewarded, rate, first⟩
  obtain ⟨trace, coverage, partials⟩ := cut calls queued covered appended
  refine ⟨calls, ?_, trace, coverage, rates, partials⟩
  simpa only [getCurrentEpoch, slot] using firsts

/-- Slot caching and increment preserve epoch charge coverage and its pre-update amounts. -/
private theorem slot_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    (ok : advanceSlot config checks s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ exitCap) ∧
      PartialsAppended electra s t calls := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨calls, firsts, trace, covered, rates, appended⟩ :=
      epoch_indexedTrace electra early exitCap
        (ExitRateBelow.of_validators early (by rfl) (by rfl) below) advance
    exact ⟨calls, firsts, trace, covered, rates, appended⟩
  · cases advance
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, .of_data rfl, by simp, .of_kept rfl⟩

/-- After Electra and before Gloas, upgrades carry both departure queues and the registry.

The only such upgrade is the one to Fulu. -/
private theorem upgrades_departureQueues {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) (targetElectra : .pectra ≤ t.fork) :
    departureQueues targetElectra t.state = departureQueues electra s.state ∧
      t.state.validators.data = s.state.validators.data ∧
      t.state.balances.data = s.state.balances.data ∧
      (t.state.pendingConsolidations targetElectra).data =
        (s.state.pendingConsolidations electra).data := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    have nextElectra := Nat.le_trans electra (Nat.le_of_lt next.property)
    have nextEarly := Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early
    obtain ⟨queues, registry, balances, pending⟩ := ih next nextElectra early rest targetElectra
    rw [queues, registry, balances, pending]
    obtain ⟨fork, state⟩ := s
    have sourceEarly := Nat.lt_trans next.property nextEarly
    have forkCases : fork = .pectra ∨ fork = .fusaka := by
      change Fork.pectra ≤ fork at electra
      change fork < Fork.glamsterdam at sourceEarly
      cases fork <;> simp_all (config := { decide := true })
      all_goals cases nextOk
    rcases forkCases with rfl | rfl
    · simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨_, upgraded, rfl⟩ := nextOk
      refine ⟨?_, (upgradeToFulu_spec upgraded).1, (upgradeToFulu_spec upgraded).2.1, ?_⟩
      all_goals
        simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
        obtain ⟨_, _, rfl⟩ := upgraded
        rfl
    · simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨_, _, rfl⟩ := nextOk
      exact False.elim (Nat.lt_irrefl _ nextEarly)
  | case2 s notDue => cases ok; exact ⟨rfl, rfl, rfl, rfl⟩

/-- After Electra and before Gloas, the upgrades of a slot keep the registry.

The only such upgrade is the one to Fulu, which carries the validators as they are. -/
theorem processUpgrades_validators_of_electra {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) :
    t.state.validators.data = s.state.validators.data :=
  (upgrades_departureQueues electra early ok
    (Nat.le_trans electra (processUpgrades_fork_le ok))).2.1

/-- The withdrawal-request fold retains charge coverage and all capacity-consuming calls. -/
private theorem withdrawalRequests_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {requests : List WithdrawalRequest}
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    (ok : requests.foldlM (processWithdrawalRequest config · electra ·) s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ exitCap) ∧
      PartialsAppended electra s t calls := by
  obtain ⟨calls, trace, covered, appended, sites⟩ := withdrawal_fold_exit_sites electra early ok
  obtain ⟨firsts, rates⟩ :=
    exit_sites_bounds (s := s) exitCap fun called member => by
      obtain ⟨site, kept, slot, rate, first⟩ := sites called member
      exact ⟨site, slot, ExitRateBelow.of_prefix early kept below, rate, first⟩
  exact ⟨calls, firsts, trace, covered, rates, appended⟩

/-- The number of validators active at the current epoch of a state. -/
def activeCount {fork : Fork} (s : BeaconState preset fork) : Nat :=
  (getActiveValidatorIndices s (getCurrentEpoch s)).length

/-- At most every validator of the registry is active. -/
private theorem activeCount_le_size {fork : Fork} (s : BeaconState preset fork) :
    activeCount s ≤ s.validators.data.size :=
  (List.length_filterMap_le _ _).trans (by simp)

/-- The validator-count churn is bounded by the churn of any bound on the active count. -/
theorem validatorChurnLimit_le_of_active {fork : Fork} (s : BeaconState preset fork)
    (bound : Nat) (counted : activeCount s ≤ bound) :
    (getValidatorChurnLimit config s).toNat ≤ cohortCap config bound := by
  have converted : (getActiveValidatorIndices s (getCurrentEpoch s)).length.toUInt64.toNat ≤
      bound := (Nat.mod_le _ _).trans counted
  simp only [getValidatorChurnLimit, Uint64.toNat_max, UInt64.toNat_div, cohortCap]
  exact max_le_max_left _ (Nat.div_le_div_right converted)

/-- The validator-count churn is bounded by the registry size, not just active entries. -/
theorem validatorChurnLimit_le_cohortCap {fork : Fork} (s : BeaconState preset fork)
    (bound : Nat) (bounded : s.validators.data.size ≤ bound) :
    (getValidatorChurnLimit config s).toNat ≤ cohortCap config bound :=
  validatorChurnLimit_le_of_active s bound ((activeCount_le_size s).trans bounded)

/-- A finite pre-Electra exit is assigned only while its count cohort has room. -/
private theorem exitQueue_count_room {fork : Fork} {s queued : BeaconState preset fork}
    (early : fork < .pectra) {amount : Gwei} {epoch : Epoch}
    (ok : exitQueue config s amount = .ok (queued, epoch))
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (bound : Nat) (counted : activeCount s ≤ bound) :
    queued = s ∧
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length <
        max 1 (cohortCap config bound) := by
  have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt early
  simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨placed, scheduled, rfl, rfl⟩ := ok
  exact ⟨rfl, (exitQueueEpoch_churn scheduled finite).trans_le
    (max_le_max_left _ (validatorChurnLimit_le_of_active s bound counted))⟩

/-- Voluntary exits retain concrete charge coverage across their entire operation fold. -/
private theorem voluntaryExits_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {exits : List SignedVoluntaryExit}
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    (ok : exits.foldlM (processVoluntaryExit config checks) s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ exitCap) ∧
      PartialsAppended electra s t calls := by
  obtain ⟨calls, trace, covered, appended, sites⟩ := voluntary_fold_exit_sites electra early ok
  obtain ⟨firsts, rates⟩ :=
    exit_sites_bounds (s := s) exitCap fun called member => by
      obtain ⟨site, kept, slot, rate, first⟩ := sites called member
      exact ⟨site, slot, ExitRateBelow.of_prefix early kept below, rate, first⟩
  exact ⟨calls, firsts, trace, covered, rates, appended⟩

/-- Successful consolidation requests record the input to their balance-queue call.

Credential switches and ignored requests do not call that queue. -/
private def consolidationRequestCalls {fork : Fork} (config : Config)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : ConsolidationRequest) : Except TransitionError Bool := do
  if request.sourcePubkey == request.targetPubkey then return false
  if (state.pendingConsolidations electra).data.size ==
      preset.PENDING_CONSOLIDATIONS_LIMIT.toNat then return false
  if (← liftAccessor (getConsolidationChurnLimit config state)) ≤ preset.MIN_ACTIVATION_BALANCE
    then return false
  let some sourcePosition := findValidatorByPubkey state request.sourcePubkey | return false
  let some targetPosition := findValidatorByPubkey state request.targetPubkey | return false
  let sourceIndex ← liftAccessor (liftArith (Uint64.ofNatChecked sourcePosition.val))
  let targetIndex ← liftAccessor (liftArith (Uint64.ofNatChecked targetPosition.val))
  let source := state.validators.data[sourcePosition]
  let target := state.validators.data[targetPosition]
  unless hasExecutionWithdrawalCredential source &&
      credentialAddress source.withdrawalCredentials == request.sourceAddress do return false
  unless hasCompoundingWithdrawalCredential target do return false
  let epoch := getCurrentEpoch state
  unless isActiveValidator source epoch && isActiveValidator target epoch do return false
  unless source.exitEpoch == FAR_FUTURE_EPOCH && target.exitEpoch == FAR_FUTURE_EPOCH do
    return false
  let eligible ←
    liftAccessor (liftArith
      (Uint64.addChecked source.activationEpoch config.SHARD_COMMITTEE_PERIOD))
  if epoch < eligible then return false
  if 0 < (← liftAccessor (getPendingBalanceToWithdraw state electra sourceIndex)) then
    return false
  let _ ← queueConsolidation config state electra sourceIndex source targetIndex
  return true

/-- The state of a consolidation request when it calls the consolidation queue, else none. -/
private def consolidationRequestSites {fork : Fork} (config : Config)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : ConsolidationRequest) :
    Except TransitionError (List (ForkedBeaconState preset)) := do
  return if ← consolidationRequestCalls config state electra request then [⟨fork, state⟩] else []

/-- Consolidation requests never spend the separate exit queue. -/
private theorem consolidationRequest_exitFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    t.earliestExitEpoch electra = s.earliestExitEpoch electra ∧
      t.exitBalanceToConsume electra = s.exitBalanceToConsume electra ∧
      (t.pendingPartialWithdrawals electra).data = (s.pendingPartialWithdrawals electra).data := by
  rcases consolidationRequest_cases ok with rfl | ⟨_, _, _, switched⟩ | ⟨i, v, j, _, _, called⟩
  · exact ⟨rfl, rfl, rfl⟩
  · have frame := switchToCompounding_departureQueues electra switched
    exact ⟨congrArg Prod.fst frame, congrArg (fun q => q.2.1) frame,
      congrArg (fun q => q.2.2.2.2) frame⟩
  · obtain ⟨_, _, _, _, _, _, _, set, _, rfl⟩ := queueConsolidation_steps called
    obtain ⟨_, rfl⟩ := setValidator_ok set
    exact ⟨rfl, rfl, rfl⟩

private theorem queueExcess_registry {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : t.validators = s.validators := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rfl
  · cases ok; rfl

private theorem switchToCompounding_coverage {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) :
    DepartureCoverage (config := config) s t [] := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨validator, found, changed, set, queued⟩ := ok
  have setAt := set
  rw [setValidator_eq_setValidatorAt] at setAt
  have covered := DepartureCoverage.setValidatorAt (config := config)
    (by rwa [← getValidator_eq_getValidatorAt] : getValidatorAt s index.toNat = .ok validator)
    setAt rfl
  apply covered.suffix (RegistryLifecycle.setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩)
  intro i old next before after
  rw [queueExcess_registry electra queued] at after
  cases Option.some.inj (before.symm.trans after)
  rfl

/-- A credential switch keeps the pending consolidations. -/
private theorem switchToCompounding_pendingConsolidations {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) :
    (t.pendingConsolidations electra).data = (s.pendingConsolidations electra).data := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, _, set, queued⟩ := ok
  obtain ⟨_, rfl⟩ := setValidator_ok set
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, setBalanceOk, rfl⟩ := queued
    obtain ⟨_, rfl⟩ := setBalance_ok setBalanceOk
    rfl
  · cases queued; rfl

/-- A request classified as not calling churn preserves both departure queues.

It also keeps the pending consolidations. -/
private theorem consolidationRequest_notCalled_frames {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok false) :
    departureQueues electra t = departureQueues electra s ∧
      (t.pendingConsolidations electra).data = (s.pendingConsolidations electra).data := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls at classified
  simp only [bind, Except.bind, pure, Except.pure] at ok classified
  repeat' split at ok
  all_goals first
    | (cases ok; exact ⟨rfl, rfl⟩)
    | (cases ok)
    | exact ⟨switchToCompounding_departureQueues electra (liftAccessor_ok.mp ok),
        switchToCompounding_pendingConsolidations electra (liftAccessor_ok.mp ok)⟩
    | (simp_all only [↓reduceIte, Bool.false_eq_true]; cases classified)

/-- A request classified as not calling churn preserves both departure queues. -/
private theorem consolidationRequest_notCalled {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok false) :
    departureQueues electra t = departureQueues electra s :=
  (consolidationRequest_notCalled_frames electra ok classified).1

/-- A consolidation request without a churn call assigns no exit epoch. -/
private theorem consolidationRequest_notCalled_coverage {fork : Fork}
    {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok false) :
    DepartureCoverage (config := config) s t [] := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls at classified
  simp only [bind, Except.bind, pure, Except.pure] at ok classified
  repeat' split at ok
  all_goals first
    | (cases ok; exact DepartureCoverage.of_data rfl)
    | (cases ok)
    | exact switchToCompounding_coverage electra (liftAccessor_ok.mp ok)
    | (simp_all only [↓reduceIte, Bool.false_eq_true]; cases classified)

/-- A request classified as calling churn schedules its actual registry source. -/
private theorem consolidationRequest_called {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok true) :
    ∃ sourceIndex source targetIndex,
      getValidator s sourceIndex = .ok source ∧
      queueConsolidation config s electra sourceIndex source targetIndex = .ok t := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls at classified
  simp only [bind, Except.bind, pure, Except.pure] at ok classified
  repeat' split at ok
  all_goals first
    | (solve | cases ok)
    | exact ⟨_, _, _, getValidator_eq_ok_iff.mpr
        (getElem?_toNat_of_ofNatChecked (by assumption)), ok⟩
    | (simp_all only [↓reduceIte, Bool.false_eq_true]; cases classified)

/-- A successful request always has a successful classification of its churn call. -/
private theorem consolidationRequestCalls_result {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    ∃ called, consolidationRequestCalls config s electra request = .ok called := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls
  split at ok
  · rename_i same
    simp only [same, ↓reduceIte, pure, Except.pure]
    exact ⟨false, rfl⟩
  · rename_i different
    simp only [different]
    repeat' first
      | (split at ok)
      | (simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok)
      | (obtain ⟨value, computed, ok⟩ := ok)
    all_goals simp_all only [bind, Except.bind, pure, Except.pure, ↓reduceIte]
    all_goals first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩

/-- Replay requests in order, retaining each actual consolidation queue input. -/
private def consolidationRequestsSites {fork : Fork} (config : Config) (electra : .pectra ≤ fork)
    (state : BeaconState preset fork) : List ConsolidationRequest →
      Except TransitionError (BeaconState preset fork × List (ForkedBeaconState preset))
  | [] => pure (state, [])
  | request :: rest => do
    let sites ← consolidationRequestSites config state electra request
    let next ← processConsolidationRequest config state electra request
    let (last, later) ← consolidationRequestsSites config electra next rest
    return (last, sites ++ later)

private theorem consolidationRequestsSites_result {fork : Fork}
    {electra : .pectra ≤ fork} {s t : BeaconState preset fork}
    {requests : List ConsolidationRequest}
    (ok : requests.foldlM (processConsolidationRequest config · electra ·) s = .ok t) :
    ∃ sites, consolidationRequestsSites config electra s requests = .ok (t, sites) := by
  induction requests generalizing s with
  | nil => cases ok; exact ⟨[], rfl⟩
  | cons request rest ih =>
    obtain ⟨next, stepped, remaining⟩ := bind_ok_iff.mp ok
    obtain ⟨called, classified⟩ := consolidationRequestCalls_result stepped
    obtain ⟨sites, replayed⟩ := ih remaining
    refine ⟨(if called then [⟨fork, s⟩] else []) ++ sites, ?_⟩
    simp only [consolidationRequestsSites, consolidationRequestSites, classified, stepped,
      replayed, bind, Except.bind, pure, Except.pure]

private theorem consolidationRequestsSites_indexedTrace_sites {fork : Fork}
    (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    {sites : List (ForkedBeaconState preset)} {requests : List ConsolidationRequest}
    (ok : consolidationRequestsSites config electra s requests = .ok (t, sites)) (cap : Nat)
    (rates : ∀ site ∈ sites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (calls.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config calls sites ∧ ∀ called ∈ calls, called.entry = none := by
  induction requests generalizing s sites with
  | nil =>
    cases ok
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, DepartureCoverage.of_data rfl,
      by simp, by simp [ConsolidationCallSites], by simp⟩
  | cons request rest ih =>
    simp only [consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨here, recorded, middle, stepped, ⟨last, later⟩, replayed, rfl, rfl⟩ := ok
    obtain ⟨tailCalls, tailFrom, tail, tailCoverage, tailRates, tailSites, tailEntries⟩ :=
      ih replayed
      (fun site mem h rate computed => rates site (List.mem_append_right _ mem) h rate computed)
    have epoch : getCurrentEpoch middle = getCurrentEpoch s := by
      simp only [getCurrentEpoch, (frame_processConsolidationRequest stepped).slot]
    rw [epoch] at tailFrom
    have tailLifecycle : RegistryLifecycle middle last := by
      have result : rest.foldlM (processConsolidationRequest config · electra ·) middle =
          .ok last := by
        clear tailFrom tail tailCoverage tailRates tailSites tailEntries rates recorded stepped ih
          epoch
        induction rest generalizing middle later last with
        | nil => cases replayed; rfl
        | cons request rest inner =>
          simp only [consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at replayed
          obtain ⟨_, _, next, step, ⟨_, _⟩, recur, rfl, rfl⟩ := replayed
          simp only [List.foldlM_cons, step, bind, Except.bind, inner _ _ _ recur]
      exact RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok) result
    simp only [consolidationRequestSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at recorded
    obtain ⟨called, classified, rfl⟩ := recorded
    cases called with
    | false =>
      have frame := consolidationRequest_notCalled electra stepped classified
      have epoch := congrArg (fun q => q.2.2.1) frame
      have balance := congrArg (fun q => q.2.2.2.1) frame
      change middle.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra
        at epoch
      change middle.consolidationBalanceToConsume electra =
        s.consolidationBalanceToConsume electra at balance
      rw [epoch, balance] at tail
      refine ⟨tailCalls, tailFrom, tail, ?_, tailRates, ?_, tailEntries⟩
      · exact DepartureCoverage.append_of_effectiveKept
          (consolidationRequest_notCalled_coverage electra stepped classified) tailCoverage
            (registryLifecycle_processConsolidationRequest stepped) tailLifecycle
            (effectiveKept_consolidationRequest stepped)
      · simpa using tailSites
    | true =>
      obtain ⟨sourceIndex, source, targetIndex, found, scheduled⟩ :=
        consolidationRequest_called electra stepped classified
      obtain ⟨call, first, head, rate, firstOk, entry, covered⟩ :=
        queueConsolidation_indexedTrace_site electra found scheduled
      have coverage : DepartureCoverage s middle [call] :=
        DepartureCoverage.of_accessor early (by
          intro other old next before after unset assigned
          exact ⟨call, List.mem_singleton_self _,
            covered other old next before after unset assigned⟩)
      refine ⟨call :: tailCalls, ?_, head.append tail, ?_, ?_, ?_, ?_⟩
      · intro called member
        exact (List.mem_cons.mp member).elim (fun same => same ▸ first) (tailFrom called)
      · exact coverage.append_of_effectiveKept tailCoverage
          (registryLifecycle_processConsolidationRequest stepped) tailLifecycle
          (effectiveKept_consolidationRequest stepped)
      · intro called member
        rcases List.mem_cons.mp member with rfl | member
        · exact rates ⟨fork, s⟩ (by simp) electra called.call.rate rate
        · exact tailRates called member
      · intro called member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨⟨fork, s⟩, by simp, firstOk, rate⟩
        · obtain ⟨site, present, paired⟩ := tailSites called member
          exact ⟨site, List.mem_append_right _ present, paired⟩
      · intro called member
        exact (List.mem_cons.mp member).elim (fun same => same ▸ entry) (tailEntries called)

/-- Deposit requests keep the registry, the activity and the effective balances. -/
private theorem depositRequests_sitePrefix {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deposits : List DepositRequest}
    (ok : deposits.foldlM (processDepositRequest · electra ·) s = .ok t) : SitePrefix s t :=
  SitePrefix.fold
    (fun _ _ _ h => ⟨(frame_processDepositRequest h).registryGrows,
      activeStep_processDepositRequest h, effectiveKept_depositRequest h⟩) ok

/-- Withdrawal requests keep the registry, the activity and the effective balances. -/
private theorem withdrawalRequests_sitePrefix {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {requests : List WithdrawalRequest}
    (ok : requests.foldlM (processWithdrawalRequest config · electra ·) s = .ok t) :
    SitePrefix s t :=
  SitePrefix.fold
    (fun _ _ _ h => ⟨(frame_processWithdrawalRequest h).registryGrows,
      activeStep_processWithdrawalRequest h, effectiveKept_withdrawalRequest h⟩) ok

private theorem executionRequests_coverage_sites {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s deposited withdrawn t : BeaconState preset fork}
    {deposits : List DepositRequest} {withdrawals : List WithdrawalRequest}
    {consolidations : List ConsolidationRequest} {sites : List (ForkedBeaconState preset)}
    (depositedOk : deposits.foldlM (processDepositRequest · electra ·) s = .ok deposited)
    (withdrawnOk : withdrawals.foldlM (processWithdrawalRequest config · electra ·)
      deposited = .ok withdrawn)
    (consolidatedOk : consolidations.foldlM (processConsolidationRequest config · electra ·)
      withdrawn = .ok t)
    (replayed : consolidationRequestsSites config electra withdrawn consolidations =
      .ok (t, sites)) (cap exitCap : Nat)
    (below : ExitRateBelow config exitCap s)
    (rates : ∀ site ∈ sites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        (exits ++ consolidations) ∧
      DepartureCoverage s t (exits ++ consolidations) ∧
      DepartureQueueTrace (deposited.earliestExitEpoch electra)
        (deposited.exitBalanceToConsume electra) (exits.map (·.call))
        (withdrawn.earliestExitEpoch electra) (withdrawn.exitBalanceToConsume electra) ∧
      DepartureQueueTrace (withdrawn.earliestConsolidationEpoch electra)
        (withdrawn.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ exitCap) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations sites ∧
      PartialsAppended electra s t exits ∧ ∀ called ∈ consolidations, called.entry = none := by
  have depositsData : deposited.validators = s.validators :=
    foldlM_ok_invariant (fun t => t.validators = s.validators)
      (fun _ _ _ kept ok => (processDepositRequest_ok ok).2.1.trans kept) rfl depositedOk
  have belowDeposited : ExitRateBelow config exitCap deposited :=
    ExitRateBelow.of_prefix early (depositRequests_sitePrefix electra depositedOk) below
  obtain ⟨exitCalls, exitFrom, exitTrace, exitCoverage, exitRates, exitAppended⟩ :=
    withdrawalRequests_indexedTrace electra early exitCap belowDeposited withdrawnOk
  obtain ⟨consolidationCalls, consolidationFrom, consolidationTrace,
    consolidationCoverage, consolidationRates, consolidationSites, consolidationEntries⟩ :=
    consolidationRequestsSites_indexedTrace_sites electra early replayed cap rates
  have depositedSlot :=
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processDepositRequest ok) depositedOk).slot
  have withdrawnSlot :=
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processWithdrawalRequest ok) withdrawnOk).slot
  have depositedEpoch : getCurrentEpoch deposited = getCurrentEpoch s := by
    simp only [getCurrentEpoch, depositedSlot]
  have withdrawnEpoch : getCurrentEpoch withdrawn = getCurrentEpoch s := by
    simp only [getCurrentEpoch, withdrawnSlot, depositedSlot]
  rw [depositedEpoch] at exitFrom
  rw [withdrawnEpoch] at consolidationFrom
  have coverage := exitCoverage.append_of_effectiveKept consolidationCoverage
    (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok) withdrawnOk)
    (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok) consolidatedOk)
    (effectiveKept_fold (fun _ _ _ ok => effectiveKept_withdrawalRequest ok)
      (fun _ _ _ ok => (registryLifecycle_processWithdrawalRequest ok).size_le) withdrawnOk)
  have depositsKept := congrArg (fun q => q.2.2.2.2)
    (foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
      (fun _ _ _ kept ok => (depositRequest_departureQueues electra ok).trans kept) rfl depositedOk)
  have consolidatedKept : (t.pendingPartialWithdrawals electra).data =
      (withdrawn.pendingPartialWithdrawals electra).data :=
    foldlM_ok_invariant (fun t => (t.pendingPartialWithdrawals electra).data =
        (withdrawn.pendingPartialWithdrawals electra).data)
      (fun _ _ _ kept ok => (consolidationRequest_exitFrame electra ok).2.2.trans kept) rfl
      consolidatedOk
  refine ⟨exitCalls, consolidationCalls, exitFrom.append consolidationFrom,
    ?_, exitTrace, consolidationTrace,
    exitRates, consolidationRates, consolidationSites,
    (exitAppended.kept_left depositsKept).kept_right consolidatedKept,
    consolidationEntries⟩
  intro i old next before after
  apply coverage i old next _ after
  simpa only [depositsData] using before

private theorem operations_prefix_site_prefixes {fork : Fork} (electra : .pectra ≤ fork)
    {s proposed attested voted deposited exited changed : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} {before : fork < .hegota}
    (proposedOk : body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) s = .ok proposed)
    (attestedOk : body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposed = .ok attested)
    (votedOk : body.attestations.data.toList.foldlM
      (processAttestation config checks · parentSlot ·) attested = .ok voted)
    (depositedOk : (body.deposits before).data.toList.foldlM
      (processDeposit config checks before) voted = .ok deposited)
    (exitedOk : body.voluntaryExits.data.toList.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited)
    (changedOk : processBlsToExecutionChanges config checks exited body = .ok changed) :
    SitePrefix s proposed ∧ SitePrefix s deposited ∧ SitePrefix s changed := by
  have proposers : SitePrefix s proposed := SitePrefix.fold
    (fun _ _ _ ok => ⟨(frame_processProposerSlashing ok).registryGrows,
      activeStep_processProposerSlashing ok, effectiveKept_proposerSlashing ok⟩) proposedOk
  have attesters : SitePrefix proposed attested := SitePrefix.fold
    (fun _ _ _ ok => ⟨(frame_processAttesterSlashing ok).registryGrows,
      activeStep_processAttesterSlashing ok, effectiveKept_attesterSlashing ok⟩) attestedOk
  have votes : SitePrefix attested voted := SitePrefix.fold
    (fun _ _ _ ok => ⟨(frame_processAttestation ok).registryGrows,
      activeStep_processAttestation ok,
      effectiveKept_data (congrArg (·.data) (processAttestation_registry ok).1)⟩) votedOk
  have deposits : SitePrefix voted deposited := SitePrefix.fold
    (fun _ _ _ ok => ⟨(frame_processDeposit ok).registryGrows,
      activeStep_processDeposit ok, effectiveKept_processDeposit ok⟩) depositedOk
  have exits : SitePrefix deposited exited := SitePrefix.fold
    (fun _ _ _ ok => ⟨(frame_processVoluntaryExit ok).registryGrows,
      activeStep_processVoluntaryExit ok, effectiveKept_voluntaryExit ok⟩) exitedOk
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  simp only [processBlsToExecutionChanges, capella, ↓reduceDIte,
    ← Array.foldlM_toList] at changedOk
  have changes : SitePrefix exited changed := SitePrefix.fold
    (fun _ _ _ ok => ⟨(frame_processBlsToExecutionChange ok).registryGrows,
      activeStep_processBlsToExecutionChange ok, effectiveKept_blsChange ok⟩) changedOk
  exact ⟨proposers, proposers.trans (attesters.trans (votes.trans deposits)),
    proposers.trans (attesters.trans (votes.trans (deposits.trans (exits.trans changes))))⟩

/-- The header, execution, randao and eth1 data of a block keep the registry and activity. -/
private theorem blockHead_sitePrefix {fork : Fork} {engine : ExecutionEngine preset fork}
    {s headed executed revealed voted : BeaconState preset fork}
    {block : BeaconBlock preset fork} {bellatrix : .bellatrix ≤ fork} {before : fork < .hegota}
    (headedOk : processBlockHeader s block = .ok headed)
    (executedOk : processBlockExecution config checks engine headed block.body bellatrix =
      .ok executed)
    (revealedOk : processRandao config checks executed block.body = .ok revealed)
    (votedOk : processEth1Data before revealed block.body = .ok voted) :
    SitePrefix s voted := by
  have head : SitePrefix s headed := by
    refine ⟨(frame_processBlockHeader headedOk).registryGrows,
      activeStep_processBlockHeader headedOk, ?_⟩
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact effectiveKept_refl _
  have execution : SitePrefix headed executed :=
    ⟨(frame_processBlockExecution executedOk).registryGrows,
      activeStep_processBlockExecution executedOk,
      effectiveKept_data (congrArg (·.data) (processBlockExecution_validators executedOk))⟩
  have randao : SitePrefix executed revealed := by
    refine ⟨(frame_processRandao revealedOk).registryGrows,
      activeStep_processRandao revealedOk, ?_⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    exact effectiveKept_refl _
  have vote : SitePrefix revealed voted := by
    refine ⟨(frame_processEth1Data votedOk).registryGrows,
      activeStep_processEth1Data votedOk, ?_⟩
    obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
    exact effectiveKept_data (congrArg (·.validators.data) rest)
  exact head.trans (execution.trans (randao.trans vote))

/-- The pre-Gloas operation prefix covers all exits before execution requests. -/
private theorem operationsPrefix_coverage {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s proposed attested voted deposited exited changed :
      BeaconState preset fork} {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    {before : fork < .hegota}
    (exitCap : Nat) (below : ExitRateBelow config exitCap s)
    (proposedOk : body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) s = .ok proposed)
    (attestedOk : body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposed = .ok attested)
    (votedOk : body.attestations.data.toList.foldlM
      (processAttestation config checks · parentSlot ·) attested = .ok voted)
    (depositedOk : (body.deposits before).data.toList.foldlM
      (processDeposit config checks before) voted = .ok deposited)
    (exitedOk : body.voluntaryExits.data.toList.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited)
    (changedOk : processBlsToExecutionChanges config checks exited body = .ok changed) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        calls ∧ DepartureCoverage s changed calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (changed.earliestExitEpoch electra)
        (changed.exitBalanceToConsume electra) ∧
      (∀ called ∈ calls,
        called.call.rate.toNat ≤ exitCap) ∧
      RegistryLifecycle s changed ∧
      (∀ i, i < s.validators.data.size →
        effectiveAt ⟨fork, changed⟩ i = effectiveAt ⟨fork, s⟩ i) ∧
      PartialsAppended electra s changed calls := by
  obtain ⟨toProposed, toDeposited, -⟩ := operations_prefix_site_prefixes electra proposedOk
    attestedOk votedOk depositedOk exitedOk changedOk
  have belowProposed := ExitRateBelow.of_prefix early toProposed below
  have belowDeposited := ExitRateBelow.of_prefix early toDeposited below
  obtain ⟨one, oneFrom, oneTrace, oneCoverage, oneRates, oneAppended⟩ :=
    DepartureCoverage.foldlM electra exitCap (ExitRateBelow config exitCap)
    (fun _ _ _ ok good => proposerSlashing_indexedTrace electra early exitCap good ok)
    (fun _ _ _ ok good => ExitRateBelow.of_prefix early
      ⟨(frame_processProposerSlashing ok).registryGrows, activeStep_processProposerSlashing ok,
        effectiveKept_proposerSlashing ok⟩ good)
    (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok)
    (fun _ _ _ ok => effectiveKept_proposerSlashing ok)
    (fun _ _ _ ok => (frame_processProposerSlashing ok).slot) below proposedOk
  obtain ⟨two, twoFrom, twoTrace, twoCoverage, twoRates, twoAppended⟩ :=
    DepartureCoverage.foldlM electra exitCap (ExitRateBelow config exitCap)
    (fun _ _ _ ok good => attesterSlashing_indexedTrace electra early exitCap good ok)
    (fun _ _ _ ok good => ExitRateBelow.of_prefix early
      ⟨(frame_processAttesterSlashing ok).registryGrows, activeStep_processAttesterSlashing ok,
        effectiveKept_attesterSlashing ok⟩ good)
    (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
    (fun _ _ _ ok => effectiveKept_attesterSlashing ok)
    (fun _ _ _ ok => (frame_processAttesterSlashing ok).slot) belowProposed attestedOk
  obtain ⟨three, threeFrom, threeTrace, threeCoverage, threeRates, threeAppended⟩ :=
    voluntaryExits_indexedTrace electra early exitCap belowDeposited exitedOk
  have proposedSlot :=
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposedOk).slot
  have attestedSlot :=
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processAttesterSlashing ok) attestedOk).slot
  have votedSlot :=
    (Frame.foldlM (fun _ _ _ ok => frame_processAttestation ok) votedOk).slot
  have depositedSlot :=
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processDeposit ok) depositedOk).slot
  have proposedEpoch : getCurrentEpoch proposed = getCurrentEpoch s := by
    simp only [getCurrentEpoch, proposedSlot]
  have depositedEpoch : getCurrentEpoch deposited = getCurrentEpoch s := by
    simp only [getCurrentEpoch, depositedSlot, votedSlot, attestedSlot, proposedSlot]
  rw [proposedEpoch] at twoFrom
  rw [depositedEpoch] at threeFrom
  have firstLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok) proposedOk
  have secondLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok) attestedOk
  have votesLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processAttestation ok) votedOk
  have depositsLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processDeposit ok) depositedOk
  have exitsLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok) exitedOk
  have votesData : voted.validators = attested.validators :=
    foldlM_ok_invariant (fun t => t.validators = attested.validators)
      (fun _ _ _ kept ok => (processAttestation_registry ok).1.trans kept) rfl votedOk
  have depositsCoverage := DepartureCoverage.empty_fold
    (fun _ _ _ ok => deposit_coverage electra ok)
    (fun _ _ _ ok => registryLifecycle_processDeposit ok) depositedOk
  have both := oneCoverage.append_of_effectiveKept twoCoverage firstLife secondLife
    (effectiveKept_fold (fun _ _ _ ok => effectiveKept_proposerSlashing ok)
      (fun _ _ _ ok => (registryLifecycle_processProposerSlashing ok).size_le) proposedOk)
  have middle := (both.suffix_of_empty (.of_data (congrArg (·.data) votesData))
    (firstLife.trans secondLife) votesLife).suffix_of_empty depositsCoverage
      ((firstLife.trans secondLife).trans votesLife) depositsLife
  have balances := effectiveKept_trans
    (effectiveKept_fold (fun _ _ _ ok => effectiveKept_proposerSlashing ok)
      (fun _ _ _ ok => (registryLifecycle_processProposerSlashing ok).size_le) proposedOk)
    (effectiveKept_trans
      (effectiveKept_fold (fun _ _ _ ok => effectiveKept_attesterSlashing ok)
        (fun _ _ _ ok => (registryLifecycle_processAttesterSlashing ok).size_le) attestedOk)
      (effectiveKept_trans (effectiveKept_data (congrArg (·.data) votesData))
        (effectiveKept_fold (fun _ _ _ ok => effectiveKept_processDeposit ok)
          (fun _ _ _ ok => (registryLifecycle_processDeposit ok).size_le) depositedOk)
        votesLife.size_le) secondLife.size_le) firstLife.size_le
  have prefixCoverage := middle.append_of_effectiveKept threeCoverage
    (((firstLife.trans secondLife).trans votesLife).trans depositsLife) exitsLife balances
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  simp only [processBlsToExecutionChanges, capella, ↓reduceDIte,
    ← Array.foldlM_toList] at changedOk
  have changesLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changedOk
  have changesCoverage := DepartureCoverage.empty_fold
    (fun _ _ _ ok => credentials_coverage ok)
    (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changedOk
  have votesFrame : departureQueues electra voted = departureQueues electra attested :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra attested)
      (fun _ _ _ kept ok => (attestation_departureQueues electra ok).trans kept) rfl votedOk
  have depositsFrame : departureQueues electra deposited = departureQueues electra voted :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra voted)
      (fun _ _ _ kept ok => (deposit_departureQueues electra ok).trans kept) rfl depositedOk
  have changesFrame : departureQueues electra changed = departureQueues electra exited :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra exited)
      (fun _ _ _ kept ok => (credentials_departureQueues electra ok).trans kept) rfl changedOk
  refine ⟨(one ++ two) ++ three, (oneFrom.append twoFrom).append threeFrom,
    prefixCoverage.suffix_of_empty changesCoverage
    ((((firstLife.trans secondLife).trans votesLife).trans depositsLife).trans exitsLife)
    changesLife, ?_, ?_, ?_, ?_,
    (((oneAppended.append twoAppended).kept_right
      (congrArg (fun q => q.2.2.2.2) (depositsFrame.trans votesFrame))).append
        threeAppended).kept_right (congrArg (fun q => q.2.2.2.2) changesFrame)⟩
  · have middleEpoch := congrArg Prod.fst (depositsFrame.trans votesFrame)
    have middleBalance := congrArg (fun q => q.2.1) (depositsFrame.trans votesFrame)
    have lastEpoch := congrArg Prod.fst changesFrame
    have lastBalance := congrArg (fun q => q.2.1) changesFrame
    change deposited.earliestExitEpoch electra = attested.earliestExitEpoch electra at middleEpoch
    change deposited.exitBalanceToConsume electra = attested.exitBalanceToConsume electra
      at middleBalance
    change changed.earliestExitEpoch electra = exited.earliestExitEpoch electra at lastEpoch
    change changed.exitBalanceToConsume electra = exited.exitBalanceToConsume electra at lastBalance
    rw [middleEpoch, middleBalance] at threeTrace
    rw [lastEpoch, lastBalance, List.map_append, List.map_append]
    exact (oneTrace.append twoTrace).append threeTrace
  · intro called member
    rcases List.mem_append.mp member with member | member
    · exact (List.mem_append.mp member).elim (oneRates called) (twoRates called)
    · exact threeRates called member
  · exact ((((firstLife.trans secondLife).trans votesLife).trans depositsLife).trans
      exitsLife).trans changesLife
  · exact effectiveKept_trans balances
      (effectiveKept_trans
        (effectiveKept_fold (fun _ _ _ ok => effectiveKept_voluntaryExit ok)
          (fun _ _ _ ok => (registryLifecycle_processVoluntaryExit ok).size_le) exitedOk)
        (effectiveKept_fold (fun _ _ _ ok => effectiveKept_blsChange ok)
          (fun _ _ _ ok => (registryLifecycle_processBlsToExecutionChange ok).size_le) changedOk)
        exitsLife.size_le)
      (((firstLife.trans secondLife).trans votesLife).trans depositsLife).size_le

/-- The block prefix reaches execution requests before any consolidation queue call. -/
private def blockConsolidationSites {fork : Fork} (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) :
    Except TransitionError (List (ForkedBeaconState preset)) := do
  if electra : .pectra ≤ fork ∧ fork < .glamsterdam then
    have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra.1
    have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
    let parentSlot := state.latestBlockHeader.slot
    let state ← processBlockHeader state block
    let state ← processBlockExecution config checks engine state block.body bellatrix
    let state ← processRandao config checks state block.body
    let state ← processEth1Data before state block.body
    let expected ← expectedDepositCount state before
    let deposits := (block.body.deposits before).data
    ensure (deposits.size = expected) (.wrongDepositCount deposits.size expected)
    let state ← block.body.proposerSlashings.data.foldlM
      (processProposerSlashing config checks) state
    let state ← block.body.attesterSlashings.data.foldlM
      (processAttesterSlashing config checks) state
    let state ← block.body.attestations.data.foldlM
      (processAttestation config checks · parentSlot ·) state
    let state ← deposits.foldlM (processDeposit config checks before) state
    let state ← block.body.voluntaryExits.data.foldlM (processVoluntaryExit config checks) state
    let state ← processBlsToExecutionChanges config checks state block.body
    let requests := block.body.executionRequests electra
    let state ← requests.deposits.data.foldlM (processDepositRequest · electra.1 ·) state
    let state ← requests.withdrawals.data.foldlM
      (processWithdrawalRequest config · electra.1 ·) state
    return (← consolidationRequestsSites config electra.1 state
      requests.consolidations.data.toList).2
  else return []

private theorem slashing_consolidationFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  obtain ⟨exited, initiated, frame⟩ := slashValidator_departureQueues electra ok
  exact (congrArg (fun q => q.2.2) frame).trans
    (initiateExit_consolidationFrame electra initiated)

private theorem proposerSlashing_consolidationFrame {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashing_consolidationFrame electra slashed

private theorem attesterSlashing_consolidationFrame {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, flag⟩, foldedOk, ok⟩ := ok
  simp only [pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  refine foldlM_ok_invariant
    (fun pair => (departureQueues electra pair.1).2.2 = (departureQueues electra s).2.2)
    ?_ rfl foldedOk
  intro ⟨a, firstFlag⟩ index ⟨b, lastFlag⟩ kept stepped
  simp only [slashIfSlashable, bind_ok_iff] at stepped
  obtain ⟨_, _, stepped⟩ := stepped
  split at stepped
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at stepped
    obtain ⟨_, slashed, rfl, _⟩ := stepped
    exact (slashing_consolidationFrame electra slashed).trans kept
  · cases stepped; exact kept

/-- A withdrawal request keeps the consolidation queue, and may add a partial withdrawal. -/
private theorem withdrawalRequest_consolidationFrame {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork) {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    ((departureQueues electra t).2.2.1, (departureQueues electra t).2.2.2.1) =
      ((departureQueues electra s).2.2.1, (departureQueues electra s).2.2.2.1) := by
  rcases withdrawalRequest_cases ok with rfl | ⟨index, _, _, initiated⟩ | ⟨index, v, owed, _, paid⟩
  · rfl
  · have frame := initiateExit_consolidationFrame electra initiated
    rw [frame]
  · simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok] at paid
    obtain ⟨_, _, _, _, paid⟩ := paid
    split at paid
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at paid
      obtain ⟨⟨queued, epoch⟩, called, _, _, _, _, rfl⟩ := paid
      have frame := exitUpdate_consolidationFrame electra called
      change ((departureQueues electra queued).2.2.1, (departureQueues electra queued).2.2.2.1) = _
      rw [frame]
    · cases paid; rfl

private theorem epoch_consolidationFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processEpoch config checks s = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  apply (processEpoch_trace ok).transport
    (fun a b => (departureQueues electra b).2.2 = (departureQueues electra a).2.2)
    (fun _ => rfl) (fun one two => two.trans one)
  intro k _ a b computed
  have edge := EpochStage.action_cases.mp computed
  cases k
  case registry =>
    simp only [EpochStage.Edge, processRegistryUpdates, electra, ↓reduceIte,
      bind_ok_iff] at edge
    obtain ⟨_, _, entries⟩ := edge
    refine foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra a).2.2)
      ?_ rfl entries
    intro c index d kept stepped
    rcases registryEntry_departureQueues electra stepped with frame | ⟨_, initiated⟩
    · exact (congrArg (fun q => q.2.2) frame).trans kept
    · exact (initiateExit_consolidationFrame electra initiated).trans kept
  all_goals exact congrArg (fun q => q.2.2) (epochStage_departureQueues electra early edge nofun)

/-- The number of queued partial withdrawals that a block reads.

Its withdrawals are those that the state after its header expects, from Capella on. -/
private def blockPartialsTaken {fork : Fork} (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) : Nat :=
  if capella : .shapella ≤ fork then
    (((processBlockHeader state block >>= (getExpectedWithdrawals · capella)).toOption).map
      (·.processedPartialWithdrawalsCount.toNat)).getD 0
  else 0

private theorem block_indexedTrace_sites {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) (cap exitCap : Nat)
    (below : ExitRateBelow config exitCap s)
    (rates : ∀ sites, blockConsolidationSites config checks engine s block = .ok sites →
      ∀ site ∈ sites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ sites, blockConsolidationSites config checks engine s block = .ok sites ∧
    ∃ exits consolidations : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch s).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        (exits ++ consolidations) ∧
      DepartureCoverage s t (exits ++ consolidations) ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (exits.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ exitCap) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations sites ∧
      (∀ called ∈ consolidations, called.entry = none) ∧
      blockPartialsTaken s block ≤ (s.pendingPartialWithdrawals electra).data.size ∧
      (t.pendingPartialWithdrawals electra).data.toList =
        (s.pendingPartialWithdrawals electra).data.toList.drop (blockPartialsTaken s block) ++
          exits.filterMap (·.entry) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  obtain ⟨voted, operated, started, operatedOk, -, syncedOk⟩ := processBlock_operationsInput ok
  have headData := started.validators_eq early
  obtain ⟨parented, headed, executed, revealed, paidOk, headedOk, executedOk, revealedOk,
    votedOk⟩ := started
  simp only [notGloas, bellatrix, before, altair, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at paidOk executedOk votedOk syncedOk
  subst paidOk
  simp only [processOperations, notGloas, electra, ↓reduceDIte,
    bind_ok_iff, ensure_ok_iff] at operatedOk
  obtain ⟨expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
    votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
    requestsOk⟩ := operatedOk
  have requestsLife := registryLifecycle_processExecutionRequests requestsOk
  simp only [processExecutionRequests, bind_ok_iff] at requestsOk
  obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidatedOk⟩ := requestsOk
  obtain ⟨sites, replayed⟩ := consolidationRequestsSites_result
    (by simpa only [← Array.foldlM_toList] using consolidatedOk)
  have ensured : ensure ((block.body.deposits before).data.size = expected)
      (TransitionError.wrongDepositCount (block.body.deposits before).data.size expected) =
        .ok () := ensure_ok_iff.mpr count
  -- The replay reaches the same withdrawal output before recording consolidation sites.
  have recorded : blockConsolidationSites config checks engine s block = .ok sites := by
    rw [blockConsolidationSites, dite_eq_left ⟨electra, early⟩]
    simp only [headedOk, executedOk, revealedOk, votedOk, expectedOk, ensured,
      proposedOk, attestedOk, votedAttOk, depositedOk, exitedOk, changedOk,
      requestedOk, withdrawnOk, replayed, pure, Except.pure, bind, Except.bind]
  rw [← Array.foldlM_toList] at proposedOk attestedOk votedAttOk depositedOk exitedOk
  rw [← Array.foldlM_toList] at requestedOk withdrawnOk consolidatedOk
  have belowVoted : ExitRateBelow config exitCap voted :=
    ExitRateBelow.of_prefix early (blockHead_sitePrefix headedOk executedOk revealedOk votedOk)
      below
  have belowChanged : ExitRateBelow config exitCap changed :=
    ExitRateBelow.of_prefix early (operations_prefix_site_prefixes electra proposedOk attestedOk
      votedAttOk depositedOk exitedOk changedOk).2.2 belowVoted
  obtain ⟨first, firstFrom, firstCoverage, firstTrace, firstRates, firstLife, firstBalances,
    firstAppended⟩ :=
    operationsPrefix_coverage electra early exitCap belowVoted proposedOk attestedOk
      votedAttOk depositedOk exitedOk changedOk
  obtain ⟨exits, consolidations, requestsFrom, covered, exitTrace, consolidationTrace,
    exitRates, consolidationRates, consolidationSites, requestsAppended, consolidationEntries⟩ :=
    executionRequests_coverage_sites electra early requestedOk withdrawnOk consolidatedOk
      replayed cap exitCap belowChanged (rates sites recorded)
  have headSlot : voted.slot = s.slot :=
    (frame_processEth1Data votedOk).slot.trans
      ((frame_processRandao revealedOk).slot.trans
        ((frame_processBlockExecution executedOk).slot.trans
          (frame_processBlockHeader headedOk).slot))
  have prefixSlot : changed.slot = voted.slot := by
    have one :=
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposedOk).slot
    have two :=
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processAttesterSlashing ok) attestedOk).slot
    have three := (Frame.foldlM (fun _ _ _ ok => frame_processAttestation ok) votedAttOk).slot
    have four := (BlockFrame.foldlM (fun _ _ _ ok => frame_processDeposit ok) depositedOk).slot
    have five :=
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processVoluntaryExit ok) exitedOk).slot
    simp only [processBlsToExecutionChanges, capella, ↓reduceDIte,
      ← Array.foldlM_toList] at changedOk
    exact (BlockFrame.foldlM
      (fun _ _ _ ok => frame_processBlsToExecutionChange ok) changedOk).slot.trans
      (five.trans (four.trans (three.trans (two.trans one))))
  have headEpoch : getCurrentEpoch voted = getCurrentEpoch s := by
    simp only [getCurrentEpoch, headSlot]
  have prefixEpoch : getCurrentEpoch changed = getCurrentEpoch s := by
    simp only [getCurrentEpoch, prefixSlot, headSlot]
  rw [headEpoch] at firstFrom
  rw [prefixEpoch] at requestsFrom
  have requestedFrame : departureQueues electra requested = departureQueues electra changed :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra changed)
      (fun _ _ _ kept ok => (depositRequest_departureQueues electra ok).trans kept)
      rfl requestedOk
  have withdrawnFrame : ((departureQueues electra withdrawn).2.2.1,
      (departureQueues electra withdrawn).2.2.2.1) =
      ((departureQueues electra requested).2.2.1, (departureQueues electra requested).2.2.2.1) :=
    foldlM_ok_invariant
      (fun t => ((departureQueues electra t).2.2.1, (departureQueues electra t).2.2.2.1) =
        ((departureQueues electra requested).2.2.1, (departureQueues electra requested).2.2.2.1))
      (fun _ _ _ kept ok => (withdrawalRequest_consolidationFrame electra ok).trans kept)
      rfl withdrawnOk
  have operatedFrame : operated.earliestExitEpoch electra = withdrawn.earliestExitEpoch electra ∧
      operated.exitBalanceToConsume electra = withdrawn.exitBalanceToConsume electra :=
    foldlM_ok_invariant (fun t =>
      t.earliestExitEpoch electra = withdrawn.earliestExitEpoch electra ∧
      t.exitBalanceToConsume electra = withdrawn.exitBalanceToConsume electra)
      (fun _ _ _ kept ok =>
        let frame := consolidationRequest_exitFrame electra ok
        ⟨frame.1.trans kept.1, frame.2.1.trans kept.2⟩) ⟨rfl, rfl⟩ consolidatedOk
  have prefixFrame : (departureQueues electra changed).2.2 =
      (departureQueues electra voted).2.2 := by
    have one := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (proposerSlashing_consolidationFrame electra ok).trans kept) rfl proposedOk
    have two := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (attesterSlashing_consolidationFrame electra ok).trans kept) one attestedOk
    have three := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (congrArg (fun q => q.2.2) (attestation_departureQueues electra ok)).trans kept)
      two votedAttOk
    have four := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (congrArg (fun q => q.2.2) (deposit_departureQueues electra ok)).trans kept)
      three depositedOk
    have five := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (initiateExit_consolidationFrame electra (processVoluntaryExit_initiates ok)).trans kept)
      four exitedOk
    simp only [processBlsToExecutionChanges, capella, ↓reduceDIte,
      ← Array.foldlM_toList] at changedOk
    exact foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (congrArg (fun q => q.2.2) (credentials_departureQueues electra ok)).trans kept)
      five changedOk
  obtain ⟨planned, plannedOk, executedFrame⟩ :=
    ((blockExecution_departureQueues electra executedOk).resolve_right
      fun ⟨g, _⟩ => Nat.not_le_of_lt early g).2
  have headFrame := blockHead_departureQueues electra headedOk executedFrame revealedOk votedOk
  have taken : blockPartialsTaken s block = planned.processedPartialWithdrawalsCount.toNat := by
    simp [blockPartialsTaken, capella, headedOk, plannedOk, Except.toOption, bind, Except.bind]
  have headQueue :
      headed.pendingPartialWithdrawals electra = s.pendingPartialWithdrawals electra := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    rfl
  obtain ⟨_, synced⟩ := processSyncAggregate_eq syncedOk
  have tailFrame : departureQueues electra t = departureQueues electra operated := by
    rw [synced]
    rfl
  have operatedCoverage : DepartureCoverage voted operated
      ((first ++ exits) ++ consolidations) := by
    simpa only [List.append_assoc] using
      firstCoverage.append_of_effectiveKept covered firstLife requestsLife firstBalances
  have tailData : t.validators = operated.validators := by rw [synced]
  refine ⟨sites, recorded, first ++ exits, consolidations, ?_, ?_, ?_, ?_, ?_, consolidationRates,
    consolidationSites, consolidationEntries, ?_, ?_⟩
  · simpa only [List.append_assoc] using firstFrom.append requestsFrom
  · intro i old next a b
    apply operatedCoverage i old next
    · simpa only [headData] using a
    · simpa only [tailData] using b
  · have requestedEpoch := congrArg Prod.fst requestedFrame
    have requestedBalance := congrArg (fun q => q.2.1) requestedFrame
    change requested.earliestExitEpoch electra = changed.earliestExitEpoch electra
      at requestedEpoch
    change requested.exitBalanceToConsume electra = changed.exitBalanceToConsume electra
      at requestedBalance
    rw [requestedEpoch, requestedBalance] at exitTrace
    have linked := firstTrace.append exitTrace
    have firstEpoch := congrArg Prod.fst headFrame
    have firstBalance := congrArg (fun q => q.2.1) headFrame
    have lastEpoch := congrArg Prod.fst tailFrame
    have lastBalance := congrArg (fun q => q.2.1) tailFrame
    change voted.earliestExitEpoch electra = s.earliestExitEpoch electra at firstEpoch
    change voted.exitBalanceToConsume electra = s.exitBalanceToConsume electra at firstBalance
    change t.earliestExitEpoch electra = operated.earliestExitEpoch electra at lastEpoch
    change t.exitBalanceToConsume electra = operated.exitBalanceToConsume electra at lastBalance
    rw [firstEpoch, firstBalance] at linked
    rw [List.map_append, lastEpoch, lastBalance, operatedFrame.1, operatedFrame.2]
    exact linked
  · have initial := withdrawnFrame.trans
      ((congrArg (fun q => (q.2.2.1, q.2.2.2.1)) requestedFrame).trans
        ((congrArg (fun p => (p.1, p.2.1)) prefixFrame).trans
          (congrArg (fun q => (q.2.2.1, q.2.2.2.1)) headFrame)))
    have firstEpoch := congrArg Prod.fst initial
    have firstBalance := congrArg Prod.snd initial
    have lastEpoch := congrArg (fun q => q.2.2.1) tailFrame
    have lastBalance := congrArg (fun q => q.2.2.2.1) tailFrame
    change withdrawn.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra
      at firstEpoch
    change withdrawn.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra
      at firstBalance
    change t.earliestConsolidationEpoch electra = operated.earliestConsolidationEpoch electra
      at lastEpoch
    change t.consolidationBalanceToConsume electra = operated.consolidationBalanceToConsume electra
      at lastBalance
    rw [firstEpoch, firstBalance] at consolidationTrace
    rw [lastEpoch, lastBalance]
    exact consolidationTrace
  · intro called member
    exact (List.mem_append.mp member).elim (firstRates called) (exitRates called)
  · rw [taken, ← headQueue]
    exact (getExpectedWithdrawals_bounds plannedOk).2.2.1 electra
  · have last := congrArg (fun q => q.2.2.2.2.toList) tailFrame
    have head := congrArg (fun q => q.2.2.2.2.toList) headFrame
    change (t.pendingPartialWithdrawals electra).data.toList =
      (operated.pendingPartialWithdrawals electra).data.toList at last
    change (voted.pendingPartialWithdrawals electra).data.toList =
      ((s.pendingPartialWithdrawals electra).data.extract
        planned.processedPartialWithdrawalsCount.toNat
        (s.pendingPartialWithdrawals electra).data.size).toList at head
    rw [last, requestsAppended, firstAppended, head, taken, List.filterMap_append,
      List.append_assoc]
    simp

/-- The states at which a block reads the consolidation churn limit, in order. -/
@[no_expose] def _root_.EthLib.Consensus.Step.consolidationSites {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : List (ForkedBeaconState preset) :=
  match step with
  | .slot _ => []
  | .block engine signed _ _ =>
    ((blockConsolidationSites config checks engine x.state signed.message).toOption).getD []

/-- The states at which the blocks of a run read the consolidation churn limit, in order. -/
def _root_.EthLib.Consensus.Run.consolidationSites {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List (ForkedBeaconState preset)
  | _, .nil => []
  | _, .snoc pre step => pre.consolidationSites ++ step.consolidationSites

/-- The number of queued partial withdrawals that a step reads. -/
private def _root_.EthLib.Consensus.Step.partialsTaken {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : Nat :=
  match step with
  | .slot _ => 0
  | .block _ signed _ _ => blockPartialsTaken x.state signed.message

/-- The number of queued partial withdrawals that the steps of a run read. -/
private def _root_.EthLib.Consensus.Run.partialsTaken {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → Nat
  | _, .nil => 0
  | _, .snoc pre step => pre.partialsTaken + step.partialsTaken

/-- The queued partial withdrawals that a step reads: the front of the queue at its start.

A block reads them after its header, which keeps the queue. -/
private def _root_.EthLib.Consensus.Step.partialsRemoved {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : List PendingPartialWithdrawal :=
  if electra : .pectra ≤ x.fork then
    (x.state.pendingPartialWithdrawals electra).data.toList.take step.partialsTaken
  else []

/-- The queued partial withdrawals that the steps of a run read, in order. -/
private def _root_.EthLib.Consensus.Run.partialsRemoved {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List PendingPartialWithdrawal
  | _, .nil => []
  | _, .snoc pre step => pre.partialsRemoved ++ step.partialsRemoved

/-- The consolidation sites of two runs in turn are those of the first, then the second. -/
private theorem _root_.EthLib.Consensus.Run.consolidationSites_append
    {a b c : ForkedBeaconState preset} (one : Run config checks a b)
    (two : Run config checks b c) :
    (one.append two).consolidationSites = one.consolidationSites ++ two.consolidationSites := by
  induction two with
  | nil => simp [Run.append, Run.consolidationSites]
  | snoc two step ih => simp only [Run.append, Run.consolidationSites, ih, List.append_assoc]

private theorem slot_consolidationFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : advanceSlot config checks s = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, cached, cache, stepped, advance, rfl⟩ := ok
  have cachedFrame : (departureQueues electra cached).2.2 =
      (departureQueues electra s).2.2 := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
    rfl
  change (departureQueues electra stepped).2.2 = (departureQueues electra s).2.2
  unfold epochIfLast at advance
  split at advance
  · exact (epoch_consolidationFrame electra early advance).trans cachedFrame
  · cases advance; exact cachedFrame

/-- A request that grows the pending consolidations records its input state as a site. -/
private theorem consolidationRequestsSites_mem {fork : Fork} (electra : .pectra ≤ fork)
    {s mid next last : BeaconState preset fork} {sites : List (ForkedBeaconState preset)}
    {pre rest : List ConsolidationRequest} {request : ConsolidationRequest}
    (ok : consolidationRequestsSites config electra s (pre ++ request :: rest) =
      .ok (last, sites))
    (reached : pre.foldlM (processConsolidationRequest config · electra ·) s = .ok mid)
    (stepped : processConsolidationRequest config mid electra request = .ok next)
    (grows : (next.pendingConsolidations electra).data.size ≠
      (mid.pendingConsolidations electra).data.size) :
    (⟨fork, mid⟩ : ForkedBeaconState preset) ∈ sites := by
  induction pre generalizing s sites last with
  | nil =>
    cases reached
    simp only [List.nil_append, consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨here, recorded, _, _, ⟨_, _⟩, _, _, rfl⟩ := ok
    simp only [consolidationRequestSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at recorded
    obtain ⟨called, classified, rfl⟩ := recorded
    cases called with
    | true => simp
    | false =>
      exact absurd (congrArg (·.size)
        (consolidationRequest_notCalled_frames electra stepped classified).2) grows
  | cons head tail ih =>
    simp only [List.cons_append, consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨_, _, middle, headOk, ⟨_, later⟩, replayed, _, rfl⟩ := ok
    simp only [List.foldlM_cons, headOk, bind, Except.bind] at reached
    exact List.mem_append_right _ (ih replayed reached)

/-- Only a consolidation request that schedules its source moves the consolidation queue.

Each other block operation keeps the consolidation epoch and balance of the queue. -/
theorem consolidationQueue_dispatch {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork} :
    let Kept := t.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra ∧
      t.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra
    ((∃ (engine : ExecutionEngine preset fork) (block : BeaconBlock preset fork),
        OperationsInput config checks engine s block t) → Kept) ∧
    ((∃ slashing, processProposerSlashing config checks s slashing = .ok t) → Kept) ∧
    ((∃ slashing, processAttesterSlashing config checks s slashing = .ok t) → Kept) ∧
    ((∃ parentSlot attestation,
        processAttestation config checks s parentSlot attestation = .ok t) → Kept) ∧
    ((∃ (before : fork < .hegota) (deposit : Deposit),
        processDeposit config checks before s deposit = .ok t) → Kept) ∧
    ((∃ exit, processVoluntaryExit config checks s exit = .ok t) → Kept) ∧
    ((∃ change, processBlsToExecutionChange config checks s change = .ok t) → Kept) ∧
    ((∃ request, processDepositRequest s electra request = .ok t) → Kept) ∧
    ((∃ request, processWithdrawalRequest config s electra request = .ok t) → Kept) ∧
    ((∃ (altair : .altair ≤ fork) (aggregate : SyncAggregate preset),
        processSyncAggregate config checks s altair aggregate = .ok t) → Kept) ∧
    -- A request returns its state, switches credentials, or schedules its source.
    (∀ request, processConsolidationRequest config s electra request = .ok t →
      t = s ∨ (∃ index, switchToCompoundingValidator s electra index = .ok t) ∨
        ∃ (sourceIndex targetIndex : ValidatorIndex) (source : Validator),
          getValidator s sourceIndex = .ok source ∧
          queueConsolidation config s electra sourceIndex source targetIndex = .ok t) ∧
    -- A credential switch keeps the queue.
    (∀ index, switchToCompoundingValidator s electra index = .ok t → Kept) ∧
    -- A scheduled source always makes one queue call.
    (∀ (sourceIndex targetIndex : ValidatorIndex) (source : Validator),
      queueConsolidation config s electra sourceIndex source targetIndex = .ok t →
      ∃ call : DepartureQueueCall,
        call.amount = source.effectiveBalance ∧
        -- The call reads its input and churn rate before the request.
        call.earliest = s.earliestConsolidationEpoch electra ∧
        call.available = s.consolidationBalanceToConsume electra ∧
        call.epoch = t.earliestConsolidationEpoch electra ∧
        call.left = t.consolidationBalanceToConsume electra ∧
        getConsolidationChurnLimit config s = .ok call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first ∧
        ∃ next, getValidator t sourceIndex = .ok next ∧ next.exitEpoch = call.epoch) := by
  intro Kept
  -- Each frame below equates the consolidation part of the departure queues.
  have kept (frame : (departureQueues electra t).2.2 = (departureQueues electra s).2.2) :
      Kept := ⟨congrArg Prod.fst frame, congrArg (fun q => q.2.1) frame⟩
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  refine ⟨?_, fun ⟨_, ok⟩ => kept (proposerSlashing_consolidationFrame electra ok),
    fun ⟨_, ok⟩ => kept (attesterSlashing_consolidationFrame electra ok),
    fun ⟨_, _, ok⟩ => kept (congrArg (·.2.2) (attestation_departureQueues electra ok)),
    fun ⟨_, _, ok⟩ => kept (congrArg (·.2.2) (deposit_departureQueues electra ok)),
    fun ⟨_, ok⟩ => kept (initiateExit_consolidationFrame electra
      (processVoluntaryExit_initiates ok)),
    fun ⟨_, ok⟩ => kept (congrArg (·.2.2) (credentials_departureQueues electra ok)),
    fun ⟨_, ok⟩ => kept (congrArg (·.2.2) (depositRequest_departureQueues electra ok)),
    fun ⟨_, ok⟩ => ?_, fun ⟨_, _, ok⟩ => ?_, fun _ ok => ?_,
    fun _ ok => kept (congrArg (·.2.2) (switchToCompounding_departureQueues electra ok)),
    fun _ _ _ ok => queueConsolidation_call electra ok⟩
  · rintro ⟨engine, block, parented, headed, executed, revealed, paidOk, headedOk, executedOk,
      revealedOk, votedOk⟩
    simp only [notGloas, bellatrix, before, ↓reduceDIte, pure, Except.pure,
      Except.ok.injEq] at paidOk executedOk votedOk
    subst paidOk
    obtain ⟨planned, _, executedFrame⟩ :=
      ((blockExecution_departureQueues electra executedOk).resolve_right
        fun ⟨g, _⟩ => Nat.not_le_of_lt early g).2
    have frame := blockHead_departureQueues electra headedOk executedFrame revealedOk votedOk
    refine ⟨(congrArg (fun q => q.2.2.1) frame).trans ?_,
      (congrArg (fun q => q.2.2.2.1) frame).trans ?_⟩ <;> rfl
  · have frame := withdrawalRequest_consolidationFrame electra ok
    exact ⟨congrArg Prod.fst frame, congrArg Prod.snd frame⟩
  · obtain ⟨_, rfl⟩ := processSyncAggregate_eq ok
    exact ⟨rfl, rfl⟩
  · rcases consolidationRequest_cases ok with same | ⟨index, _, _, switched⟩ |
      ⟨sourceIndex, source, targetIndex, _, accepted, queued⟩
    · exact .inl same
    · exact .inr (.inl ⟨index, switched⟩)
    · exact .inr (.inr ⟨sourceIndex, targetIndex, source,
        getValidator_eq_ok_iff.mpr accepted.sourceAt, queued⟩)

/-- A slot step keeps the consolidation queue, across its epoch and its fork upgrades. -/
theorem advanceSlotAcross_consolidationQueue {u v : ForkedBeaconState preset}
    (electra : .pectra ≤ u.fork) (target : .pectra ≤ v.fork) (early : v.fork < .glamsterdam)
    (ok : advanceSlotAcross config checks u = .ok v) :
    v.state.earliestConsolidationEpoch target = u.state.earliestConsolidationEpoch electra ∧
      v.state.consolidationBalanceToConsume target =
        u.state.consolidationBalanceToConsume electra := by
  have sourceEarly := Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  obtain ⟨frame, _, _, _⟩ := upgrades_departureQueues (s := ⟨u.fork, advanced⟩)
    electra early upgraded target
  have both := (congrArg (fun q => q.2.2) frame).trans
    (slot_consolidationFrame electra sourceEarly advancedOk)
  exact ⟨congrArg Prod.fst both, congrArg (fun q => q.2.1) both⟩

/-- A request that grows the pending consolidations runs at a site of its block.

The premises are the operations of the block, in order, up to the request. -/
theorem Step.consolidationSites_of_request {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    {before : fork < .hegota} {expected : Nat}
    {input proposed attested voted deposited exited changed requested withdrawn consolidated mid
      next : BeaconState preset fork}
    {pre rest : List ConsolidationRequest} {request : ConsolidationRequest}
    (inputOk : OperationsInput config checks engine s signed.message input)
    (expectedOk : expectedDepositCount input before = .ok expected)
    (count : (signed.message.body.deposits before).data.size = expected)
    (proposedOk : signed.message.body.proposerSlashings.data.foldlM
      (processProposerSlashing config checks) input = .ok proposed)
    (attestedOk : signed.message.body.attesterSlashings.data.foldlM
      (processAttesterSlashing config checks) proposed = .ok attested)
    (votedOk : signed.message.body.attestations.data.foldlM
      (processAttestation config checks · s.latestBlockHeader.slot ·) attested = .ok voted)
    (depositedOk : (signed.message.body.deposits before).data.foldlM
      (processDeposit config checks before) voted = .ok deposited)
    (exitedOk : signed.message.body.voluntaryExits.data.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited)
    (changedOk : processBlsToExecutionChanges config checks exited signed.message.body =
      .ok changed)
    (requestedOk : (signed.message.body.executionRequests ⟨electra, early⟩).deposits.data.foldlM
      (processDepositRequest · electra ·) changed = .ok requested)
    (withdrawnOk :
      (signed.message.body.executionRequests ⟨electra, early⟩).withdrawals.data.foldlM
        (processWithdrawalRequest config · electra ·) requested = .ok withdrawn)
    (consolidatedOk :
      (signed.message.body.executionRequests ⟨electra, early⟩).consolidations.data.toList.foldlM
        (processConsolidationRequest config · electra ·) withdrawn = .ok consolidated)
    (split : (signed.message.body.executionRequests ⟨electra, early⟩).consolidations.data.toList =
      pre ++ request :: rest)
    (reached : pre.foldlM (processConsolidationRequest config · electra ·) withdrawn = .ok mid)
    (stepped : processConsolidationRequest config mid electra request = .ok next)
    (grows : (next.pendingConsolidations electra).data.size ≠
      (mid.pendingConsolidations electra).data.size) :
    (⟨fork, mid⟩ : ForkedBeaconState preset) ∈
      (Step.block (checks := checks) engine signed due ok).consolidationSites := by
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  obtain ⟨parented, headed, executed, revealed, paidOk, headedOk, executedOk, revealedOk,
    inputOk⟩ := inputOk
  simp only [notGloas, bellatrix, before, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at paidOk executedOk inputOk
  subst paidOk
  -- The request list of the block, run from the withdrawal output, records the sites.
  obtain ⟨sites, replayed⟩ := consolidationRequestsSites_result consolidatedOk
  have ensured : ensure ((signed.message.body.deposits before).data.size = expected)
      (TransitionError.wrongDepositCount (signed.message.body.deposits before).data.size
        expected) = .ok () := ensure_ok_iff.mpr count
  -- The site replay of the block reaches the same withdrawal output.
  have recorded : blockConsolidationSites config checks engine s signed.message =
      .ok sites := by
    rw [blockConsolidationSites, dite_eq_left ⟨electra, early⟩]
    simp only [headedOk, executedOk, revealedOk, inputOk, expectedOk, ensured,
      proposedOk, attestedOk, votedOk, depositedOk, exitedOk, changedOk,
      requestedOk, withdrawnOk, replayed, pure, Except.pure, bind, Except.bind]
  change _ ∈ ((blockConsolidationSites config checks engine s signed.message).toOption).getD []
  rw [recorded]
  rw [split] at replayed
  exact consolidationRequestsSites_mem electra replayed reached stepped grows

/-- One step's indexed calls trace both departure queues with exit churn at most `exitCap`. -/
private theorem step_indexedTrace_sites_cap {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap exitCap : Nat)
    (below : ExitRateBelow config exitCap x.state)
    (rates : ∀ site ∈ step.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch x.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        (exits ++ consolidations) ∧
      DepartureCoverage x.state y.state (exits ++ consolidations) ∧
      DepartureQueueTrace (x.state.earliestExitEpoch electra)
        (x.state.exitBalanceToConsume electra) (exits.map (·.call))
        (y.state.earliestExitEpoch targetElectra) (y.state.exitBalanceToConsume targetElectra) ∧
      DepartureQueueTrace (x.state.earliestConsolidationEpoch electra)
        (x.state.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (y.state.earliestConsolidationEpoch targetElectra)
        (y.state.consolidationBalanceToConsume targetElectra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ exitCap) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations step.consolidationSites ∧
      (∀ called ∈ consolidations, called.entry = none) ∧
      step.partialsTaken ≤ (x.state.pendingPartialWithdrawals electra).data.size ∧
      (y.state.pendingPartialWithdrawals targetElectra).data.toList =
        (x.state.pendingPartialWithdrawals electra).data.toList.drop step.partialsTaken ++
          exits.filterMap (·.entry) := by
  have sourceEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    obtain ⟨frame, data, _, _⟩ := upgrades_departureQueues (s := ⟨x.fork, advanced⟩)
      electra early upgraded targetElectra
    obtain ⟨calls, firsts, trace, covered, exitRates, appended⟩ :=
      slot_indexedTrace electra sourceEarly exitCap below advancedOk
    have consolidationFrame := slot_consolidationFrame electra sourceEarly advancedOk
    have first := congrArg Prod.fst frame
    have left := congrArg (fun q => q.2.1) frame
    change y.state.earliestExitEpoch targetElectra = advanced.earliestExitEpoch electra at first
    change y.state.exitBalanceToConsume targetElectra = advanced.exitBalanceToConsume electra
      at left
    refine ⟨calls, [], ?_, ?_, ?_, ?_, exitRates, by simp,
      by simp [ConsolidationCallSites], by simp, Nat.zero_le _, ?_⟩
    · simpa only [List.append_nil] using firsts
    · simpa only [List.append_nil] using
        (show DepartureCoverage x.state y.state calls from fun i old next before after =>
          covered i old next before (by simpa only [data] using after))
    · rw [first, left]
      exact trace
    · have both := (congrArg (fun q => q.2.2) frame).trans consolidationFrame
      have epoch := congrArg Prod.fst both
      have balance := congrArg (fun q => q.2.1) both
      change y.state.earliestConsolidationEpoch targetElectra =
        x.state.earliestConsolidationEpoch electra at epoch
      change y.state.consolidationBalanceToConsume targetElectra =
        x.state.consolidationBalanceToConsume electra at balance
      rw [epoch, balance]
      exact .nil _ _
    · have kept := congrArg (fun q => q.2.2.2.2.toList) frame
      change (y.state.pendingPartialWithdrawals targetElectra).data.toList =
        (advanced.pendingPartialWithdrawals electra).data.toList at kept
      rw [kept, appended]
      rfl
  | block engine signed due ok =>
    have processed := (applySignedBlock_ok ok).2.1
    obtain ⟨sites, recorded, traced⟩ := block_indexedTrace_sites electra early processed cap
      exitCap below
      (by
        intro sites recorded site member h rate computed
        apply rates site ?_ h rate computed
        simpa only [Step.consolidationSites, recorded, Except.toOption, Option.getD_some] using
          member)
    simpa only [Step.consolidationSites, Step.partialsTaken, recorded, Except.toOption,
      Option.getD_some] using traced

private theorem step_indexedTrace_sites {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap : Nat)
    (rates : ∀ site ∈ step.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch x.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        (exits ++ consolidations) ∧
      DepartureCoverage x.state y.state (exits ++ consolidations) ∧
      DepartureQueueTrace (x.state.earliestExitEpoch electra)
        (x.state.exitBalanceToConsume electra) (exits.map (·.call))
        (y.state.earliestExitEpoch targetElectra) (y.state.exitBalanceToConsume targetElectra) ∧
      DepartureQueueTrace (x.state.earliestConsolidationEpoch electra)
        (x.state.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (y.state.earliestConsolidationEpoch targetElectra)
        (y.state.consolidationBalanceToConsume targetElectra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations step.consolidationSites ∧
      (∀ called ∈ consolidations, called.entry = none) ∧
      step.partialsTaken ≤ (x.state.pendingPartialWithdrawals electra).data.size ∧
      (y.state.pendingPartialWithdrawals targetElectra).data.toList =
        (x.state.pendingPartialWithdrawals electra).data.toList.drop step.partialsTaken ++
          exits.filterMap (·.entry) :=
  step_indexedTrace_sites_cap step electra early targetElectra cap _
    (ExitRateBelow.of_max (Nat.lt_of_le_of_lt step.chainStep.fork_le early) x.state) rates

/-- A run's indexed calls trace both departure queues with exit churn at most `exitCap`. -/
private theorem run_indexedTrace_sites_cap {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap exitCap : Nat)
    (exitSteps : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → ExitRateBelow config exitCap u.state)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch x.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        (exits ++ consolidations) ∧
      (∀ charge ∈ tail.departureCharges, ∃ called ∈ exits ++ consolidations,
        called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
          called.call.amount.toNat = charge.amount) ∧
      DepartureQueueTrace (x.state.earliestExitEpoch electra)
        (x.state.exitBalanceToConsume electra) (exits.map (·.call))
        (y.state.earliestExitEpoch targetElectra) (y.state.exitBalanceToConsume targetElectra) ∧
      DepartureQueueTrace (x.state.earliestConsolidationEpoch electra)
        (x.state.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (y.state.earliestConsolidationEpoch targetElectra)
        (y.state.consolidationBalanceToConsume targetElectra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ exitCap) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations tail.consolidationSites ∧
      (∀ called ∈ consolidations, called.entry = none) ∧
      tail.partialsRemoved.length = tail.partialsTaken ∧
      tail.partialsRemoved ++ (y.state.pendingPartialWithdrawals targetElectra).data.toList =
        (x.state.pendingPartialWithdrawals electra).data.toList ++
          exits.filterMap (·.entry) := by
  induction tail with
  | nil =>
    exact ⟨[], [], by simp [DepartureCallsFrom], by simp [Run.departureCharges],
      .nil _ _, .nil _ _, by simp, by simp, by simp [ConsolidationCallSites], by simp,
      by simp [Run.partialsRemoved, Run.partialsTaken], by simp [Run.partialsRemoved]⟩
  | @snoc middle last pre step ih =>
    have middleElectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    obtain ⟨firstExits, firstConsolidations, firstFrom, firstMatched, firstExitTrace,
      firstConsolidationTrace, firstExitRates, firstConsolidationRates, firstSites,
      firstEntries, firstBound, firstQueue⟩ := ih
        (Nat.lt_of_le_of_lt step.chainStep.fork_le early) middleElectra
        (fun {u w} step' contained => exitSteps step' (.earlier contained step))
        (fun site member h rate computed =>
          rates site (List.mem_append_left _ member) h rate computed)
    obtain ⟨lastExits, lastConsolidations, lastFrom, covered, lastExitTrace,
      lastConsolidationTrace, lastExitRates, lastConsolidationRates, lastSites,
      lastEntries, lastBound, lastQueue⟩ :=
      step_indexedTrace_sites_cap step middleElectra early targetElectra cap exitCap
        (exitSteps step (.last pre step))
        (fun site member h rate computed =>
          rates site (List.mem_append_right _ member) h rate computed)
    rw [← Array.length_toList] at lastBound
    have removed : step.partialsRemoved =
        (middle.state.pendingPartialWithdrawals middleElectra).data.toList.take
          step.partialsTaken := by
      unfold Step.partialsRemoved
      split
      · rfl
      · contradiction
    refine ⟨firstExits ++ lastExits, firstConsolidations ++ lastConsolidations,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have ordered := UInt64.le_iff_toNat_le.mp
        (currentEpoch_le_of_chainSteps pre.chainSteps)
      have lastFrom := DepartureCallsFrom.mono
        (start := (getCurrentEpoch x.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        lastFrom (by omega)
      intro called member
      simp only [List.mem_append] at member
      rcases member with (one | two) | (three | four)
      · exact firstFrom called (List.mem_append_left _ one)
      · exact lastFrom called (List.mem_append_left _ two)
      · exact firstFrom called (List.mem_append_right _ three)
      · exact lastFrom called (List.mem_append_right _ four)
    · intro charge member
      rcases List.mem_append.mp member with earlier | latest
      · obtain ⟨called, present, paired⟩ := firstMatched charge earlier
        refine ⟨called, ?_, paired⟩
        simp only [List.mem_append] at present ⊢
        exact present.elim (fun h => .inl (.inl h)) (fun h => .inr (.inl h))
      · obtain ⟨called, present, paired⟩ := covered.step_charges step charge latest
        refine ⟨called, ?_, paired⟩
        simp only [List.mem_append] at present ⊢
        exact present.elim (fun h => .inl (.inr h)) (fun h => .inr (.inr h))
    · simpa only [List.map_append] using firstExitTrace.append lastExitTrace
    · simpa only [List.map_append] using firstConsolidationTrace.append lastConsolidationTrace
    · intro called member
      exact (List.mem_append.mp member).elim (firstExitRates called) (lastExitRates called)
    · intro called member
      exact (List.mem_append.mp member).elim
        (firstConsolidationRates called) (lastConsolidationRates called)
    · intro called member
      rcases List.mem_append.mp member with first | last
      · obtain ⟨site, present, paired⟩ := firstSites called first
        exact ⟨site, List.mem_append_left _ present, paired⟩
      · obtain ⟨site, present, paired⟩ := lastSites called last
        exact ⟨site, List.mem_append_right _ present, paired⟩
    · intro called member
      exact (List.mem_append.mp member).elim (firstEntries called) (lastEntries called)
    · simp only [Run.partialsRemoved, Run.partialsTaken, removed, List.length_append,
        List.length_take, firstBound]
      omega
    · rw [Run.partialsRemoved, removed, lastQueue, List.filterMap_append, List.append_assoc,
        ← List.append_assoc (List.take _ _), List.take_append_drop, ← List.append_assoc,
        firstQueue, List.append_assoc]

private theorem run_indexedTrace_sites {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap : Nat)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List (IndexedDepartureCall preset config),
      DepartureCallsFrom ((getCurrentEpoch x.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat)
        (exits ++ consolidations) ∧
      (∀ charge ∈ tail.departureCharges, ∃ called ∈ exits ++ consolidations,
        called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
          called.call.amount.toNat = charge.amount) ∧
      DepartureQueueTrace (x.state.earliestExitEpoch electra)
        (x.state.exitBalanceToConsume electra) (exits.map (·.call))
        (y.state.earliestExitEpoch targetElectra) (y.state.exitBalanceToConsume targetElectra) ∧
      DepartureQueueTrace (x.state.earliestConsolidationEpoch electra)
        (x.state.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (y.state.earliestConsolidationEpoch targetElectra)
        (y.state.consolidationBalanceToConsume targetElectra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations tail.consolidationSites ∧
      (∀ called ∈ consolidations, called.entry = none) ∧
      tail.partialsRemoved.length = tail.partialsTaken ∧
      tail.partialsRemoved ++ (y.state.pendingPartialWithdrawals targetElectra).data.toList =
        (x.state.pendingPartialWithdrawals electra).data.toList ++
          exits.filterMap (·.entry) :=
  run_indexedTrace_sites_cap tail electra early targetElectra cap _
    (fun {u _} _ contained =>
      let ⟨_, _, _, uEarly, _⟩ := Apriori.Internal.Run.contains_step_facts contained early
      ExitRateBelow.of_max uEarly u.state) rates

/-- The entries of the calls hold the amounts of the calls with no index. -/
private theorem partials_entries_sum (calls : List (IndexedDepartureCall preset config)) :
    ((calls.filterMap (·.entry)).map (·.amount.toNat)).sum =
      ((calls.filter (·.index.isNone)).map (·.call.amount.toNat)).sum := by
  induction calls with
  | nil => rfl
  | cons called rest ih =>
    cases entry : called.entry with
    | none =>
      have indexed : called.index.isNone = false := by
        cases index : called.index with
        | none => simpa [entry] using called.tagged.mp index
        | some _ => rfl
      simp [entry, indexed, ih]
    | some pending =>
      have unindexed : called.index = none := called.tagged.mpr (by simp [entry])
      simp [entry, unindexed, ih,
        (called.pushed pending entry).1]

/-- The departure calls in the window fit the queue budget with exit churn at most `exitCap`. -/
private theorem exit_calls_le_window_electra_cap {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high cap exitCap : Nat)
    (exitSteps : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → ExitRateBelow config exitCap u.state)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ calls : List (IndexedDepartureCall preset config),
      (∀ charge ∈ tail.departureCharges, ∃ called ∈ calls,
        called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
          called.call.amount.toNat = charge.amount) ∧
      (∀ targetElectra : .pectra ≤ y.fork,
        tail.partialsRemoved.length = tail.partialsTaken ∧
        tail.partialsRemoved ++ (y.state.pendingPartialWithdrawals targetElectra).data.toList =
          (x.state.pendingPartialWithdrawals electra).data.toList ++
            calls.filterMap (·.entry)) ∧
      (tail.partialsRemoved.map (·.amount.toNat)).sum ≤
        ((x.state.pendingPartialWithdrawals electra).data.toList.map (·.amount.toNat)).sum +
          ((calls.filter (·.index.isNone)).map (·.call.amount.toNat)).sum ∧
      ((calls.filter fun c => c.call.epoch.toNat ≤ high + 1).map
          fun c => c.call.amount.toNat).sum ≤
        (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
          (x.state.exitBalanceToConsume electra).toNat else 0) +
        (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
          (x.state.consolidationBalanceToConsume electra).toNat else 0) +
        (high + 2 - max (getCurrentEpoch x.state).toNat
          (x.state.earliestExitEpoch electra).toNat) *
          exitCap +
        (high + 2 - max (getCurrentEpoch x.state).toNat
          (x.state.earliestConsolidationEpoch electra).toNat) * cap := by
  have targetElectra := Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)
  obtain ⟨exits, consolidations, firsts, matched, exitTrace, consolidationTrace,
    exitRates, consolidationRates, -, entries, bound, queue⟩ :=
    run_indexedTrace_sites_cap tail electra early targetElectra cap exitCap exitSteps rates
  have unqueued : consolidations.filterMap (·.entry) = [] :=
    List.filterMap_eq_nil_iff.mpr entries
  refine ⟨exits ++ consolidations, matched, fun _ => ?_, ?_, ?_⟩
  · rw [List.filterMap_append, unqueued, List.append_nil]
    exact ⟨bound, queue⟩
  · have sums := congrArg (fun l => (l.map (·.amount.toNat)).sum) queue
    simp only [List.map_append, List.sum_append] at sums
    rw [← partials_entries_sum, List.filterMap_append, unqueued, List.append_nil]
    omega
  have queueBound {calls : List (IndexedDepartureCall preset config)} {first last : Epoch}
      {available left : Gwei}
      (trace : DepartureQueueTrace first available (calls.map (·.call)) last left) (cap : Nat)
      (rates : ∀ called ∈ calls, called.call.rate.toNat ≤ cap)
      (firsts : DepartureCallsFrom
        ((getCurrentEpoch x.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat) calls) :
      ((calls.filter fun called => called.call.epoch.toNat ≤ high + 1).map
        fun called => called.call.amount.toNat).sum ≤
          (if first.toNat ≤ high + 1 then available.toNat else 0) +
            (high + 2 - max (getCurrentEpoch x.state).toNat first.toNat) * cap := by
    have budget := trace.window_le_from (getCurrentEpoch x.state).toNat (high + 1) cap
      (by
        intro call member
        obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
        exact rates called present)
      (by
        intro call member
        obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
        have first := firsts called present
        omega)
    simpa only [List.filter_map, List.map_map, Function.comp_def,
      Nat.add_assoc, Nat.reduceAdd] using budget
  have exitBound := queueBound exitTrace exitCap exitRates
    (fun called member => firsts called (List.mem_append_left _ member))
  have consolidationBound := queueBound consolidationTrace cap consolidationRates
    (fun called member => firsts called (List.mem_append_right _ member))
  simp only [List.filter_append, List.map_append, List.sum_append]
  omega

/-- The exit-queue calls of a run from Electra, and their spending in a window, before Gloas. -/
private theorem exit_calls_le_window_electra {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high cap : Nat)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    -- The calls carry the registry index of each departure, or no index for a partial withdrawal.
    --
    -- A call with no index carries the entry it queues for its amount.
    --
    -- That entry is due from the epoch of the call plus the delay.
    ∃ calls : List (IndexedDepartureCall preset config),
      -- Each departure charge is a call with its index, its exit epoch and its amount.
      (∀ charge ∈ tail.departureCharges, ∃ called ∈ calls,
        called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
          called.call.amount.toNat = charge.amount) ∧
      -- The blocks of the run read entries from the front of the queue of partial withdrawals.
      --
      -- Those entries, then the queue at `y`, are the queue at `x`, then the entries of the calls.
      (∀ targetElectra : .pectra ≤ y.fork,
        tail.partialsRemoved.length = tail.partialsTaken ∧
        tail.partialsRemoved ++ (y.state.pendingPartialWithdrawals targetElectra).data.toList =
          (x.state.pendingPartialWithdrawals electra).data.toList ++
            calls.filterMap (·.entry)) ∧
      -- So each entry read is pending at `x`, or is the entry of its own call with no index.
      --
      -- That call has the amount of the entry.
      (tail.partialsRemoved.map (·.amount.toNat)).sum ≤
        ((x.state.pendingPartialWithdrawals electra).data.toList.map (·.amount.toNat)).sum +
          ((calls.filter (·.index.isNone)).map (·.call.amount.toNat)).sum ∧
      -- Calls with an epoch at most `high + 1` spend at most the carry and the churn of the queues.
      --
      -- That bound counts departures and partial withdrawals together.
      ((calls.filter fun c => c.call.epoch.toNat ≤ high + 1).map
          fun c => c.call.amount.toNat).sum ≤
        (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
          (x.state.exitBalanceToConsume electra).toNat else 0) +
        (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
          (x.state.consolidationBalanceToConsume electra).toNat else 0) +
        -- The churn of each queue counts each epoch from where that queue opens.
        (high + 2 - max (getCurrentEpoch x.state).toNat
          (x.state.earliestExitEpoch electra).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (high + 2 - max (getCurrentEpoch x.state).toNat
          (x.state.earliestConsolidationEpoch electra).toNat) * cap :=
  exit_calls_le_window_electra_cap tail electra early high cap _
    (fun {u _} _ contained =>
      let ⟨_, _, _, uEarly, _⟩ := Apriori.Internal.Run.contains_step_facts contained early
      ExitRateBelow.of_max uEarly u.state) rates

/-- Post-Electra departures spend only carry-in capacity and eligible epochs in the window.

The exit churn limit at the input of each step of the run is at most `exitCap`.

The exit queue then adds at most `exitCap` for each epoch of the window. -/
theorem departure_charges_le_window_electra_cap {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high cap exitCap : Nat)
    (exitRates : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → ∀ rate : Gwei,
        exitChurnLimit config u.state = .ok rate → rate.toNat ≤ exitCap)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
        (x.state.exitBalanceToConsume electra).toNat else 0) +
      (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
        (x.state.consolidationBalanceToConsume electra).toNat else 0) +
      (high + 2 - max (getCurrentEpoch x.state).toNat (x.state.earliestExitEpoch electra).toNat) *
        exitCap +
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (x.state.earliestConsolidationEpoch electra).toNat) * cap := by
  obtain ⟨calls, matched, -, -, bound⟩ :=
    exit_calls_le_window_electra_cap tail electra early high cap exitCap exitRates rates
  exact (departureCharges_le_calls (departureCharges_run_indices tail) matched (high + 1)).trans
    bound

/-- Post-Electra departures spend only carry-in capacity and eligible epochs in the window. -/
private theorem departure_charges_le_window_electra {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high cap : Nat)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
        (x.state.exitBalanceToConsume electra).toNat else 0) +
      (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
        (x.state.consolidationBalanceToConsume electra).toNat else 0) +
      (high + 2 - max (getCurrentEpoch x.state).toNat (x.state.earliestExitEpoch electra).toNat) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (x.state.earliestConsolidationEpoch electra).toNat) * cap :=
  departure_charges_le_window_electra_cap tail electra early high cap _
    (fun {_ _} _ contained _ computed =>
      let ⟨_, _, _, uEarly, _⟩ := Apriori.Internal.Run.contains_step_facts contained early
      exitChurnLimit_le_cap uEarly computed) rates

/-- Every finite exit cohort holds at most the larger of its base count and a cap.

A tail reads the base from its reference state, whose cohorts a tail cannot bound. -/
private def ExitCohortsBounded {fork : Fork} (base : Epoch → Nat) (cap : Nat)
    (s : BeaconState preset fork) : Prop :=
  ∀ epoch : Epoch, epoch ≠ FAR_FUTURE_EPOCH →
    s.validators.data.toList.countP (·.exitEpoch == epoch) ≤ max (base epoch) cap

private structure CountCohortStep {f h : Fork} (config : Config) (bound : Nat)
    (s : BeaconState preset f) (t : BeaconState preset h) : Prop where
  grows : s.validators.data.size ≤ t.validators.data.size
  bounded : ∀ base, ExitCohortsBounded base (max 1 (cohortCap config bound)) s →
    ExitCohortsBounded base (max 1 (cohortCap config bound)) t
  epochs : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat
  future : ∀ (i : Nat) (old next : Validator), s.validators.data[i]? = some old →
    t.validators.data[i]? = some next → next.exitEpoch = old.exitEpoch ∨
      (getCurrentEpoch s).toNat ≤ next.exitEpoch.toNat

private theorem CountCohortStep.refl {f : Fork} (s : BeaconState preset f) (bound : Nat) :
    CountCohortStep config bound s s :=
  ⟨Nat.le_refl _, fun _ => id, Nat.le_refl _, fun _ _ _ before after =>
    .inl (congrArg Validator.exitEpoch (Option.some.inj (after.symm.trans before)))⟩

private theorem CountCohortStep.trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k} {bound : Nat}
    (one : CountCohortStep config bound s t) (two : CountCohortStep config bound t u) :
    CountCohortStep config bound s u := by
  refine ⟨one.grows.trans two.grows,
    fun base capped => two.bounded base (one.bounded base capped),
    one.epochs.trans two.epochs, ?_⟩
  intro i old next before after
  have inside := (Array.getElem?_eq_some_iff.mp before).1
  have middleInside := Nat.lt_of_lt_of_le inside one.grows
  have middleFound : t.validators.data[i]? = some t.validators.data[i] := by
    simp [middleInside]
  rcases two.future i _ next middleFound after with same | later
  · rcases one.future i old _ before middleFound with earlier | later
    · exact .inl (same.trans earlier)
    · exact .inr (by rw [same]; exact later)
  · exact .inr (one.epochs.trans later)

private theorem CountCohortStep.data {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (bound : Nat)
    (same : t.validators.data = s.validators.data := by rfl)
    (epochs : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat := by exact Nat.le_refl _) :
    CountCohortStep config bound s t := by
  constructor
  · exact Nat.le_of_eq (congrArg Array.size same.symm)
  · intro _ capped epoch finite
    simpa only [same] using capped epoch finite
  · exact epochs
  · intro i old next before after
    rw [same] at after
    exact .inl (congrArg Validator.exitEpoch (Option.some.inj (after.symm.trans before)))

private theorem CountCohortStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {action : BeaconState preset f → α → Except ε (BeaconState preset f)} {items : List α}
    {bound : Nat} (kept : ∀ a item b, action a item = .ok b → CountCohortStep config bound a b)
    (ok : items.foldlM action s = .ok t) : CountCohortStep config bound s t :=
  foldlM_ok_invariant (CountCohortStep config bound s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s bound) ok

/-- A step that keeps the slot and activity keeps the number of active validators. -/
private theorem activeCount_eq_of_activeStep {f : Fork} {s t : BeaconState preset f}
    (step : ActiveStep s t) : activeCount t = activeCount s := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, step.1]
  unfold activeCount
  rw [epoch, step.2.getActiveValidatorIndices_eq (getCurrentEpoch_le_activityFixedEpoch s)]

/-- A step that keeps activity, and keeps the cohorts bounded when its input count is bounded.

The count then stays bounded at every later input, so the exits of a fold can read it. -/
private def CountedStep {f : Fork} (config : Config) (bound : Nat)
    (s t : BeaconState preset f) : Prop :=
  ActiveStep s t ∧ (activeCount s ≤ bound → CountCohortStep config bound s t)

private theorem CountedStep.refl {f : Fork} (s : BeaconState preset f) (bound : Nat) :
    CountedStep config bound s s :=
  ⟨ActiveStep.refl s, fun _ => .refl s bound⟩

private theorem CountedStep.trans {f : Fork} {s t u : BeaconState preset f} {bound : Nat}
    (one : CountedStep config bound s t) (two : CountedStep config bound t u) :
    CountedStep config bound s u :=
  ⟨one.1.trans two.1, fun counted => (one.2 counted).trans
    (two.2 (by rw [activeCount_eq_of_activeStep one.1]; exact counted))⟩

private theorem CountedStep.fold {f : Fork} {s t : BeaconState preset f} {α ε : Type}
    {action : BeaconState preset f → α → Except ε (BeaconState preset f)} {items : List α}
    {bound : Nat} (kept : ∀ a item b, action a item = .ok b → CountedStep config bound a b)
    (ok : items.foldlM action s = .ok t) : CountedStep config bound s t :=
  foldlM_ok_invariant (CountedStep config bound s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s bound) ok

private theorem CountedStep.of_validators {f : Fork} {s t : BeaconState preset f} (bound : Nat)
    (same : t.validators = s.validators) (slot : t.slot = s.slot) :
    CountedStep config bound s t :=
  ⟨ActiveStep.of_validators (congrArg (·.data) same) slot, fun _ =>
    .data bound (congrArg (·.data) same)
      (by simp only [getCurrentEpoch, slot]; exact Nat.le_refl _)⟩

private theorem CountCohortStep.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v w : Validator} (bound : Nat) (found : getValidatorAt s i = .ok v)
    (room : w.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch ≠ w.exitEpoch →
      s.validators.data.toList.countP (·.exitEpoch == w.exitEpoch) <
        max 1 (cohortCap config bound))
    (ok : s.setValidatorAt i w = .ok t)
    (placed : w.exitEpoch = v.exitEpoch ∨ (getCurrentEpoch s).toNat ≤ w.exitEpoch.toNat) :
    CountCohortStep config bound s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok ok
  have read := getValidatorAt_eq_ok_iff.mp found
  have atIndex : s.validators.data[i] = v := by
    rw [Array.getElem?_eq_getElem inside] at read
    exact Option.some.inj read
  constructor
  · simp [BeaconState.putValidator]
  · intro base capped epoch finite
    have oldBound := capped epoch finite
    change (s.validators.data.set i w).toList.countP (·.exitEpoch == epoch) ≤ _
    rw [Array.toList_set, List.countP_set (by simpa using inside)]
    simp only [Array.getElem_toList, atIndex]
    by_cases same : w.exitEpoch = epoch
    · subst epoch
      by_cases previous : v.exitEpoch = w.exitEpoch
      · have positive := List.boole_getElem_le_countP
          (p := fun validator : Validator => validator.exitEpoch == w.exitEpoch)
          (l := s.validators.data.toList) (i := i) (by simpa using inside)
        simp only [Array.getElem_toList, atIndex, previous, beq_self_eq_true,
          ↓reduceIte] at positive ⊢
        omega
      · have room := room finite previous
        have wide := Nat.le_max_right (base w.exitEpoch) (max 1 (cohortCap config bound))
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
    · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, ↓reduceIte]
      omega
  · exact Nat.le_refl _
  · intro j old next before after
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.getElem?_set] at after
    split at after
    · rename_i same
      subst j
      have oldSame := Option.some.inj (read.symm.trans before)
      have nextSame := Option.some.inj after
      subst old next
      exact placed
    · exact .inl (congrArg Validator.exitEpoch (Option.some.inj (after.symm.trans before)))

private theorem CountCohortStep.setExitUnchanged {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v w : Validator} (bound : Nat) (found : getValidatorAt s i = .ok v)
    (ok : s.setValidatorAt i w = .ok t) (same : w.exitEpoch = v.exitEpoch) :
    CountCohortStep config bound s t :=
  .setValidatorAt bound found (fun _ different => False.elim (different same.symm)) ok
    (.inl same)

private theorem CountCohortStep.exit {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) (counted : activeCount s ≤ bound) :
    CountCohortStep config bound s t := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact .refl _ bound
  · have queuedSame : queued = s := by
      have notElectra : ¬ .pectra ≤ f := Nat.not_le_of_lt early
      simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at queue
      obtain ⟨_, _, same, _⟩ := queue
      exact same.symm
    subst queued
    rw [getValidator_eq_getValidatorAt] at found
    rw [setValidator_eq_setValidatorAt] at set
    apply CountCohortStep.setValidatorAt bound
      found _ set
    · exact .inr (by have later := exitQueue_lt queue; dsimp only; omega)
    · intro finite _
      simpa only [List.countP_eq_length_filter] using
        (exitQueue_count_room early queue finite bound counted).2

private theorem CountCohortStep.increase {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {index amount : UInt64} (ok : increaseBalance s index amount = .ok t) :
    CountCohortStep config bound s t :=
  .data bound (congrArg (·.data) (increaseBalance_validators ok))
    (by simp only [getCurrentEpoch, (frame_increaseBalance ok).slot]; exact Nat.le_refl _)

private theorem CountCohortStep.decrease {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {index amount : UInt64} (ok : decreaseBalance s index amount = .ok t) :
    CountCohortStep config bound s t :=
  .data bound (congrArg (·.data) (decreaseBalance_validators ok))
    (by simp only [getCurrentEpoch, (frame_decreaseBalance ok).slot]; exact Nat.le_refl _)

private theorem CountCohortStep.slash {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {index : ValidatorIndex}
    {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) (counted : activeCount s ≤ bound) :
    CountCohortStep config bound s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  have first := (CountCohortStep.exit early bound exited counted).trans
    (CountCohortStep.setExitUnchanged bound found set rfl)
  have second := (CountCohortStep.decrease (config := config) bound lowered).trans
    ((CountCohortStep.increase bound raised).trans (CountCohortStep.increase bound paid))
  have total := first.trans ((CountCohortStep.data bound (s := marked)
    (t := { marked with slashings })).trans second)
  split
  · exact total.trans (.data bound rfl)
  · exact total

private theorem CountCohortStep.add {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    CountCohortStep config bound s t := by
  have data := addValidatorToRegistry_validators_eq_push ok
  constructor
  · simp [data]
  · intro _ capped epoch finite
    simpa [data, getValidatorFromDeposit, Ne.symm finite] using capped epoch finite
  · simp only [getCurrentEpoch, addValidatorToRegistry_slot ok]
    exact Nat.le_refl _
  · intro i old next before after
    have inside := (Array.getElem?_eq_some_iff.mp before).1
    have kept : t.validators.data[i]? = some old := by
      simpa [data, Array.getElem?_push, Nat.ne_of_lt inside] using before
    exact .inl (congrArg Validator.exitEpoch (Option.some.inj (after.symm.trans kept)))

private theorem CountCohortStep.deposit {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    CountCohortStep config bound s t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact .refl _ bound
  · exact .increase bound raised
  · exact .add bound added

private theorem CountCohortStep.processDeposit {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    CountCohortStep config bound s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  have notElectra : ¬ .pectra ≤ f := Nat.not_le_of_lt early
  simp only [applyDeposit, notElectra, ↓reduceDIte] at credited
  exact (CountCohortStep.data bound (s := s)
    (t := { s with eth1DepositIndex := fun _ => next })).trans (.deposit bound credited)

private theorem CountedStep.registryEntry {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {index : Nat}
    (ok : updateRegistryEntry config s index = .ok t) : CountedStep config bound s t := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have same : queued.exitEpoch = v.exitEpoch ∧ queued.activationEpoch = v.activationEpoch := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      exact ⟨rfl, rfl⟩
    · cases queue; exact ⟨rfl, rfl⟩
  -- The queue for activation keeps the activation and exit epochs, so activity is kept.
  have first : CountedStep config bound s marked :=
    ⟨activeStep_setValidatorAt found
      (fun _ _ => by simp only [isActiveValidator, same.1, same.2]) set,
      fun _ => CountCohortStep.setExitUnchanged bound found set same.1⟩
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact first.trans ⟨activeStep_initiateValidatorExit exited, .exit early bound exited⟩
  · cases ok; exact first

private theorem CountCohortStep.activate {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {index : ValidatorIndex} (ok : activateValidator s index = .ok t) :
    CountCohortStep config bound s t := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, set⟩ := ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  exact .setExitUnchanged bound found set rfl

private theorem CountedStep.registry {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) (ok : processRegistryUpdates config s = .ok t) :
    CountedStep config bound s t := by
  refine ⟨activeStep_processRegistryUpdates early ok, fun counted => ?_⟩
  have notElectra : ¬ .pectra ≤ f := Nat.not_le_of_lt early
  simp only [processRegistryUpdates, notElectra, ↓reduceIte, bind_ok_iff] at ok
  obtain ⟨_, updated, activated⟩ := ok
  exact ((CountedStep.fold (fun _ _ _ => CountedStep.registryEntry early bound) updated).2
    counted).trans (.fold (fun _ _ _ => CountCohortStep.activate bound) activated)

private theorem CountCohortStep.proposerSlashing {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t)
    (counted : activeCount s ≤ bound) : CountCohortStep config bound s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact .slash early bound slashed counted

private theorem CountCohortStep.attesterSlashing {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t)
    (counted : activeCount s ≤ bound) : CountCohortStep config bound s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine (foldlM_ok_invariant (fun step => CountedStep config bound s step.1)
    ?_ (.refl _ bound) folded).2 counted
  intro step i next previous computed
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact previous.trans ⟨activeStep_slashValidator slashed, .slash early bound slashed⟩
  · cases computed; exact previous

private theorem CountCohortStep.blsChange {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    CountCohortStep config bound s t := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  exact .setExitUnchanged bound found set rfl

private theorem CountCohortStep.effective {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) (ok : processEffectiveBalanceUpdates s = .ok t) :
    CountCohortStep config bound s t := by
  unfold processEffectiveBalanceUpdates at ok
  refine CountCohortStep.fold (fun _ _ _ computed => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, found, _, _, _, _, set⟩ := computed
  exact .setExitUnchanged bound found set rfl

private theorem CountedStep.epoch {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) (ok : processEpoch config checks s = .ok t) :
    CountedStep config bound s t := by
  apply (processEpoch_trace ok).transport (CountedStep config bound)
    (fun a => .refl a bound) (fun one two => one.trans two)
  intro k _ a b computed
  have edge := EpochStage.action_cases.mp computed
  cases k
  case registry => exact .registry early bound edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact absurd ‹_› (Nat.not_le_of_lt early)
    · subst edge
      exact .refl _ bound
  case effectiveBalances =>
    exact ⟨activeStep_processEffectiveBalanceUpdates edge, fun _ => .effective bound edge⟩
  all_goals
    exact .of_validators bound (edge.validators_eq ⟨nofun, nofun, nofun⟩) (edge.slot_eq)

private theorem CountedStep.block {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (ok : processBlock config checks engine s block = .ok t) :
    CountedStep config bound s t := by
  have notElectra : ¬ .pectra ≤ f := Nat.not_le_of_lt early
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt (early.trans (by decide))
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : CountedStep config bound s input :=
    .of_validators bound (started.validators_eq (Nat.lt_trans early (by decide)))
      (frame_operationsInput started).slot
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of (CountedStep config bound) (fun a => .refl a bound)
      (fun one two => one.trans two)
      (fun deposited => ⟨activeStep_processDeposit deposited,
        fun _ => CountCohortStep.processDeposit early bound deposited⟩)
      (fun exited => ⟨activeStep_processVoluntaryExit exited,
        .exit early bound (processVoluntaryExit_initiates exited)⟩)
      (fun changed => ⟨activeStep_processBlsToExecutionChange changed,
        fun _ => CountCohortStep.blsChange bound changed⟩)
      (fun {_ _ _ electra} _ => absurd electra.1 notElectra)
      (fun {_ _ gloas _} _ => absurd gloas notGloas) operated
  have tail : CountedStep config bound last t := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact .of_validators bound rfl rfl
    · cases synced
      exact .refl _ bound
  exact head.trans <|
    (CountedStep.fold (fun _ _ _ slashed => ⟨activeStep_processProposerSlashing slashed,
      CountCohortStep.proposerSlashing early bound slashed⟩) proposersOk).trans <|
    (CountedStep.fold (fun _ _ _ slashed => ⟨activeStep_processAttesterSlashing slashed,
      CountCohortStep.attesterSlashing early bound slashed⟩) slashingsOk).trans <|
    (CountedStep.fold (fun _ _ _ attested => .of_validators bound
      (processAttestation_registry attested).1 (frame_processAttestation attested).slot)
      attestedOk).trans (rest.trans tail)

private theorem CountCohortStep.slot {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) (ok : advanceSlot config checks s = .ok t)
    (counted : activeCount s ≤ bound) : CountCohortStep config bound s t := by
  obtain ⟨next, cached, epoched, sum, cachedOk, advanced, rfl⟩ := advanceSlot_ok ok
  have cachedSame : cached.validators = s.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have cachedSlot := processSlot_slot cachedOk
  have head : CountCohortStep config bound s cached :=
    .data bound (congrArg (·.data) cachedSame)
      (by simp only [getCurrentEpoch, cachedSlot]; exact Nat.le_refl _)
  have middle : CountCohortStep config bound cached epoched ∧ epoched.slot = cached.slot := by
    unfold epochIfLast at advanced
    split at advanced
    · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame advanced
      -- The epoch pass runs at the cached state, which has the registry and slot of `s`.
      have cachedCount : activeCount cached = activeCount s := activeCount_eq_of_activeStep
        (ActiveStep.of_validators (congrArg (·.data) cachedSame) cachedSlot)
      exact ⟨(CountedStep.epoch early bound advanced).2 (cachedCount ▸ counted),
        frame.slot.trans (activeStep_processJustificationAndFinalization justifiedOk).1⟩
    · cases advanced; exact ⟨.refl _ bound, rfl⟩
  apply (head.trans middle.1).trans
  refine CountCohortStep.data bound (s := epoched) (t := { epoched with slot := next }) rfl ?_
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  change epoched.slot.toNat / _ ≤ next.toNat / _
  rw [middle.2, cachedSlot, sum]
  exact Nat.div_le_div_right (Nat.le_succ _)

private theorem CountCohortStep.preActivation {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex} (bound : Nat)
    (ok : queuePreActivation s electra index = .ok t) : CountCohortStep config bound s t := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, balanced, balance, marked, set, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok balance
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  have changed := CountCohortStep.setExitUnchanged (config := config) bound
    (s := s.putBalance index.toNat _ 0) (v := v) (by exact found) set rfl
  exact (CountCohortStep.data bound (s := s)
    (t := s.putBalance index.toNat _ 0)).trans
      (changed.trans (.data bound rfl))

private theorem CountCohortStep.excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : Nat} (bound : Nat)
    (ok : queueCompoundingExcess s electra index = .ok t) : CountCohortStep config bound s t := by
  unfold queueCompoundingExcess at ok
  split at ok
  · split at ok
    · have step := liftAccessor_ok.mp ok
      simp only [queueExcessActiveBalance, bind_ok_iff] at step
      obtain ⟨_, _, step⟩ := step
      split at step
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
        obtain ⟨_, _, _, _, _, set, rfl⟩ := step
        obtain ⟨_, rfl⟩ := setBalance_ok set
        exact .data bound rfl
      · cases step; exact .refl _ bound
    · cases ok; exact .refl _ bound
  · cases ok; exact .refl _ bound

private theorem CountCohortStep.upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}} (bound : Nat)
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) :
    CountCohortStep config bound s.state t.val.state := by
  have epochs : (getCurrentEpoch s.state).toNat ≤ (getCurrentEpoch t.val.state).toNat := by
    simp only [getCurrentEpoch, (upgradeFrame_upgradeNext ok).slot]
    exact Nat.le_refl _
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact .data bound (upgradeToAltair_spec upgraded).1 epochs
  · subst ok; exact .data bound rfl epochs
  · subst ok; exact .data bound rfl epochs
  · subst ok; exact .data bound rfl epochs
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, _, _, _, _, middle, queued, compounded⟩ := upgraded
    have one := CountCohortStep.fold (config := config)
      (fun _ _ _ computed => CountCohortStep.preActivation bound computed) queued
    have two := CountCohortStep.fold (config := config)
      (fun _ _ _ computed => CountCohortStep.excess bound computed) compounded
    exact (CountCohortStep.data bound (h := .pectra) (s := state) (t := _) rfl).trans
      (one.trans two)
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact .data bound (upgradeToFulu_spec upgraded).1 epochs
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬ Fork.hegota < Fork.glamsterdam) early)

private theorem CountCohortStep.upgrades {s t : ForkedBeaconState preset} (bound : Nat)
    (ok : processUpgrades config checks s = .ok t) (early : t.fork < .glamsterdam) :
    CountCohortStep config bound s.state t.state := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact (CountCohortStep.upgrade bound nextOk
      (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early)).trans (ih next rest early)
  | case2 s notDue => cases ok; exact .refl _ bound

private theorem CountCohortStep.crossing {s t : ForkedBeaconState preset} (bound : Nat)
    (step : Step config checks s t) (early : s.fork < .pectra)
    (targetEarly : t.fork < .glamsterdam) (counted : activeCount s.state ≤ bound) :
    CountCohortStep config bound s.state t.state := by
  cases step with
  | block engine signed due ok =>
    exact (CountedStep.block early bound (applySignedBlock_ok ok).2.1).2 counted
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact (CountCohortStep.slot early bound slotOk counted).trans
      (CountCohortStep.upgrades bound upgrades targetEarly)

private theorem CountCohortStep.step {s t : ForkedBeaconState preset} (bound : Nat)
    (step : Step config checks s t) (early : t.fork < .pectra)
    (counted : activeCount s.state ≤ bound) :
    CountCohortStep config bound s.state t.state :=
  .crossing bound step (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
    (Nat.lt_trans early (by decide)) counted

/-- A run before Electra keeps the cohorts bounded when each of its steps starts counted. -/
private theorem CountCohortStep.run {s t : ForkedBeaconState preset} (bound : Nat)
    (run : Run config checks s t) (early : t.fork < .pectra)
    (counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      run.Contains step → u.fork < .pectra → activeCount u.state ≤ bound) :
    CountCohortStep config bound s.state t.state := by
  induction run with
  | nil => exact .refl _ bound
  | snoc pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    exact (ih middleEarly fun later member => counted later (.earlier member _)).trans
      (CountCohortStep.step bound step early (counted step (.last _ _) middleEarly))

/-- Before Gloas, a step charges each departure at an exit epoch no earlier than its input epoch.

Before Electra the exit is placed from the current epoch on.

From Electra each charge is a queue call, which starts no earlier than the current epoch. -/
theorem departureCharges_epoch_ge {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam)
    (charge : DepartureCharge) (member : charge ∈ step.departureCharges) :
    (getCurrentEpoch x.state).toNat ≤ charge.epoch := by
  by_cases electra : .pectra ≤ x.fork
  · -- Every rate fits 64 bits, so that cap serves for the consolidation calls.
    obtain ⟨_, _, firsts, covered, -⟩ := step_indexedTrace_sites step electra early
      (Nat.le_trans electra step.chainStep.fork_le) (2 ^ 64)
      (fun _ _ _ rate _ => (UInt64.toNat_lt rate).le)
    obtain ⟨called, present, -, epoch, -⟩ := covered.step_charges step charge member
    have placed := called.call.epoch_ge.2
    have first := firsts called present
    omega
  · obtain ⟨⟨old, i⟩, present, added⟩ := List.mem_filterMap.mp member
    have found : x.state.validators.data[i]? = some old := by
      simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using present
    dsimp only at added
    split at added
    · cases added
    · rename_i next after
      split at added
      · rename_i assigned
        cases Option.some.inj added
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at assigned
        rcases (CountCohortStep.crossing (activeCount x.state) step (Nat.lt_of_not_ge electra)
          early (Nat.le_refl _)).future i old next found after with same | lower
        · exact False.elim (assigned.2 (same.trans assigned.1))
        · exact lower
      · cases added

/-- Each departure charge of a run exits at least the seed lookahead after the next epoch. -/
theorem Run.departureCharges_epoch_ge_start {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) :
    ∀ c ∈ tail.departureCharges,
      (getCurrentEpoch x.state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch := by
  obtain ⟨exits, consolidations, firsts, matched, -⟩ :=
    run_indexedTrace_sites tail electra early
      (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)) (2 ^ 64)
      (fun _ _ _ rate _ => (UInt64.toNat_lt rate).le)
  intro charge member
  obtain ⟨called, present, -, epoch, -⟩ := matched charge member
  have placed := called.call.epoch_ge.2
  have first := firsts called present
  omega

private theorem pre_electra_charge_step_bounds {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (step : Step config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : x.fork < .pectra) (targetEarly : y.fork < .glamsterdam)
    (charge : DepartureCharge) (member : charge ∈ step.departureCharges) :
    (getCurrentEpoch x.state).toNat ≤ charge.epoch ∧
      charge.amount ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
  obtain ⟨⟨old, i⟩, present, added⟩ := List.mem_filterMap.mp member
  have found : x.state.validators.data[i]? = some old := by
    simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using present
  dsimp only at added
  split at added
  · cases added
  · rename_i next after
    split at added
    · rename_i assigned
      cases Option.some.inj added
      have lower := departureCharges_epoch_ge step targetEarly _ member
      have capped := shared.effectiveBalance_capped genesis caps
        old (Array.mem_of_getElem? found)
      have notElectra : ¬ .pectra ≤ x.fork := Nat.not_le_of_lt early
      simp only [withdrawalMaxEffectiveBalance, notElectra, ↓reduceIte] at capped
      exact ⟨lower, UInt64.le_iff_toNat_le.mp capped⟩
    · cases added

private theorem pre_electra_charge_bounds {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : y.fork < .pectra) (charge : DepartureCharge)
    (member : charge ∈ tail.departureCharges) :
    (getCurrentEpoch x.state).toNat ≤ charge.epoch ∧
      charge.amount ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
  induction tail with
  | nil => simp [Run.departureCharges] at member
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    rcases List.mem_append.mp member with earlier | latest
    · exact ih middleEarly earlier
    · have bounds := pre_electra_charge_step_bounds (shared.append pre) step genesis caps
        middleEarly (Nat.lt_trans early (by decide)) charge latest
      exact ⟨(UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)).trans
        bounds.1, bounds.2⟩

/-- The charges of a tail at a finite epoch, with the cohort of `x` there, fit in its cohort at `y`.

A charge names a validator whose exit was unassigned, so it is not in the cohort of `x`. -/
private theorem charge_count_le_cohort {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (epoch : Nat) (finite : epoch ≠ FAR_FUTURE_EPOCH.toNat) :
    tail.departureCharges.countP (fun charge => charge.epoch == epoch) +
      x.state.validators.data.toList.countP (fun v => v.exitEpoch.toNat == epoch) ≤
      y.state.validators.data.toList.countP (fun v => v.exitEpoch.toNat == epoch) := by
  let selected := tail.departureCharges.filter (fun charge => charge.epoch == epoch)
  let cohort {f : Fork} (s : BeaconState preset f) := s.validators.data.toList.zipIdx.filter
    (fun entry => entry.1.exitEpoch.toNat == epoch)
  have count {f : Fork} (s : BeaconState preset f) : (cohort s).length =
      s.validators.data.toList.countP (fun v => v.exitEpoch.toNat == epoch) := by
    dsimp only [cohort]
    rw [← List.countP_eq_length_filter]
    have mapped := List.countP_map (l := s.validators.data.toList.zipIdx)
      (f := Prod.fst) (p := fun v => v.exitEpoch.toNat == epoch)
    simpa only [List.zipIdx_map_fst, Function.comp_def] using mapped.symm
  have positions {f : Fork} (s : BeaconState preset f) : ((cohort s).map Prod.snd).Nodup := by
    have all : (s.validators.data.toList.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range'
    exact (List.filter_sublist.map Prod.snd).nodup all
  have member {f : Fork} {s : BeaconState preset f} {i : Nat}
      (inside : i ∈ (cohort s).map Prod.snd) :
      ∃ v, s.validators.data[i]? = some v ∧ v.exitEpoch.toNat = epoch := by
    obtain ⟨⟨v, j⟩, present, rfl⟩ := List.mem_map.mp inside
    obtain ⟨present, same⟩ := List.mem_filter.mp present
    exact ⟨v, by simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using present,
      by simpa using same⟩
  have unique : (selected.map (·.index) ++ (cohort x.state).map Prod.snd).Nodup := by
    refine List.nodup_append.mpr ⟨((List.filter_sublist).map DepartureCharge.index).nodup
      (departureCharges_run_indices tail), positions x.state, ?_⟩
    intro i chosen j old
    obtain ⟨charge, picked, rfl⟩ := List.mem_map.mp chosen
    obtain ⟨v, found, exit⟩ := member old
    have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => finite (by rw [← exit, far])
    exact tail.departure_charge_ne_of_assigned j v found assigned charge
      (List.mem_filter.mp picked).1
  have subset : selected.map (·.index) ++ (cohort x.state).map Prod.snd ⊆
      (cohort y.state).map Prod.snd := by
    intro i inside
    have located : ∃ v, y.state.validators.data[i]? = some v ∧ v.exitEpoch.toNat = epoch := by
      rcases List.mem_append.mp inside with chosen | old
      · obtain ⟨charge, picked, rfl⟩ := List.mem_map.mp chosen
        obtain ⟨chargeMember, same⟩ := List.mem_filter.mp picked
        obtain ⟨v, found, _, exit⟩ := tail.departure_charge_exit charge chargeMember
        exact ⟨v, found, by simpa [exit] using same⟩
      · obtain ⟨v, found, exit⟩ := member old
        have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => finite (by rw [← exit, far])
        obtain ⟨later, laterFound, kept⟩ := tail.registryLifecycle.validators i v found
        exact ⟨later, laterFound, by rw [kept.exitEpoch assigned]; exact exit⟩
    obtain ⟨v, found, exit⟩ := located
    apply List.mem_map.mpr
    refine ⟨(v, i), List.mem_filter.mpr ⟨?_, by simpa using exit⟩, rfl⟩
    simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using found
  have bound := unique.length_le_of_subset subset
  simp only [List.length_append, List.length_map] at bound
  rw [count x.state, count y.state] at bound
  simpa only [selected, ← List.countP_eq_length_filter] using bound

private theorem charge_window_length_le (charges : List DepartureCharge) (start high cap : Nat)
    (firsts : ∀ charge ∈ charges, start ≤ charge.epoch)
    (counts : ∀ epoch, charges.countP (fun charge => charge.epoch == epoch) ≤ cap) :
    (charges.filter (fun charge => charge.epoch ≤ high)).length ≤ (high + 1 - start) * cap := by
  have outside (n : Nat) (before : n < start) :
      charges.countP (fun charge => charge.epoch ≤ n) = 0 := by
    apply List.countP_eq_zero.mpr
    intro charge member
    have lower := firsts charge member
    simp only [decide_eq_true_eq]
    omega
  rw [← List.countP_eq_length_filter]
  induction high with
  | zero =>
    by_cases inside : start ≤ 0
    · have zero : start = 0 := by omega
      subst start
      have same : (fun charge : DepartureCharge => decide (charge.epoch ≤ 0)) =
          (fun charge => charge.epoch == 0) := by
        funext charge
        apply Bool.eq_iff_iff.mpr
        simp
      rw [same]
      simpa only [Nat.reduceAdd, Nat.sub_zero, Nat.one_mul, Nat.le_zero_eq,
        decide_eq_true_eq, beq_iff_eq] using counts 0
    · rw [outside 0 (by omega)]
      exact Nat.zero_le _
  | succ high ih =>
    by_cases inside : start ≤ high + 1
    · have splitCount : charges.countP (fun charge => charge.epoch ≤ high + 1) =
          charges.countP (fun charge => charge.epoch ≤ high) +
          charges.countP (fun charge => charge.epoch == high + 1) := by
        clear firsts counts outside ih
        induction charges with
        | nil => simp
        | cons charge rest ih =>
          simp only [List.countP_cons, ih]
          split_ifs <;> simp_all only [decide_eq_true_eq, beq_iff_eq] <;> omega
      rw [splitCount]
      have distance : high + 1 + 1 - start = (high + 1 - start) + 1 := by omega
      have latest := counts (high + 1)
      simpa only [Nat.succ_eq_add_one, distance, Nat.add_mul, Nat.one_mul] using
        Nat.add_le_add ih latest
    · rw [outside (high + 1) (by omega)]
      exact Nat.zero_le _

private theorem charges_le_window_of_cohorts {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (start high cap maxAmount : Nat)
    (cohorts : ExitCohortsBounded
      (fun epoch => x.state.validators.data.toList.countP (·.exitEpoch == epoch)) cap y.state)
    (bounds : ∀ charge ∈ tail.departureCharges,
      start ≤ charge.epoch ∧ charge.amount ≤ maxAmount) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high).map (·.amount)).sum ≤
      (high + 1 - start) * (cap * maxAmount) := by
  have counts (epoch : Nat) :
      tail.departureCharges.countP (fun charge => charge.epoch == epoch) ≤ cap := by
    by_cases empty : tail.departureCharges.countP (fun charge => charge.epoch == epoch) = 0
    · rw [empty]; exact Nat.zero_le _
    obtain ⟨charge, member, same⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero empty)
    obtain ⟨v, found, finite, exit⟩ := tail.departure_charge_exit charge member
    have exit : v.exitEpoch.toNat = epoch := exit.trans (beq_iff_eq.mp same)
    have predicates : (fun w : Validator => w.exitEpoch.toNat == epoch) =
        (fun w => w.exitEpoch == v.exitEpoch) := by
      funext w
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, ← exit, UInt64.toNat_inj]
    have joint := charge_count_le_cohort tail epoch
      (fun far => finite (UInt64.toNat_inj.mp (exit.trans far)))
    rw [predicates] at joint
    have capped := cohorts v.exitEpoch finite
    -- The cohort of `x` is part of the cohort of `y`, so the charges fit in the cap.
    rcases Nat.le_total (x.state.validators.data.toList.countP (·.exitEpoch == v.exitEpoch))
      cap with le | le
    · rw [Nat.max_eq_right le] at capped
      omega
    · rw [Nat.max_eq_left le] at capped
      omega
  have length := charge_window_length_le tail.departureCharges
    start high cap (fun charge member => (bounds charge member).1) counts
  have amount := List.sum_le_length_nsmul
    ((tail.departureCharges.filter fun c => c.epoch ≤ high).map (·.amount))
    maxAmount (by
      intro amount member
      obtain ⟨charge, present, equal⟩ := List.mem_map.mp member
      rw [← equal]
      exact (bounds charge (List.mem_filter.mp present).1).2)
  simp only [List.length_map, nsmul_eq_mul, Nat.cast_id] at amount
  apply amount.trans
  simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_right maxAmount length

private theorem pre_electra_charges_le_window {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : y.fork < .pectra) (high bound : Nat)
    (counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → u.fork < .pectra → activeCount u.state ≤ bound) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high).map (·.amount)).sum ≤
      (high + 1 - (getCurrentEpoch x.state).toNat) *
        (max 1 (cohortCap config bound) * preset.MAX_EFFECTIVE_BALANCE.toNat) :=
  charges_le_window_of_cohorts tail _ high _ _
    ((CountCohortStep.run bound tail early counted).bounded _
      (fun _ _ => Nat.le_max_left _ _))
    (pre_electra_charge_bounds shared tail genesis caps early)

private theorem crossing_charges_le_window {g x middle y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x middle)
    (step : Step config checks middle y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : middle.fork < .pectra) (targetEarly : y.fork < .glamsterdam) (high bound : Nat)
    (counted : ∀ {u w : ForkedBeaconState preset} (later : Step config checks u w),
      (pre.snoc step).Contains later → u.fork < .pectra → activeCount u.state ≤ bound) :
    (((pre.snoc step).departureCharges.filter fun c => c.epoch ≤ high).map (·.amount)).sum ≤
      (high + 1 - (getCurrentEpoch x.state).toNat) *
        (max 1 (cohortCap config bound) * preset.MAX_EFFECTIVE_BALANCE.toNat) := by
  have kept := CountCohortStep.crossing bound step early targetEarly
    (counted step (.last _ _) early)
  have before := CountCohortStep.run bound pre early
    fun later member => counted later (.earlier member _)
  apply charges_le_window_of_cohorts (pre.snoc step) _ high _ _
    (kept.bounded _ (before.bounded _ (fun _ _ => Nat.le_max_left _ _)))
  intro charge member
  rcases List.mem_append.mp member with earlier | latest
  · exact pre_electra_charge_bounds shared pre genesis caps early charge earlier
  · have bounds := pre_electra_charge_step_bounds (shared.append pre) step genesis caps
      early targetEarly charge latest
    exact ⟨(UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)).trans
      bounds.1, bounds.2⟩

/-- A step within one epoch keeps every existing effective balance. -/
theorem step_same_epoch_effective {x y : ForkedBeaconState preset}
    (step : Step config checks x y)
    (epoch : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    ∀ i, i < x.state.validators.data.size → effectiveAt y i = effectiveAt x i :=
  Run.effectiveKept_of_same_epoch (Run.nil.snoc step) epoch

/-- A run inside one epoch keeps every existing effective balance.

Blocks keep them at every fork, and a slot inside the epoch runs no epoch transition.

The slot is not an epoch boundary, so it runs no upgrade. -/
theorem run_same_epoch_effective {x y : ForkedBeaconState preset}
    (tail : Run config checks x y)
    (epoch : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    ∀ i, i < x.state.validators.data.size → effectiveAt y i = effectiveAt x i :=
  Run.effectiveKept_of_same_epoch tail epoch

private theorem consolidationRequestSites_input {fork : Fork} {s : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    {sites : List (ForkedBeaconState preset)}
    (ok : consolidationRequestSites config s electra request = .ok sites)
    (site : ForkedBeaconState preset) (member : site ∈ sites) : site = ⟨fork, s⟩ := by
  simp only [consolidationRequestSites, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨called, _, rfl⟩ := ok
  cases called with
  | false => simp at member
  | true => simpa using member

private theorem consolidationRequestsSites_prefix {fork : Fork}
    {electra : .pectra ≤ fork} {s t : BeaconState preset fork}
    {sites : List (ForkedBeaconState preset)} {requests : List ConsolidationRequest}
    (ok : consolidationRequestsSites config electra s requests = .ok (t, sites))
    (site : ForkedBeaconState preset) (member : site ∈ sites) :
    ∃ u : BeaconState preset fork, site = ⟨fork, u⟩ ∧ SitePrefix s u := by
  induction requests generalizing s sites with
  | nil => cases ok; simp at member
  | cons request rest ih =>
    simp only [consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨here, recorded, next, stepped, ⟨last, later⟩, replayed, rfl, rfl⟩ := ok
    rcases List.mem_append.mp member with first | tail
    · exact ⟨s, consolidationRequestSites_input recorded site first, .refl s⟩
    · obtain ⟨u, same, kept⟩ := ih replayed tail
      exact ⟨u, same, (SitePrefix.mk
        (frame_processConsolidationRequest stepped).registryGrows
        (activeStep_processConsolidationRequest stepped)
        (effectiveKept_consolidationRequest stepped)).trans kept⟩

private theorem blockConsolidationSites_prefix {fork : Fork}
    {engine : ExecutionEngine preset fork} {s : BeaconState preset fork}
    {block : BeaconBlock preset fork} {sites : List (ForkedBeaconState preset)}
    (ok : blockConsolidationSites config checks engine s block = .ok sites)
    (site : ForkedBeaconState preset) (member : site ∈ sites) :
    ∃ u : BeaconState preset fork, site = ⟨fork, u⟩ ∧ SitePrefix s u := by
  unfold blockConsolidationSites at ok
  split at ok
  · rename_i electra
    simp only [bind_ok_iff, ensure_ok_iff, pure, Except.pure, Except.ok.injEq,
      ← Array.foldlM_toList] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
      votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
      requested, requestedOk, withdrawn, withdrawnOk, ⟨last, recorded⟩, replayed, rfl⟩ := ok
    have prior := blockHead_sitePrefix headedOk executedOk revealedOk votedOk
    have operations := (operations_prefix_site_prefixes electra.1 proposedOk attestedOk votedAttOk
      depositedOk exitedOk changedOk).2.2
    have requests : SitePrefix changed requested := depositRequests_sitePrefix electra.1 requestedOk
    have withdrawals : SitePrefix requested withdrawn :=
      withdrawalRequests_sitePrefix electra.1 withdrawnOk
    obtain ⟨u, same, kept⟩ := consolidationRequestsSites_prefix replayed site member
    exact ⟨u, same, prior.trans (operations.trans (requests.trans (withdrawals.trans kept)))⟩
  · cases ok; simp at member

/-- A consolidation site of a run from Electra lies between Electra and Gloas.

It is no earlier than the run's first epoch.

In that epoch it reads the total active balance of the run's first state. -/
theorem consolidationSite_epoch_total {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam)
    (site : ForkedBeaconState preset) (member : site ∈ tail.consolidationSites) :
    .pectra ≤ site.fork ∧ site.fork < .glamsterdam ∧
      getCurrentEpoch x.state ≤ getCurrentEpoch site.state ∧
      (getCurrentEpoch site.state = getCurrentEpoch x.state →
        getTotalActiveBalance site.state = getTotalActiveBalance x.state) := by
  induction tail with
  | nil => simp [Run.consolidationSites] at member
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have middleElectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    rcases List.mem_append.mp member with previous | current
    · exact ih middleEarly previous
    · cases step with
      | slot ok => simp [Step.consolidationSites] at current
      | @block fork before after engine signed due applied =>
        unfold Step.consolidationSites at current
        cases replay : blockConsolidationSites config checks engine before signed.message with
        | error err => simp [replay, Except.toOption] at current
        | ok sites =>
          simp only [replay, Except.toOption, Option.getD_some] at current
          obtain ⟨u, rfl, kept⟩ := blockConsolidationSites_prefix replay site current
          have epoch : getCurrentEpoch u = getCurrentEpoch before := by
            simp only [getCurrentEpoch, kept.active.1]
          refine ⟨middleElectra, middleEarly, ?_, ?_⟩
          · rw [epoch]
            exact currentEpoch_le_of_chainSteps pre.chainSteps
          · intro same
            have first := total_active_congr
              ((activeKept_of_chainSteps pre.chainSteps).mono
                (getCurrentEpoch_le_activityFixedEpoch x.state))
              (epoch.symm.trans same)
              (run_same_epoch_effective pre (epoch.symm.trans same))
            have second := total_active_congr
              (kept.active.2.mono (getCurrentEpoch_le_activityFixedEpoch before)) epoch
              kept.effective
            exact second.trans first

/-- A consolidation site reads the consolidation churn of the input state of a step of the run. -/
theorem consolidationSite_rate {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (site : ForkedBeaconState preset) (member : site ∈ tail.consolidationSites) :
    ∃ (u w : ForkedBeaconState preset) (step : Step config checks u w), tail.Contains step ∧
      (.pectra ≤ site.fork → .pectra ≤ u.fork) ∧
      ∀ rate : Gwei, getConsolidationChurnLimit config site.state = .ok rate →
        getConsolidationChurnLimit config u.state = .ok rate := by
  induction tail with
  | nil => simp [Run.consolidationSites] at member
  | @snoc middle last pre step ih =>
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    rcases List.mem_append.mp member with previous | current
    · obtain ⟨u, w, found, contained, forks, rate⟩ := ih middleEarly previous
      exact ⟨u, w, found, .earlier contained step, forks, rate⟩
    · cases step with
      | slot ok => simp [Step.consolidationSites] at current
      | @block fork before after engine signed due applied =>
        unfold Step.consolidationSites at current
        cases replay : blockConsolidationSites config checks engine before signed.message with
        | error err => simp [replay, Except.toOption] at current
        | ok sites =>
          simp only [replay, Except.toOption, Option.getD_some] at current
          obtain ⟨u, rfl, kept⟩ := blockConsolidationSites_prefix replay site current
          have epoch : getCurrentEpoch u = getCurrentEpoch before := by
            simp only [getCurrentEpoch, kept.active.1]
          have total := total_active_congr
            (kept.active.2.mono (getCurrentEpoch_le_activityFixedEpoch before)) epoch
            kept.effective
          refine ⟨_, _, _, .last pre (.block engine signed due applied), id, ?_⟩
          intro rate computed
          have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt middleEarly
          rw [← computed]
          simp only [getConsolidationChurnLimit, notGloas, ↓reduceIte,
            getActivationExitChurnLimit, getBalanceChurnLimit, total]

private theorem DepartureQueueTrace.window_le_initialized
    {earliest epoch : Epoch} {available left : Gwei} {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left) (start high cap : Nat)
    (later : start < earliest.toNat)
    (rates : ∀ call ∈ calls, call.rate.toNat ≤ cap)
    (startup : ∀ call ∈ calls, available.toNat ≤ cap ∨ earliest < call.first) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map fun call => call.amount.toNat).sum ≤
      (high + 1 - start) * cap := by
  cases trace with
  | nil => simp
  | cons call tail =>
    rcases startup call (by simp) with bounded | reset
    · have budget := (DepartureQueueTrace.cons call tail).window_le high cap rates
      have initial : departureQueuePotential high cap call.earliest call.available ≤
          (high + 1 - start) * cap := by
        unfold departureQueuePotential
        split
        · calc
            _ ≤ cap + (high - call.earliest.toNat) * cap := Nat.add_le_add_right bounded _
            _ = (1 + (high - call.earliest.toNat)) * cap := by rw [Nat.add_mul, Nat.one_mul]
            _ ≤ _ := Nat.mul_le_mul_right cap (by omega)
        · exact Nat.zero_le _
      exact (Nat.le_add_right _ _).trans (budget.trans initial)
    · exact tail.window_le_of_reset start high cap rates
        (by
          rw [UInt64.lt_iff_toNat_lt, Uint64.toNat_max]
          exact Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp reset) (Nat.le_max_right _ _))
        (by omega)

private structure InitializedDepartureQueues (s : ForkedBeaconState preset)
    (electra : .pectra ≤ s.fork) : Prop where
  exitLater : (getCurrentEpoch s.state).toNat < (s.state.earliestExitEpoch electra).toNat
  exitCap : (s.state.exitBalanceToConsume electra).toNat ≤
    config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
  consolidationFirst : computeActivationExitEpoch preset (getCurrentEpoch s.state) =
    .ok (s.state.earliestConsolidationEpoch electra)
  consolidationRate : getConsolidationChurnLimit config s.state =
    .ok (s.state.consolidationBalanceToConsume electra)

private theorem initialized_electra {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    InitializedDepartureQueues (config := config) ⟨.pectra, t⟩
      (show Fork.pectra ≤ .pectra from Nat.le_refl _) := by
  obtain ⟨epoch, _, exitRate, consolidationRate⟩ := electra_crossing_queues ok
  obtain ⟨first, exitEpoch, exitCapacity, consolidationCapacity, firstOk, _, fields⟩ :=
    electra_departure_initialization ok
  have firstField := congrArg (fun q => q.2.2.1) fields
  change t.earliestConsolidationEpoch (by decide) = first at firstField
  refine ⟨?_, exitChurnLimit_le_cap (by decide) exitRate, ?_, consolidationRate⟩
  · rw [epoch]
    exact (electra_departure_epochs ok).1
  · rw [epoch, firstField]
    exact firstOk

private theorem initialized_upgrades {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) (targetElectra : .pectra ≤ t.fork)
    (initial : InitializedDepartureQueues (config := config) s electra) :
    InitializedDepartureQueues (config := config) t targetElectra := by
  obtain ⟨fields, data, _, _⟩ := upgrades_departureQueues electra early ok targetElectra
  have epoch : getCurrentEpoch t.state = getCurrentEpoch s.state := by
    simp only [getCurrentEpoch, processUpgrades_slot ok]
  have sourceEarly := Nat.lt_of_le_of_lt (processUpgrades_fork_le ok) early
  have total := total_active_congr (ActiveKept.of_validators data _) epoch
    (by intro i _; simp only [effectiveAt, data])
  have notGloas : ¬ .glamsterdam ≤ t.fork := Nat.not_le_of_lt early
  have sourceNotGloas : ¬ .glamsterdam ≤ s.fork := Nat.not_le_of_lt sourceEarly
  have consolidation : getConsolidationChurnLimit config t.state =
      getConsolidationChurnLimit config s.state := by
    simp only [getConsolidationChurnLimit, notGloas,
      sourceNotGloas, ↓reduceIte, getActivationExitChurnLimit,
      getBalanceChurnLimit, total]
  have exitEpoch := congrArg Prod.fst fields
  have exitBalance := congrArg (fun q => q.2.1) fields
  have consolidationEpoch := congrArg (fun q => q.2.2.1) fields
  have consolidationBalance := congrArg (fun q => q.2.2.2.1) fields
  change t.state.earliestExitEpoch targetElectra = s.state.earliestExitEpoch electra at exitEpoch
  change t.state.exitBalanceToConsume targetElectra = s.state.exitBalanceToConsume electra
    at exitBalance
  change t.state.earliestConsolidationEpoch targetElectra =
    s.state.earliestConsolidationEpoch electra at consolidationEpoch
  change t.state.consolidationBalanceToConsume targetElectra =
    s.state.consolidationBalanceToConsume electra at consolidationBalance
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [epoch, exitEpoch] using initial.exitLater
  · simpa only [exitBalance] using initial.exitCap
  · simpa only [epoch, consolidationEpoch] using initial.consolidationFirst
  · simpa only [consolidationBalance] using consolidation.trans initial.consolidationRate

private theorem crossing_upgrades_initialized {s t : ForkedBeaconState preset}
    (before : s.fork < .pectra) (electra : .pectra ≤ t.fork)
    (early : t.fork < .glamsterdam) (ok : processUpgrades config checks s = .ok t) :
    InitializedDepartureQueues (config := config) t electra := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    by_cases stillBefore : next.val.fork < .pectra
    · exact ih next stillBefore electra early rest
    · have nextElectra := Nat.le_of_not_lt stillBefore
      have initial : InitializedDepartureQueues (config := config) next.val nextElectra := by
        obtain ⟨fork, state⟩ := s
        cases fork
        all_goals try (solve | simp (config := { decide := true }) at before)
        all_goals
          simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
            throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at nextOk
        · obtain ⟨_, _, rfl⟩ := nextOk
          simp (config := { decide := true }) at nextElectra
        · subst nextOk; simp (config := { decide := true }) at nextElectra
        · subst nextOk; simp (config := { decide := true }) at nextElectra
        · subst nextOk; simp (config := { decide := true }) at nextElectra
        · obtain ⟨_, upgraded, rfl⟩ := nextOk
          exact initialized_electra upgraded
      exact initialized_upgrades nextElectra early rest electra initial
  | case2 s notDue => cases ok; exact False.elim (Nat.not_lt_of_ge electra before)

private theorem crossing_initialized {s t : ForkedBeaconState preset}
    (step : Step config checks s t) (before : s.fork < .pectra)
    (electra : .pectra ≤ t.fork) (early : t.fork < .glamsterdam) :
    InitializedDepartureQueues (config := config) t electra := by
  cases step with
  | block engine signed due ok => exact False.elim (Nat.not_lt_of_ge electra before)
  | slot ok =>
    obtain ⟨advanced, _, upgraded⟩ := bind_ok_iff.mp ok
    exact crossing_upgrades_initialized (s := ⟨s.fork, advanced⟩) before electra early upgraded

private theorem initialized_charges_le_window {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (high cap : Nat)
    (initial : InitializedDepartureQueues (config := config) x electra)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high).map (·.amount)).sum ≤
      (high + 1 - (getCurrentEpoch x.state).toNat) *
        (config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + cap) := by
  have targetElectra := Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)
  obtain ⟨exits, consolidations, _, matched, exitTrace, consolidationTrace,
    exitRates, consolidationRates, sites, -⟩ :=
    run_indexedTrace_sites tail electra early targetElectra cap rates
  have charges := departureCharges_le_calls (departureCharges_run_indices tail) matched high
  have exitBound := exitTrace.window_le_initialized (getCurrentEpoch x.state).toNat high
    config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat initial.exitLater
    (by
      intro call member
      obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
      exact exitRates called present)
    (by intro _ _; exact Or.inl initial.exitCap)
  have first := (computeActivationExitEpoch_ok_iff.mp initial.consolidationFirst).2
  have consolidationLater : (getCurrentEpoch x.state).toNat <
      (x.state.earliestConsolidationEpoch electra).toNat := by omega
  have startup : ∀ call ∈ consolidations.map (·.call),
      (x.state.consolidationBalanceToConsume electra).toNat ≤ cap ∨
        x.state.earliestConsolidationEpoch electra < call.first := by
    intro call member
    obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨site, listed, firstOk, rateOk⟩ := sites called present
    obtain ⟨_, siteEarly, ordered, total⟩ := consolidationSite_epoch_total tail electra early
      site listed
    by_cases same : getCurrentEpoch site.state = getCurrentEpoch x.state
    · have sameTotal := total same
      have sourceEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
      have notGloas : ¬ .glamsterdam ≤ site.fork := Nat.not_le_of_lt siteEarly
      have sourceNotGloas : ¬ .glamsterdam ≤ x.fork := Nat.not_le_of_lt sourceEarly
      have sameRate : getConsolidationChurnLimit config site.state =
          getConsolidationChurnLimit config x.state := by
        simp only [getConsolidationChurnLimit, notGloas, sourceNotGloas, ↓reduceIte,
          getActivationExitChurnLimit, getBalanceChurnLimit, sameTotal]
      have equal := Except.ok.inj (rateOk.symm.trans
        (sameRate.trans initial.consolidationRate))
      exact Or.inl (equal ▸ consolidationRates called present)
    · have later := (computeActivationExitEpoch_ok_iff.mp firstOk).2
      have epochNe : (getCurrentEpoch site.state).toNat ≠ (getCurrentEpoch x.state).toNat :=
        fun equal => same (UInt64.toNat_inj.mp equal)
      have ordered := UInt64.le_iff_toNat_le.mp ordered
      right
      rw [UInt64.lt_iff_toNat_lt]
      omega
  have consolidationBound := consolidationTrace.window_le_initialized
    (getCurrentEpoch x.state).toNat high cap consolidationLater
    (by
      intro call member
      obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
      exact consolidationRates called present) startup
  simp only [List.filter_map, List.map_map, Function.comp_def] at exitBound consolidationBound
  simp only [List.filter_append, List.map_append, List.sum_append] at charges
  rw [Nat.mul_add]
  omega

private theorem upgrades_electra_epoch {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t)
    (initial : .pectra ≤ s.fork → config.ELECTRA_FORK_EPOCH.toNat ≤
      (getCurrentEpoch s.state).toNat) :
    .pectra ≤ t.fork → config.ELECTRA_FORK_EPOCH.toNat ≤
      (getCurrentEpoch t.state).toNat := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    apply ih next rest
    intro electra
    have slot := (upgradeFrame_upgradeNext nextOk).slot
    have epoch : getCurrentEpoch next.val.state = getCurrentEpoch s.state := by
      simp only [getCurrentEpoch, slot]
    rw [epoch]
    by_cases old : .pectra ≤ s.fork
    · exact initial old
    · obtain ⟨fork, state⟩ := s
      cases fork <;> simp only at old
      all_goals try (exact False.elim (old (by decide)))
      all_goals simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        throw] at nextOk
      all_goals try contradiction
      all_goals (obtain ⟨_, _, rfl⟩ := nextOk)
      all_goals try (exact False.elim (of_decide_eq_false rfl electra))
      simp only [upgradeDue, Config.nextFork, Option.any_some, Bool.and_eq_true,
        beq_iff_eq] at due
      have scheduled : getCurrentEpoch state = config.ELECTRA_FORK_EPOCH := by
        exact due.2
      rw [scheduled]
  | case2 s notDue => cases ok; exact initial

/-- A call leaves at most the larger of the capacity it found and its rate. -/
private theorem DepartureQueueCall.left_le (call : DepartureQueueCall) :
    call.left.toNat ≤ max call.available.toNat call.rate.toNat := by
  obtain ⟨-, spent, last⟩ := churnQueue_spend call.computed
  have avail : (if call.earliest < max call.earliest call.first then call.rate
      else call.available).toNat ≤ max call.available.toNat call.rate.toNat := by
    split <;> omega
  rcases last with same | below
  · rw [same, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at spent
    omega
  · omega

/-- A trace of calls with rates at most `cap` leaves at most the larger of its start and `cap`. -/
private theorem DepartureQueueTrace.left_le {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left) (cap : Nat)
    (rates : ∀ call ∈ calls, call.rate.toNat ≤ cap) :
    left.toNat ≤ max available.toNat cap := by
  induction trace with
  | nil => exact Nat.le_max_left _ _
  | cons call tail ih =>
    have rest := ih fun c member => rates c (List.mem_cons_of_mem _ member)
    have first := call.left_le
    have rate := rates call (List.mem_cons_self)
    omega

/-- The queues carry bounded capacity at the end `y` of a run from a state `x` after genesis.

The exit capacity at `y` is at most the largest per-epoch exit churn.

The consolidation capacity at `y` is at most the larger of its capacity at `x` and `cap`.

Here `cap` bounds the consolidation churn at each site of the run from `x`. -/
theorem queueCarry_le_of_run {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap : Nat)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    (y.state.exitBalanceToConsume targetElectra).toNat ≤
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat ∧
      (y.state.consolidationBalanceToConsume targetElectra).toNat ≤
        max (x.state.consolidationBalanceToConsume electra).toNat cap := by
  constructor
  · have gBefore : g.fork < .pectra := by
      refine Nat.lt_of_not_ge fun late => ?_
      exact absurd (Nat.lt_of_le_of_lt late genesis.before) (by decide)
    obtain ⟨u, v, head, step, rest, uBefore, vElectra, -⟩ :=
      split_electra_crossing (shared.append tail) gBefore targetElectra
    have vEarly : v.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
    have initial := crossing_initialized (config := config) step uBefore vElectra vEarly
    obtain ⟨exits, -, -, -, exitTrace, -, exitRates, -⟩ :=
      run_indexedTrace_sites rest vElectra early targetElectra (2 ^ 64)
        (fun _ _ _ rate _ => (UInt64.toNat_lt rate).le)
    have bound := exitTrace.left_le config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
      (fun call member => by
        obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
        exact exitRates called present)
    have start := initial.exitCap
    omega
  · obtain ⟨-, consolidations, -, -, -, consolidationTrace, -, consolidationRates, -⟩ :=
      run_indexedTrace_sites tail electra early targetElectra cap rates
    exact consolidationTrace.left_le cap
      (fun call member => by
        obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
        exact consolidationRates called present)

/-- A state of a run from genesis that is at Electra is at or after its fork epoch. -/
theorem reachable_electra_epoch {g y : ForkedBeaconState preset}
    (run : Run config checks g y) (genesis : Genesis (config := config) (checks := checks) g) :
    .pectra ≤ y.fork → config.ELECTRA_FORK_EPOCH.toNat ≤
      (getCurrentEpoch y.state).toNat := by
  induction run with
  | nil =>
    intro electra
    exact absurd (Nat.lt_of_le_of_lt electra genesis.before) (by decide)
  | @snoc middle last pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
      apply upgrades_electra_epoch upgrades
      intro electra
      have previous := ih electra
      have moved := advanceSlot_slot advanceOk
      have epochs : (getCurrentEpoch middle.state).toNat ≤
          (getCurrentEpoch advanced).toNat := by
        simp only [getCurrentEpoch_toNat]
        exact Nat.div_le_div_right (by omega)
      exact previous.trans epochs
    | block engine signed due ok =>
      intro electra
      have previous := ih electra
      have slot := (frame_processBlock (applySignedBlock_ok ok).2.1).slot
      simpa only [getCurrentEpoch, slot] using previous

/-- A run that crosses into Electra charges the count churn before the crossing.

After it, the run charges the Electra caps from the first Electra state `v` on. -/
private theorem crossing_charges_split {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high countBound cap : Nat)
    (counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → u.fork < .pectra → activeCount u.state ≤ countBound)
    (rates : ∀ site ∈ tail.consolidationSites, .pectra ≤ site.fork → ∀ (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap)
    (before : x.fork < .pectra) (targetElectra : .pectra ≤ y.fork) :
    ∃ v : ForkedBeaconState preset, Nonempty (Run config checks g v) ∧ .pectra ≤ v.fork ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch v.state).toNat ∧
      ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
        (high + 2 - (getCurrentEpoch x.state).toNat) *
          (max 1 (cohortCap config countBound) * preset.MAX_EFFECTIVE_BALANCE.toNat) +
        (high + 2 - (getCurrentEpoch v.state).toNat) *
          (config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + cap) := by
  obtain ⟨u, v, pre, crossing, post, uBefore, vElectra, same⟩ :=
    split_electra_crossing tail before targetElectra
  subst tail
  have vEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have legacy := crossing_charges_le_window shared pre crossing genesis caps uBefore
    vEarly (high + 1) countBound
    fun later member => counted later ((Run.contains_append _ _ _).mpr (.inl member))
  have balance := initialized_charges_le_window post vElectra early (high + 1)
    cap (crossing_initialized crossing uBefore vElectra vEarly)
    (by
      intro site member h rate computed
      apply rates site _ h rate computed
      rw [Run.consolidationSites_append]
      exact List.mem_append_right _ member)
  have ordered := UInt64.le_iff_toNat_le.mp
    (currentEpoch_le_of_chainSteps (pre.snoc crossing).chainSteps)
  refine ⟨v, ⟨shared.append (pre.snoc crossing)⟩, vElectra, ordered, ?_⟩
  rw [Run.departureCharges_append, List.filter_append, List.map_append, List.sum_append]
  simp only [Nat.add_assoc, Nat.reduceAdd] at legacy balance
  exact Nat.add_le_add legacy balance

/-- The first epoch whose exit churn is open at `x`: the earliest exit epoch from Electra.

Before Electra it is the current epoch. -/
def exitQueueStart (x : ForkedBeaconState preset) : Nat :=
  if electra : .pectra ≤ x.fork then (x.state.earliestExitEpoch electra).toNat
  else (getCurrentEpoch x.state).toNat

/-- The first epoch whose consolidation churn is open at `x`, from Electra.

Before Electra it is the current epoch. -/
def consolidationQueueStart (x : ForkedBeaconState preset) : Nat :=
  if electra : .pectra ≤ x.fork then (x.state.earliestConsolidationEpoch electra).toNat
  else (getCurrentEpoch x.state).toNat

/-- Before Gloas, the departure charges of a run fit the queues from where each one opens at `x`.

The bound covers the charges whose exit epoch is at most `high + 1`. -/
theorem departure_charges_le_window_from {g x y : ForkedBeaconState preset}
    -- The run starts at a state `x` reached from genesis and ends at a state `y` before Gloas.
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    -- The preset caps are assumed in order, as in the bound on a window from the current epoch.
    (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high countBound consolidationCap : Nat)
    -- `countBound` bounds the active validators where each step of the run starts before Electra.
    (counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → u.fork < .pectra → activeCount u.state ≤ countBound)
    -- From Electra, the consolidation churn where each step starts is at most `consolidationCap`.
    (rates : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → .pectra ≤ u.fork → ∀ rate : Gwei,
        getConsolidationChurnLimit config u.state = .ok rate → rate.toNat ≤ consolidationCap) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      -- The first summand is the unspent capacity of the two queues at `x`, their carry.
      (if electra : .pectra ≤ x.fork then
        (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
          (x.state.exitBalanceToConsume electra).toNat else 0) +
        (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
          (x.state.consolidationBalanceToConsume electra).toNat else 0)
       else 0) +
      -- Here `e` is the current epoch of `x`.
      --
      -- Before Electra at `x`, the exit queue adds `L * MAX_EFFECTIVE_BALANCE` per epoch.
      --
      -- It counts from the later of `e` and the start of the queue to `high + 1`.
      --
      -- Here `L` is the larger of 1 and the pre-Electra churn limit of `countBound` validators.
      (high + 2 - max (getCurrentEpoch x.state).toNat (exitQueueStart x)) *
        (if x.fork < .pectra then max 1 (cohortCap config countBound) *
          preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
      -- The Electra caps count only from the Electra fork epoch on.
      --
      -- Each counts to `high + 1` from the latest of `e`, its queue's start and the fork epoch.
      --
      -- The exit queue adds `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` per epoch.
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (max (exitQueueStart x) config.ELECTRA_FORK_EPOCH.toNat)) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
      -- The consolidation queue adds `consolidationCap` per epoch.
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (max (consolidationQueueStart x) config.ELECTRA_FORK_EPOCH.toNat)) *
          consolidationCap := by
  replace rates : ∀ site ∈ tail.consolidationSites, .pectra ≤ site.fork → ∀ (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ consolidationCap := by
    intro site member electra rate computed
    obtain ⟨_, _, step, contained, forks, same⟩ := consolidationSite_rate tail early site member
    exact rates step contained (forks electra) rate (same rate computed)
  by_cases electra : .pectra ≤ x.fork
  · have bound := departure_charges_le_window_electra tail electra early high
      consolidationCap rates
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    -- A state from Electra is at or after the fork epoch, so the fork epoch moves no start.
    have late := reachable_electra_epoch shared genesis electra
    have later (start : Nat) : max (getCurrentEpoch x.state).toNat
        (max start config.ELECTRA_FORK_EPOCH.toNat) =
          max (getCurrentEpoch x.state).toNat start := by omega
    simp only [electra, ↓reduceDIte, notBefore, ↓reduceIte, Nat.mul_zero,
      Nat.add_zero, exitQueueStart, consolidationQueueStart, later]
    exact bound
  · have before : x.fork < .pectra := Nat.lt_of_not_ge electra
    simp only [electra, ↓reduceDIte, before, ↓reduceIte, Nat.zero_add, exitQueueStart,
      consolidationQueueStart, Nat.max_self]
    by_cases targetBefore : y.fork < .pectra
    · have bound := pre_electra_charges_le_window shared tail genesis caps targetBefore
        (high + 1) countBound counted
      exact bound.trans (Nat.le_add_right_of_le (Nat.le_add_right _ _))
    · -- The Electra caps count from the first Electra state, which is at the fork epoch or later.
      obtain ⟨v, ⟨reached⟩, vElectra, ordered, bound⟩ := crossing_charges_split shared tail
        genesis caps early high countBound consolidationCap counted rates before
        (Nat.le_of_not_lt targetBefore)
      have late := reachable_electra_epoch reached genesis vElectra
      have suffix : high + 2 - (getCurrentEpoch v.state).toNat ≤
          high + 2 - max (getCurrentEpoch x.state).toNat
            (max (getCurrentEpoch x.state).toNat config.ELECTRA_FORK_EPOCH.toNat) := by omega
      have exits := Nat.mul_le_mul_right
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat suffix
      have consolidations := Nat.mul_le_mul_right consolidationCap suffix
      rw [Nat.mul_add] at bound
      omega

/-- Before Gloas, the departure charges of a run fit the queue capacity of a window of epochs.

The bound covers the charges whose exit epoch is at most `high + 1`. -/
theorem departure_charges_le_window {g x y : ForkedBeaconState preset}
    -- The run starts at a state `x` reached from genesis and ends at a state `y` before Gloas.
    --
    -- A charge is a validator's effective balance, counted when its unset exit epoch is assigned.
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    -- The preset caps are assumed in order.
    --
    -- `MAX_EFFECTIVE_BALANCE` is at most `MIN_ACTIVATION_BALANCE`.
    --
    -- `MIN_ACTIVATION_BALANCE` is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`.
    (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high registryBound consolidationCap : Nat)
    -- `registryBound` bounds the size of the registry at `y`.
    (registryBounded : y.state.validators.data.size ≤ registryBound)
    -- From Electra, the consolidation churn where each step starts is at most `consolidationCap`.
    --
    -- That bound on the churn is an assumption.
    (rates : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → .pectra ≤ u.fork → ∀ rate : Gwei,
        getConsolidationChurnLimit config u.state = .ok rate → rate.toNat ≤ consolidationCap) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      -- The bound is the carry at `x` plus `H` times the per-epoch caps, where `H = high + 2 - e`.
      --
      -- From Electra at `x`, the carry is the unspent capacity of the two queues.
      --
      -- They are the exit queue and the consolidation queue.
      --
      -- A queue adds its capacity only when its earliest open epoch is at most `high + 1`.
      --
      -- Before Electra at `x`, the carry is zero.
      --
      -- The carry is unspent queue capacity, not departures that are already assigned.
      (if electra : .pectra ≤ x.fork then
        (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
          (x.state.exitBalanceToConsume electra).toNat else 0) +
        (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
          (x.state.consolidationBalanceToConsume electra).toNat else 0)
       else 0) +
      -- Here `e` is the current epoch of `x`, so `H` counts the epochs from `e` to `high + 1`.
      --
      -- Both ends are counted.
      (high + 2 - (getCurrentEpoch x.state).toNat) *
        -- The caps are `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` and `consolidationCap`.
        --
        -- Before Electra at `x`, the caps also add `L * MAX_EFFECTIVE_BALANCE`.
        --
        -- `L` is the larger of 1 and the pre-Electra churn limit of `registryBound` validators.
        ((if x.fork < .pectra then max 1 (cohortCap config registryBound) *
          preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
         config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + consolidationCap) := by
  -- The registry only grows, so each step starts with at most `registryBound` active validators.
  have counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → u.fork < .pectra → activeCount u.state ≤ registryBound := by
    intro u w step member _
    obtain ⟨_, post, _⟩ := tail.contains_split step member
    exact (activeCount_le_size u.state).trans
      ((registryGrows_of_chainSteps ((Run.nil.snoc step).append post).chainSteps).trans
        registryBounded)
  have bound := departure_charges_le_window_from shared tail genesis caps early high
    registryBound consolidationCap counted rates
  have horizon (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat start ≤
      high + 2 - (getCurrentEpoch x.state).toNat :=
    Nat.sub_le_sub_left (Nat.le_max_left _ _) _
  have count := Nat.mul_le_mul_right (if x.fork < .pectra then
    max 1 (cohortCap config registryBound) * preset.MAX_EFFECTIVE_BALANCE.toNat else 0)
      (horizon (exitQueueStart x))
  have exits := Nat.mul_le_mul_right config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
    (horizon (max (exitQueueStart x) config.ELECTRA_FORK_EPOCH.toNat))
  have consolidations := Nat.mul_le_mul_right consolidationCap
    (horizon (max (consolidationQueueStart x) config.ELECTRA_FORK_EPOCH.toNat))
  rw [Nat.mul_add (high + 2 - (getCurrentEpoch x.state).toNat) (_ + _), Nat.mul_add]
  omega

/-- A window that ends before the Electra fork epoch is charged only the count churn.

An Electra part of the run starts at the fork epoch, after the window, so it adds nothing. -/
theorem departure_charges_le_window_before_fork {g x y : ForkedBeaconState preset}
    -- The run starts at a state `x` before Electra, reached from genesis, and ends before Gloas.
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high registryBound : Nat)
    (registryBounded : y.state.validators.data.size ≤ registryBound)
    (before : x.fork < .pectra) (preFork : high + 1 < config.ELECTRA_FORK_EPOCH.toNat) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      -- The bound is `H` times the cap `L * MAX_EFFECTIVE_BALANCE`, where `H = high + 2 - e`.
      --
      -- Here `e` is the current epoch of `x`.
      --
      -- `L` is the larger of 1 and the pre-Electra churn limit of `registryBound` validators.
      (high + 2 - (getCurrentEpoch x.state).toNat) *
        (max 1 (cohortCap config registryBound) * preset.MAX_EFFECTIVE_BALANCE.toNat) := by
  have counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → u.fork < .pectra → activeCount u.state ≤ registryBound := by
    intro u w step member _
    obtain ⟨_, post, _⟩ := tail.contains_split step member
    exact (activeCount_le_size u.state).trans
      ((registryGrows_of_chainSteps ((Run.nil.snoc step).append post).chainSteps).trans
        registryBounded)
  -- The Electra terms start after the window, so any bound on the rates serves: each fits 64 bits.
  have bound := departure_charges_le_window_from shared tail genesis caps early high
    registryBound (2 ^ 64) counted (fun _ _ _ rate _ => (UInt64.toNat_lt rate).le)
  have electra : ¬ .pectra ≤ x.fork := Nat.not_le_of_lt before
  have empty (start : Nat) : high + 2 - max (getCurrentEpoch x.state).toNat
      (max start config.ELECTRA_FORK_EPOCH.toNat) = 0 := by omega
  simpa only [electra, ↓reduceDIte, before, ↓reduceIte, empty, exitQueueStart, Nat.max_self,
    Nat.zero_add, Nat.add_zero, Nat.zero_mul] using bound

/-! ## Exit-call sites within block operations -/

private theorem queue_opened_capacity (envelope : Nat → Nat) (first last rate : Nat)
    (rates : ∀ epoch, first ≤ epoch → epoch < last → rate ≤ envelope epoch) :
    (last - first) * rate ≤ ∑ epoch ∈ Finset.Ico first last, envelope epoch := by
  calc
    _ = ∑ _epoch ∈ Finset.Ico first last, rate := by simp
    _ ≤ _ := Finset.sum_le_sum fun epoch member =>
      rates epoch (Finset.mem_Ico.mp member).1 (Finset.mem_Ico.mp member).2
private theorem queue_capacity_split (envelope : Nat → Nat) (first middle last : Nat)
    (one : first ≤ middle) (two : middle ≤ last) :
    (∑ epoch ∈ Finset.Ico first middle, envelope epoch) +
      (∑ epoch ∈ Finset.Ico middle last, envelope epoch) =
      ∑ epoch ∈ Finset.Ico first last, envelope epoch := by
  rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive first middle last),
    Finset.Ico_union_Ico_eq_Ico one two]
private theorem call_opened_envelope (call : DepartureQueueCall) (envelope : Nat → Nat)
    (rates : ∀ epoch, call.first.toNat ≤ epoch → call.earliest.toNat < epoch →
      epoch ≤ call.epoch.toNat → call.rate.toNat ≤ envelope epoch) :
    call.amount.toNat + call.left.toNat ≤ call.available.toNat +
      ∑ epoch ∈ Finset.Ico (call.earliest.toNat + 1) (call.epoch.toNat + 1),
        envelope epoch := by
  obtain ⟨placed, spent, _⟩ := churnQueue_spend call.computed
  have placed := UInt64.le_iff_toNat_le.mp placed
  rw [Uint64.toNat_max] at placed
  by_cases reset : call.earliest < max call.earliest call.first
  · have opened : call.earliest.toNat < call.first.toNat := by
      rw [UInt64.lt_iff_toNat_lt, Uint64.toNat_max] at reset
      omega
    have capacity := queue_opened_capacity envelope call.first.toNat (call.epoch.toNat + 1)
      call.rate.toNat (fun epoch lower upper => rates epoch lower (by omega) (by omega))
    have included : Finset.Ico call.first.toNat (call.epoch.toNat + 1) ⊆
        Finset.Ico (call.earliest.toNat + 1) (call.epoch.toNat + 1) := by
      intro epoch member
      simp only [Finset.mem_Ico] at member ⊢
      omega
    have enlarged := Finset.sum_le_sum_of_subset_of_nonneg (f := envelope) included
      (fun _ _ _ => Nat.zero_le _)
    rw [ite_eq_left reset, Uint64.toNat_max, Nat.max_eq_right (by omega)] at spent
    have distance : call.epoch.toNat + 1 - call.first.toNat =
        1 + (call.epoch.toNat - call.first.toNat) := by omega
    rw [distance, Nat.add_mul, Nat.one_mul] at capacity
    omega
  · have first : call.first.toNat ≤ call.earliest.toNat := by
      rw [UInt64.lt_iff_toNat_lt, Uint64.toNat_max] at reset
      omega
    have capacity := queue_opened_capacity envelope (call.earliest.toNat + 1)
      (call.epoch.toNat + 1) call.rate.toNat
      (fun epoch lower upper => rates epoch (by omega) (by omega) (by omega))
    rw [ite_eq_right reset, Uint64.toNat_max, Nat.max_eq_left first] at spent
    have distance : call.epoch.toNat + 1 - (call.earliest.toNat + 1) =
        call.epoch.toNat - call.earliest.toNat := by omega
    rw [distance] at capacity
    omega
private def queueEnvelopePotential (envelope : Nat → Nat) (high : Nat)
    (epoch : Epoch) (left : Gwei) : Nat :=
  if epoch.toNat ≤ high then left.toNat +
    ∑ n ∈ Finset.Ico (epoch.toNat + 1) (high + 1), envelope n else 0
private theorem call_window_envelope (call : DepartureQueueCall) (envelope : Nat → Nat)
    (high : Nat)
    (rates : ∀ epoch, call.first.toNat ≤ epoch → call.earliest.toNat < epoch →
      epoch ≤ call.epoch.toNat → call.rate.toNat ≤ envelope epoch) :
    (if call.epoch.toNat ≤ high then call.amount.toNat else 0) +
      queueEnvelopePotential envelope high call.epoch call.left ≤
      queueEnvelopePotential envelope high call.earliest call.available := by
  by_cases inside : call.epoch.toNat ≤ high
  · have before := call.epoch_mono.trans inside
    have spent := call_opened_envelope call envelope rates
    have split := queue_capacity_split envelope (call.earliest.toNat + 1)
      (call.epoch.toNat + 1) (high + 1) (by have := call.epoch_mono; omega) (by omega)
    simp only [queueEnvelopePotential, inside, before, ↓reduceIte]
    omega
  · simp only [queueEnvelopePotential, inside, ↓reduceIte, Nat.zero_add]
    exact Nat.zero_le _
private theorem trace_window_envelope {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left)
    (envelope : Nat → Nat) (high : Nat)
    (rates : ∀ call ∈ calls, ∀ n, call.first.toNat ≤ n → call.earliest.toNat < n →
      n ≤ call.epoch.toNat → call.rate.toNat ≤ envelope n) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map (·.amount.toNat)).sum +
      queueEnvelopePotential envelope high epoch left ≤
      queueEnvelopePotential envelope high earliest available := by
  induction trace with
  | nil => simp
  | cons call rest ih =>
    have spent := call_window_envelope call envelope high (rates call (by simp))
    have later := ih (fun c member => rates c (List.mem_cons_of_mem _ member))
    by_cases inside : call.epoch.toNat ≤ high
    · simp only [List.filter_cons, decide_eq_true inside, ↓reduceIte,
        List.map_cons, List.sum_cons]
      rw [ite_eq_left inside] at spent
      omega
    · simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_right inside] at spent
      omega
private theorem queue_capacity_truncate (envelope : Nat → Nat) (lower first last : Nat) :
    (∑ epoch ∈ Finset.Ico first last, if lower ≤ epoch then envelope epoch else 0) =
      ∑ epoch ∈ Finset.Ico (max lower first) last, envelope epoch := by
  have subset : Finset.Ico (max lower first) last ⊆ Finset.Ico first last := by
    intro epoch member
    simp only [Finset.mem_Ico] at member ⊢
    omega
  calc
    _ = ∑ epoch ∈ Finset.Ico (max lower first) last,
        if lower ≤ epoch then envelope epoch else 0 := by
      symm
      apply Finset.sum_subset subset
      intro epoch inside outside
      simp only [Finset.mem_Ico] at inside outside
      rw [ite_eq_right (by omega)]
    _ = _ := Finset.sum_congr rfl fun epoch member => by
      simp only [Finset.mem_Ico] at member
      rw [ite_eq_left (by omega)]
/-- Queue spending through a horizon fits the initial carry and opened capacity. -/
theorem trace_window_envelope_from {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left)
    (envelope : Nat → Nat) (lower high : Nat)
    (starts : ∀ call ∈ calls, lower ≤ call.first.toNat)
    (rates : ∀ call ∈ calls, ∀ n, call.first.toNat ≤ n → call.earliest.toNat < n →
      n ≤ call.epoch.toNat → call.rate.toNat ≤ envelope n) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map (·.amount.toNat)).sum ≤
      if earliest.toNat ≤ high then available.toNat +
        ∑ n ∈ Finset.Ico (max lower (earliest.toNat + 1)) (high + 1), envelope n else 0 := by
  have bound := trace_window_envelope trace
    (fun n => if lower ≤ n then envelope n else 0) high (by
      intro call member n first after before
      rw [ite_eq_left ((starts call member).trans first)]
      exact rates call member n first after before)
  have spent := Nat.le_trans (Nat.le_add_right _ _) bound
  simpa only [queueEnvelopePotential, queue_capacity_truncate] using spent
private theorem exit_site_total_eq {fork : Fork} {s site : BeaconState preset fork}
    (kept : SitePrefix s site) :
    getTotalActiveBalance site = getTotalActiveBalance s := by
  have epoch : getCurrentEpoch site = getCurrentEpoch s := by
    simp only [getCurrentEpoch, kept.active.1]
  exact total_active_congr
    (kept.active.2.mono (getCurrentEpoch_le_activityFixedEpoch s)) epoch kept.effective
private theorem attester_fold_exit_sites {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {slashings : List (AttesterSlashing preset fork)}
    (ok : slashings.foldlM (processAttesterSlashing config checks) s = .ok t) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  induction slashings generalizing s with
  | nil =>
    cases ok
    exact ⟨[], .nil _ _, .of_data rfl, .of_kept rfl, by simp⟩
  | cons slashing rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, stepped, remaining⟩ := ok
    obtain ⟨first, head, firstCoverage, firstAppended, firstSites⟩ :=
      attester_exit_sites electra early stepped
    obtain ⟨later, tail, laterCoverage, laterAppended, laterSites⟩ := ih remaining
    have framed := frame_processAttesterSlashing stepped
    have kept : SitePrefix s middle := ⟨framed.registryGrows,
      activeStep_processAttesterSlashing stepped, effectiveKept_attesterSlashing stepped⟩
    refine ⟨first ++ later, ?_, ?_, firstAppended.append laterAppended, ?_⟩
    · simpa only [List.map_append] using head.append tail
    · exact firstCoverage.append_of_effectiveKept laterCoverage
        (registryLifecycle_processAttesterSlashing stepped)
        (RegistryLifecycle.foldlM
          (fun _ _ _ computed => registryLifecycle_processAttesterSlashing computed) remaining)
        kept.effective
    · intro called member
      rcases List.mem_append.mp member with member | member
      · exact firstSites called member
      · obtain ⟨site, beforeSite, slot, rate, first⟩ := laterSites called member
        exact ⟨site, kept.trans beforeSite, slot.trans framed.slot, rate, first⟩
private theorem execution_requests_covered_exit_sites {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s deposited withdrawn t : BeaconState preset fork}
    {deposits : List DepositRequest} {withdrawals : List WithdrawalRequest}
    {consolidations : List ConsolidationRequest} {sites : List (ForkedBeaconState preset)}
    (depositedOk : deposits.foldlM (processDepositRequest · electra ·) s = .ok deposited)
    (withdrawnOk : withdrawals.foldlM (processWithdrawalRequest config · electra ·)
      deposited = .ok withdrawn)
    (consolidatedOk : consolidations.foldlM (processConsolidationRequest config · electra ·)
      withdrawn = .ok t)
    (replayed : consolidationRequestsSites config electra withdrawn consolidations =
      .ok (t, sites)) (cap : Nat)
    (rates : ∀ site ∈ sites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits cons : List (IndexedDepartureCall preset config),
      DepartureCoverage s t (exits ++ cons) ∧
      DepartureQueueTrace (deposited.earliestExitEpoch electra)
        (deposited.exitBalanceToConsume electra) (exits.map (·.call))
        (withdrawn.earliestExitEpoch electra) (withdrawn.exitBalanceToConsume electra) ∧
      DepartureQueueTrace (withdrawn.earliestConsolidationEpoch electra)
        (withdrawn.consolidationBalanceToConsume electra) (cons.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      PartialsAppended electra s t exits ∧
      (∀ called ∈ cons, called.entry = none) ∧
      (∀ called ∈ cons, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config cons sites ∧
      ∀ called ∈ exits, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  obtain ⟨exits, exitTrace, exitCoverage, appended, exitSites⟩ :=
    withdrawal_fold_exit_sites electra early withdrawnOk
  obtain ⟨cons, _, consTrace, consCoverage, consRates, consSites, consEntries⟩ :=
    consolidationRequestsSites_indexedTrace_sites electra early replayed cap rates
  have depositData : deposited.validators = s.validators :=
    foldlM_ok_invariant (fun t => t.validators = s.validators)
      (fun _ _ _ kept ok => (processDepositRequest_ok ok).2.1.trans kept) rfl depositedOk
  have depositPrefix : SitePrefix s deposited := depositRequests_sitePrefix electra depositedOk
  have coverage := exitCoverage.append_of_effectiveKept consCoverage
    (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok) withdrawnOk)
    (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok) consolidatedOk)
    (effectiveKept_fold (fun _ _ _ ok => effectiveKept_withdrawalRequest ok)
      (fun _ _ _ ok => (registryLifecycle_processWithdrawalRequest ok).size_le) withdrawnOk)
  have depositedKept := congrArg (fun q => q.2.2.2.2)
    (foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
      (fun _ _ _ kept ok => (depositRequest_departureQueues electra ok).trans kept) rfl depositedOk)
  have consolidatedKept : (t.pendingPartialWithdrawals electra).data =
      (withdrawn.pendingPartialWithdrawals electra).data :=
    foldlM_ok_invariant (fun t => (t.pendingPartialWithdrawals electra).data =
        (withdrawn.pendingPartialWithdrawals electra).data)
      (fun _ _ _ kept ok => (consolidationRequest_exitFrame electra ok).2.2.trans kept) rfl
      consolidatedOk
  refine ⟨exits, cons, ?_, exitTrace, consTrace,
    (appended.kept_left depositedKept).kept_right consolidatedKept,
    consEntries, consRates, consSites, ?_⟩
  · intro i old next before after
    apply coverage i old next _ after
    simpa only [depositData] using before
  · intro called member
    obtain ⟨site, kept, slot, rate, first⟩ := exitSites called member
    exact ⟨site, depositPrefix.trans kept, slot.trans depositPrefix.active.1, rate, first⟩
private theorem operations_prefix_exit_sites {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s proposed attested voted deposited exited changed :
      BeaconState preset fork} {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    {before : fork < .hegota}
    (proposedOk : body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) s = .ok proposed)
    (attestedOk : body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposed = .ok attested)
    (votedOk : body.attestations.data.toList.foldlM
      (processAttestation config checks · parentSlot ·) attested = .ok voted)
    (depositedOk : (body.deposits before).data.toList.foldlM
      (processDeposit config checks before) voted = .ok deposited)
    (exitedOk : body.voluntaryExits.data.toList.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited)
    (changedOk : processBlsToExecutionChanges config checks exited body = .ok changed) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (changed.earliestExitEpoch electra)
        (changed.exitBalanceToConsume electra) ∧
      DepartureCoverage s changed calls ∧
      PartialsAppended electra s changed calls ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  obtain ⟨one, oneTrace, oneCoverage, oneAppended, oneSites⟩ :=
    proposer_fold_exit_sites electra early proposedOk
  obtain ⟨two, twoTrace, twoCoverage, twoAppended, twoSites⟩ :=
    attester_fold_exit_sites electra early attestedOk
  obtain ⟨three, threeTrace, threeCoverage, threeAppended, threeSites⟩ :=
    voluntary_fold_exit_sites electra early exitedOk
  obtain ⟨proposers, toDeposited, -⟩ := operations_prefix_site_prefixes electra proposedOk
    attestedOk votedOk depositedOk exitedOk changedOk
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have firstLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok) proposedOk
  have secondLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok) attestedOk
  have votesLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processAttestation ok) votedOk
  have depositsLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processDeposit ok) depositedOk
  have exitsLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok) exitedOk
  have votesData : voted.validators = attested.validators :=
    foldlM_ok_invariant (fun t => t.validators = attested.validators)
      (fun _ _ _ kept ok => (processAttestation_registry ok).1.trans kept) rfl votedOk
  have depositsCoverage := DepartureCoverage.empty_fold
    (fun _ _ _ ok => deposit_coverage electra ok)
    (fun _ _ _ ok => registryLifecycle_processDeposit ok) depositedOk
  have both := oneCoverage.append_of_effectiveKept twoCoverage firstLife secondLife
    proposers.effective
  have middle := (both.suffix_of_empty (.of_data (congrArg (·.data) votesData))
    (firstLife.trans secondLife) votesLife).suffix_of_empty depositsCoverage
      ((firstLife.trans secondLife).trans votesLife) depositsLife
  have balances := toDeposited.effective
  have covered := middle.append_of_effectiveKept threeCoverage
    (((firstLife.trans secondLife).trans votesLife).trans depositsLife) exitsLife balances
  simp only [processBlsToExecutionChanges, capella, ↓reduceDIte,
    ← Array.foldlM_toList] at changedOk
  have changesLife := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changedOk
  have changesCoverage := DepartureCoverage.empty_fold
    (fun _ _ _ ok => credentials_coverage ok)
    (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changedOk
  have votesFrame : departureQueues electra voted = departureQueues electra attested :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra attested)
      (fun _ _ _ kept ok => (attestation_departureQueues electra ok).trans kept) rfl votedOk
  have depositsFrame : departureQueues electra deposited = departureQueues electra voted :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra voted)
      (fun _ _ _ kept ok => (deposit_departureQueues electra ok).trans kept) rfl depositedOk
  have changesFrame : departureQueues electra changed = departureQueues electra exited :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra exited)
      (fun _ _ _ kept ok => (credentials_departureQueues electra ok).trans kept) rfl changedOk
  refine ⟨(one ++ two) ++ three, ?_, ?_, ?_, ?_⟩
  · have middleEpoch := congrArg Prod.fst (depositsFrame.trans votesFrame)
    have middleBalance := congrArg (fun q => q.2.1) (depositsFrame.trans votesFrame)
    have lastEpoch := congrArg Prod.fst changesFrame
    have lastBalance := congrArg (fun q => q.2.1) changesFrame
    change deposited.earliestExitEpoch electra = attested.earliestExitEpoch electra at middleEpoch
    change deposited.exitBalanceToConsume electra = attested.exitBalanceToConsume electra
      at middleBalance
    change changed.earliestExitEpoch electra = exited.earliestExitEpoch electra at lastEpoch
    change changed.exitBalanceToConsume electra = exited.exitBalanceToConsume electra at lastBalance
    rw [middleEpoch, middleBalance] at threeTrace
    rw [lastEpoch, lastBalance, List.map_append, List.map_append]
    exact (oneTrace.append twoTrace).append threeTrace
  · exact covered.suffix_of_empty changesCoverage
      ((((firstLife.trans secondLife).trans votesLife).trans depositsLife).trans exitsLife)
      changesLife
  · exact (((oneAppended.append twoAppended).kept_right
      (congrArg (fun q => q.2.2.2.2) (depositsFrame.trans votesFrame))).append
        threeAppended).kept_right (congrArg (fun q => q.2.2.2.2) changesFrame)
  · intro called member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact oneSites called member
      · obtain ⟨site, kept, slot, rate, first⟩ := twoSites called member
        exact ⟨site, proposers.trans kept, slot.trans proposers.active.1, rate, first⟩
    · obtain ⟨site, kept, slot, rate, first⟩ := threeSites called member
      exact ⟨site, toDeposited.trans kept, slot.trans toDeposited.active.1, rate, first⟩
private theorem operations_prefix_site_prefix {fork : Fork} (electra : .pectra ≤ fork)
    {s proposed attested voted deposited exited changed : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} {before : fork < .hegota}
    (proposedOk : body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) s = .ok proposed)
    (attestedOk : body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposed = .ok attested)
    (votedOk : body.attestations.data.toList.foldlM
      (processAttestation config checks · parentSlot ·) attested = .ok voted)
    (depositedOk : (body.deposits before).data.toList.foldlM
      (processDeposit config checks before) voted = .ok deposited)
    (exitedOk : body.voluntaryExits.data.toList.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited)
    (changedOk : processBlsToExecutionChanges config checks exited body = .ok changed) :
    SitePrefix s changed :=
  (operations_prefix_site_prefixes electra proposedOk attestedOk votedOk depositedOk exitedOk
    changedOk).2.2

private theorem operations_covered_exit_sites {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks s body parentSlot = .ok t) :
    ∃ exits cons : List (IndexedDepartureCall preset config),
      DepartureCoverage s t (exits ++ cons) ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (exits.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      PartialsAppended electra s t exits ∧
      (∀ called ∈ cons, called.entry = none) ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (cons.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      (∀ called ∈ cons, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        getConsolidationChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first) ∧
      ∀ called ∈ exits, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  simp only [processOperations, notGloas, electra, ↓reduceDIte,
    bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨expected, _, _, _, proposed, proposedOk, attested, attestedOk,
    voted, votedOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
    requestsOk⟩ := ok
  have requestsLife := registryLifecycle_processExecutionRequests requestsOk
  simp only [processExecutionRequests, bind_ok_iff] at requestsOk
  obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidatedOk⟩ := requestsOk
  rw [← Array.foldlM_toList] at proposedOk attestedOk votedOk depositedOk exitedOk
  rw [← Array.foldlM_toList] at requestedOk withdrawnOk consolidatedOk
  obtain ⟨sites, replayed⟩ := consolidationRequestsSites_result consolidatedOk
  obtain ⟨one, oneTrace, oneCoverage, oneAppended, oneSites⟩ := operations_prefix_exit_sites
    electra early proposedOk attestedOk votedOk depositedOk exitedOk changedOk
  obtain ⟨two, cons, twoCoverage, twoTrace, consTrace, twoAppended, entries, _,
    consSites, twoSites⟩ :=
    execution_requests_covered_exit_sites electra early requestedOk withdrawnOk consolidatedOk
      replayed (2 ^ 64) (fun _ _ _ rate _ => (UInt64.toNat_lt rate).le)
  have prior := operations_prefix_site_prefix electra proposedOk attestedOk votedOk
    depositedOk exitedOk changedOk
  have firstLife := (((RegistryLifecycle.foldlM
    (fun _ _ _ h => registryLifecycle_processProposerSlashing h) proposedOk).trans
    (RegistryLifecycle.foldlM
      (fun _ _ _ h => registryLifecycle_processAttesterSlashing h) attestedOk)).trans
    (RegistryLifecycle.foldlM
      (fun _ _ _ h => registryLifecycle_processAttestation h) votedOk)).trans
    (RegistryLifecycle.foldlM
      (fun _ _ _ h => registryLifecycle_processDeposit h) depositedOk)
  have exitsLife := RegistryLifecycle.foldlM
    (fun _ _ _ h => registryLifecycle_processVoluntaryExit h) exitedOk
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have changedFold := changedOk
  simp only [processBlsToExecutionChanges, capella, ↓reduceDIte,
    ← Array.foldlM_toList] at changedFold
  have changesLife := RegistryLifecycle.foldlM
    (fun _ _ _ h => registryLifecycle_processBlsToExecutionChange h) changedFold
  have coverage := oneCoverage.append_of_effectiveKept twoCoverage
    ((firstLife.trans exitsLife).trans changesLife) requestsLife prior.effective
  have depositedFrame : departureQueues electra requested = departureQueues electra changed :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra changed)
      (fun _ _ _ kept h => (depositRequest_departureQueues electra h).trans kept) rfl requestedOk
  have withdrawnFrame : ((departureQueues electra withdrawn).2.2.1,
      (departureQueues electra withdrawn).2.2.2.1) =
      ((departureQueues electra requested).2.2.1, (departureQueues electra requested).2.2.2.1) :=
    foldlM_ok_invariant
      (fun t => ((departureQueues electra t).2.2.1, (departureQueues electra t).2.2.2.1) =
        ((departureQueues electra requested).2.2.1, (departureQueues electra requested).2.2.2.1))
      (fun _ _ _ kept h => (withdrawalRequest_consolidationFrame electra h).trans kept)
      rfl withdrawnOk
  have prefixFrame : (departureQueues electra changed).2.2 =
      (departureQueues electra s).2.2 := by
    have one := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra s).2.2)
      (fun _ _ _ kept h =>
        (proposerSlashing_consolidationFrame electra h).trans kept) rfl proposedOk
    have two := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra s).2.2)
      (fun _ _ _ kept h =>
        (attesterSlashing_consolidationFrame electra h).trans kept) one attestedOk
    have three := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra s).2.2)
      (fun _ _ _ kept h =>
        (congrArg (fun q => q.2.2) (attestation_departureQueues electra h)).trans kept)
      two votedOk
    have four := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra s).2.2)
      (fun _ _ _ kept h =>
        (congrArg (fun q => q.2.2) (deposit_departureQueues electra h)).trans kept)
      three depositedOk
    have five := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra s).2.2)
      (fun _ _ _ kept h =>
        (initiateExit_consolidationFrame electra (processVoluntaryExit_initiates h)).trans kept)
      four exitedOk
    exact foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra s).2.2)
      (fun _ _ _ kept h =>
        (congrArg (fun q => q.2.2) (credentials_departureQueues electra h)).trans kept)
      five changedFold
  have lastFrame : t.earliestExitEpoch electra = withdrawn.earliestExitEpoch electra ∧
      t.exitBalanceToConsume electra = withdrawn.exitBalanceToConsume electra :=
    foldlM_ok_invariant (fun t =>
      t.earliestExitEpoch electra = withdrawn.earliestExitEpoch electra ∧
      t.exitBalanceToConsume electra = withdrawn.exitBalanceToConsume electra)
      (fun _ _ _ kept h =>
        let frame := consolidationRequest_exitFrame electra h
        ⟨frame.1.trans kept.1, frame.2.1.trans kept.2⟩) ⟨rfl, rfl⟩ consolidatedOk
  refine ⟨one ++ two, cons, ?_, ?_, oneAppended.append twoAppended, entries, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using coverage
  · have firstEpoch := congrArg Prod.fst depositedFrame
    have firstBalance := congrArg (fun q => q.2.1) depositedFrame
    change requested.earliestExitEpoch electra = changed.earliestExitEpoch electra at firstEpoch
    change requested.exitBalanceToConsume electra = changed.exitBalanceToConsume electra
      at firstBalance
    rw [firstEpoch, firstBalance] at twoTrace
    rw [lastFrame.1, lastFrame.2, List.map_append]
    exact oneTrace.append twoTrace
  · have initial := withdrawnFrame.trans
      ((congrArg (fun q => (q.2.2.1, q.2.2.2.1)) depositedFrame).trans
        (congrArg (fun p => (p.1, p.2.1)) prefixFrame))
    have epoch := congrArg Prod.fst initial
    have balance := congrArg Prod.snd initial
    change withdrawn.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra
      at epoch
    change withdrawn.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra
      at balance
    rw [epoch, balance] at consTrace
    exact consTrace
  · intro called member
    obtain ⟨site, present, first, rate⟩ := consSites called member
    obtain ⟨u, rfl, kept⟩ := consolidationRequestsSites_prefix replayed site present
    have depositedPrefix : SitePrefix changed requested :=
      depositRequests_sitePrefix electra requestedOk
    have withdrawnPrefix : SitePrefix requested withdrawn :=
      withdrawalRequests_sitePrefix electra withdrawnOk
    have priorSite := prior.trans (depositedPrefix.trans (withdrawnPrefix.trans
      ⟨kept.grows, kept.active, kept.effective⟩))
    exact ⟨u, priorSite, priorSite.active.1, rate, first⟩
  · intro called member
    rcases List.mem_append.mp member with member | member
    · exact oneSites called member
    · obtain ⟨site, kept, slot, rate, first⟩ := twoSites called member
      exact ⟨site, prior.trans kept, slot.trans prior.active.1, rate, first⟩
private theorem block_exit_sites {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ calls cons : List (IndexedDepartureCall preset config),
      DepartureCoverage s t (calls ++ cons) ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      (t.pendingPartialWithdrawals electra).data.toList =
        (s.pendingPartialWithdrawals electra).data.toList.drop (blockPartialsTaken s block) ++
          calls.filterMap (·.entry) ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (cons.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      (∀ called ∈ cons, called.entry = none) ∧
      (∀ called ∈ cons, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        getConsolidationChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first) ∧
      ∀ called ∈ calls, ∃ site : BeaconState preset fork,
        SitePrefix s site ∧ site.slot = s.slot ∧
        exitChurnLimit config site = .ok called.call.rate ∧
        computeActivationExitEpoch preset (getCurrentEpoch site) = .ok called.call.first := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  obtain ⟨voted, operated, started, operatedOk, -, syncedOk⟩ := processBlock_operationsInput ok
  obtain ⟨parented, headed, executed, revealed, paidOk, headedOk, executedOk, revealedOk,
    votedOk⟩ := started
  simp only [notGloas, bellatrix, before, altair, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at paidOk executedOk votedOk syncedOk
  subst paidOk
  obtain ⟨calls, cons, covered, trace, appended, entries, consTrace, consSites, sites⟩ :=
    operations_covered_exit_sites electra early operatedOk
  have prior := blockHead_sitePrefix headedOk executedOk revealedOk votedOk
  obtain ⟨planned, plannedOk, executedFrame⟩ :=
    ((blockExecution_departureQueues electra executedOk).resolve_right
      fun ⟨g, _⟩ => Nat.not_le_of_lt early g).2
  have headFrame := blockHead_departureQueues electra headedOk executedFrame revealedOk votedOk
  have taken : blockPartialsTaken s block = planned.processedPartialWithdrawalsCount.toNat := by
    simp [blockPartialsTaken, capella, headedOk, plannedOk, Except.toOption, bind, Except.bind]
  obtain ⟨_, synced⟩ := processSyncAggregate_eq syncedOk
  have tailFrame : departureQueues electra t = departureQueues electra operated := by
    rw [synced]
    rfl
  have headData : voted.validators = s.validators := by
    have input : OperationsInput config checks engine s block voted :=
      ⟨s, headed, executed, revealed, by simp [notGloas, pure, Except.pure], headedOk,
        by simpa only [bellatrix, ↓reduceDIte] using executedOk, revealedOk,
        by simpa only [before, ↓reduceDIte] using votedOk⟩
    exact input.validators_eq early
  have tailData : t.validators = operated.validators := by rw [synced]
  refine ⟨calls, cons, ?_, ?_, ?_, ?_, entries, ?_, ?_⟩
  · intro i old next a b
    exact covered i old next (by simpa only [headData] using a)
      (by simpa only [tailData] using b)
  · have firstEpoch := congrArg Prod.fst headFrame
    have firstBalance := congrArg (fun q => q.2.1) headFrame
    have lastEpoch := congrArg Prod.fst tailFrame
    have lastBalance := congrArg (fun q => q.2.1) tailFrame
    change voted.earliestExitEpoch electra = s.earliestExitEpoch electra at firstEpoch
    change voted.exitBalanceToConsume electra = s.exitBalanceToConsume electra at firstBalance
    change t.earliestExitEpoch electra = operated.earliestExitEpoch electra at lastEpoch
    change t.exitBalanceToConsume electra = operated.exitBalanceToConsume electra at lastBalance
    rw [firstEpoch, firstBalance] at trace
    rw [lastEpoch, lastBalance]
    exact trace
  · have firstQueue := congrArg (fun q => q.2.2.2.2.toList) headFrame
    have lastQueue := congrArg (fun q => q.2.2.2.2.toList) tailFrame
    change (t.pendingPartialWithdrawals electra).data.toList =
      (operated.pendingPartialWithdrawals electra).data.toList at lastQueue
    change (voted.pendingPartialWithdrawals electra).data.toList =
      ((s.pendingPartialWithdrawals electra).data.extract
        planned.processedPartialWithdrawalsCount.toNat
        (s.pendingPartialWithdrawals electra).data.size).toList at firstQueue
    rw [lastQueue, appended, firstQueue, taken]
    simp
  · have initial := congrArg (fun q => (q.2.2.1, q.2.2.2.1)) headFrame
    have firstEpoch := congrArg Prod.fst initial
    have firstBalance := congrArg Prod.snd initial
    have lastEpoch := congrArg (fun q => q.2.2.1) tailFrame
    have lastBalance := congrArg (fun q => q.2.2.2.1) tailFrame
    change voted.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra
      at firstEpoch
    change voted.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra
      at firstBalance
    change t.earliestConsolidationEpoch electra = operated.earliestConsolidationEpoch electra
      at lastEpoch
    change t.consolidationBalanceToConsume electra = operated.consolidationBalanceToConsume electra
      at lastBalance
    rw [firstEpoch, firstBalance] at consTrace
    rw [lastEpoch, lastBalance]
    exact consTrace
  · intro called member
    obtain ⟨site, kept, slot, rate, first⟩ := consSites called member
    exact ⟨site, prior.trans kept, slot.trans prior.active.1, rate, first⟩
  · intro called member
    obtain ⟨site, kept, slot, rate, first⟩ := sites called member
    exact ⟨site, prior.trans kept, slot.trans prior.active.1, rate, first⟩

/-- Upgrades after Electra and before Gloas preserve registry, balances and pending sources. -/
theorem processUpgrades_retained_data {preset : Preset} {config : Config}
    {checks : SignatureChecks} {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) (targetElectra : .pectra ≤ t.fork) :
    t.state.validators.data = s.state.validators.data ∧
      t.state.balances.data = s.state.balances.data ∧
      (t.state.pendingConsolidations targetElectra).data =
        (s.state.pendingConsolidations electra).data :=
  (upgrades_departureQueues electra early ok targetElectra).2

section
variable {partialDebit : ValidatorIndex → BalanceEvent preset → Nat}

private theorem indexed_partial_amounts_le (entries : List PendingPartialWithdrawal)
    (indices : Finset Nat) (small : ∀ i ∈ indices, i < 2 ^ 64) :
    (∑ i ∈ indices, ((entries.filter (·.validatorIndex = UInt64.ofNat i)).map
      (·.amount.toNat)).sum) ≤ (entries.map (·.amount.toNat)).sum := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    have point (i : Nat) :
        (((entry :: entries).filter (·.validatorIndex = UInt64.ofNat i)).map
          (·.amount.toNat)).sum =
        (if entry.validatorIndex = UInt64.ofNat i then entry.amount.toNat else 0) +
          ((entries.filter (·.validatorIndex = UInt64.ofNat i)).map (·.amount.toNat)).sum := by
      by_cases same : entry.validatorIndex = UInt64.ofNat i <;> simp [same]
    simp_rw [point]
    rw [Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    apply Nat.add_le_add _ ih
    have singleton (i : Nat) (member : i ∈ indices) :
        entry.validatorIndex = UInt64.ofNat i ↔ i = entry.validatorIndex.toNat := by
      constructor
      · intro eq
        have converted := congrArg UInt64.toNat eq
        simpa only [UInt64.toNat_ofNat_of_lt' (small i member)] using converted.symm
      · intro eq
        subst i
        simp
    calc
      _ = ∑ i ∈ indices, if i = entry.validatorIndex.toNat then entry.amount.toNat else 0 := by
        apply Finset.sum_congr rfl
        intro i member
        simp only [singleton i member]
      _ ≤ entry.amount.toNat := by
        by_cases member : entry.validatorIndex.toNat ∈ indices <;> simp [member]
private theorem partial_withdrawals_total_le {fork : Fork} {state : BeaconState preset fork}
    {electra : .pectra ≤ fork} {start next : WithdrawalIndex} {partials : Array Withdrawal}
    {count : Nat} (early : fork < .glamsterdam)
    (computed : getPendingPartialWithdrawals state electra start #[] =
      .ok (partials, next, count)) :
    (∑ i ∈ Finset.range state.validators.data.size, withdrawnFrom partials (UInt64.ofNat i)) ≤
      (((state.pendingPartialWithdrawals electra).data.toList.take count).map
        (·.amount.toNat)).sum := by
  have point := (getPendingPartialWithdrawals_taken computed).2
  apply (Finset.sum_le_sum (fun i _ => point (UInt64.ofNat i))).trans
  apply indexed_partial_amounts_le
  intro i member
  have bound := state.validators.bound early
  have size := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  have inside := Finset.mem_range.mp member
  omega
private theorem partial_queue_telescope_due
    (removed remaining initial added : List PendingPartialWithdrawal)
    (cutoff : Nat) (queue : removed ++ remaining = initial ++ added)
    (due : ∀ entry ∈ removed, entry.withdrawableEpoch.toNat ≤ cutoff) :
    (removed.map (·.amount.toNat)).sum +
      ((remaining.filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
            (·.amount.toNat)).sum ≤
      ((initial.filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
            (·.amount.toNat)).sum +
        ((added.filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
              (·.amount.toNat)).sum := by
  have retained : removed.filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff) =
      removed := by
    apply List.filter_eq_self.mpr
    intro entry member
    exact decide_eq_true (due entry member)
  have totals := congrArg (fun entries : List PendingPartialWithdrawal =>
    ((entries.filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
          (·.amount.toNat)).sum) queue
  simp only [List.filter_append, List.map_append, List.sum_append, retained] at totals
  omega
private theorem expected_partial_pass {fork : Fork} {state : BeaconState preset fork}
    {electra : .pectra ≤ fork} {expected : ExpectedWithdrawals}
    (early : fork < .glamsterdam)
    (computed : getExpectedWithdrawals state (Nat.le_trans (by decide) electra) = .ok expected) :
    ∃ partials next,
      getPendingPartialWithdrawals state electra
        (state.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
          .ok (partials, next, expected.processedPartialWithdrawalsCount.toNat) := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold getExpectedWithdrawals at computed
  simp only [notGloas, electra, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
    Except.ok.injEq, liftCount_ok_iff] at computed
  obtain ⟨⟨builders, index1, count1⟩, first, ⟨partials, index2, count2⟩, partialsOk,
    ⟨buildersSweep, index3, count3⟩, third, ⟨sweep, index4, count4⟩, _, _, -, _, ⟨-, rfl⟩, _, -,
    _, -, rfl⟩ := computed
  cases first
  cases third
  exact ⟨partials, index2, partialsOk⟩
/-- A cost of balance events that only payload withdrawals pay.

The debits of all keys select every entry; the debit of one key selects its entries. -/
structure PartialCost (cost : BalanceEvent preset → Nat)
    (keep : PendingPartialWithdrawal → Bool) : Prop where
  -- Every event other than a withdrawals event costs nothing.
  quiet : ∀ e : BalanceEvent preset, e.source ≠ .withdrawals → cost e = 0
  -- A withdrawals event reads queued partial withdrawals.
  --
  -- It costs at most the amounts of those that `keep` selects.
  paid : ∀ {fork : Fork} {state finish : BeaconState preset fork} (electra : .pectra ≤ fork)
    {partials : Array Withdrawal} {next : WithdrawalIndex} {count : Nat} (credit debit : Nat),
    fork < .glamsterdam →
    getPendingPartialWithdrawals state electra
      (state.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] =
        .ok (partials, next, count) →
    cost ⟨.withdrawals, ⟨fork, state⟩, ⟨fork, finish⟩, credit, debit⟩ ≤
      ((((state.pendingPartialWithdrawals electra).data.toList.take count).filter keep).map
        (·.amount.toNat)).sum
  -- Every slot costs nothing.
  slot : ∀ {x y : ForkedBeaconState preset} (ok : advanceSlotAcross config checks x = .ok y),
    y.fork < .glamsterdam → ∀ {events : List (BalanceEvent preset)},
    (Step.slot ok).balanceEvents = .ok events → (events.map cost).sum = 0

variable {cost : BalanceEvent preset → Nat} {keep : PendingPartialWithdrawal → Bool}

private theorem partial_event_expected_le (charged : PartialCost (config := config)
      (checks := checks) cost keep) {fork : Fork} {state finish : BeaconState preset fork}
    {electra : .pectra ≤ fork} {expected : ExpectedWithdrawals} {credit debit : Nat}
    (early : fork < .glamsterdam)
    (computed : getExpectedWithdrawals state (Nat.le_trans (by decide) electra) = .ok expected) :
    cost ⟨.withdrawals, ⟨fork, state⟩, ⟨fork, finish⟩, credit, debit⟩ ≤
      ((((state.pendingPartialWithdrawals electra).data.toList.take
        expected.processedPartialWithdrawalsCount.toNat).filter keep).map (·.amount.toNat)).sum ∧
      ∀ entry ∈ (state.pendingPartialWithdrawals electra).data.toList.take
        expected.processedPartialWithdrawalsCount.toNat,
        entry.withdrawableEpoch ≤ getCurrentEpoch state := by
  obtain ⟨partials, next, partialsOk⟩ := expected_partial_pass early computed
  exact ⟨charged.paid electra credit debit early partialsOk,
    (getPendingPartialWithdrawals_taken partialsOk).1⟩
private theorem execution_partial_consumption (charged : PartialCost (config := config)
      (checks := checks) cost keep) {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} {credit debit : Nat}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    ∃ expected, getExpectedWithdrawals s (Nat.le_trans (by decide) electra) = .ok expected ∧
      (s.pendingPartialWithdrawals electra).data.toList.take
          expected.processedPartialWithdrawalsCount.toNat ++
        (t.pendingPartialWithdrawals electra).data.toList =
          (s.pendingPartialWithdrawals electra).data.toList ∧
      cost ⟨.withdrawals, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ ≤
        ((((s.pendingPartialWithdrawals electra).data.toList.take
          expected.processedPartialWithdrawalsCount.toNat).filter keep).map (·.amount.toNat)).sum ∧
      ∀ entry ∈ (s.pendingPartialWithdrawals electra).data.toList.take
        expected.processedPartialWithdrawalsCount.toNat,
        entry.withdrawableEpoch ≤ getCurrentEpoch s := by
  obtain ⟨expected, expectedOk, queues⟩ :=
    ((blockExecution_departureQueues electra ok).resolve_right
      fun ⟨g, _⟩ => Nat.not_le_of_lt early g).2
  have same := congrArg (fun q => q.2.2.2.2) queues
  change (t.pendingPartialWithdrawals electra).data =
    (s.pendingPartialWithdrawals electra).data.extract
      expected.processedPartialWithdrawalsCount.toNat
      (s.pendingPartialWithdrawals electra).data.size at same
  have reads := partial_event_expected_le charged (electra := electra)
    (finish := t) (credit := credit) (debit := debit)
    early expectedOk
  refine ⟨expected, expectedOk, ?_, reads⟩
  rw [same]
  simp only [Array.toList_extract, List.extract]
  rw [← Array.length_toList, ← List.length_drop, List.take_length]
  exact List.take_append_drop _ _
private theorem block_partial_removal {fork : Fork} {s headed finish : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, s⟩ = false}
    {applied : applySignedBlock config checks engine s signed true = .ok finish}
    {expected : ExpectedWithdrawals}
    (electra : .pectra ≤ fork)
    (header : processBlockHeader s signed.message = .ok headed)
    (computed : getExpectedWithdrawals headed (Nat.le_trans (by decide) electra) =
      .ok expected) :
    (Step.block engine signed due applied).partialsRemoved =
      (headed.pendingPartialWithdrawals electra).data.toList.take
        expected.processedPartialWithdrawalsCount.toNat := by
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have taken : blockPartialsTaken s signed.message =
      expected.processedPartialWithdrawalsCount.toNat := by
    simp [blockPartialsTaken, capella, header, computed, Except.toOption, bind, Except.bind]
  simp only [Step.partialsRemoved, electra, ↓reduceDIte, Step.partialsTaken, taken]
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq header
  rfl
private theorem block_execution_partial_bound (charged : PartialCost (config := config)
      (checks := checks) cost keep) {fork : Fork}
    {s headed executed finish : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, s⟩ = false}
    {applied : applySignedBlock config checks engine s signed true = .ok finish}
    {credit debit : Nat} (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (header : processBlockHeader s signed.message = .ok headed)
    (execution : processBlockExecution config checks engine headed signed.message.body
      (Nat.le_trans (by decide) electra) = .ok executed) :
    cost ⟨.withdrawals, ⟨fork, headed⟩, ⟨fork, executed⟩, credit, debit⟩ ≤
      ((((Step.block engine signed due applied).partialsRemoved).filter keep).map
        (·.amount.toNat)).sum ∧
    ∀ entry ∈ (Step.block engine signed due applied).partialsRemoved,
      entry.withdrawableEpoch ≤ getCurrentEpoch s := by
  obtain ⟨expected, expectedOk, _, bound, dueEntries⟩ :=
    execution_partial_consumption charged (credit := credit)
        (debit := debit) electra early execution
  rw [block_partial_removal electra header expectedOk]
  refine ⟨bound, ?_⟩
  intro entry member
  have dueEntry := dueEntries entry member
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq header
  exact dueEntry
private theorem block_partial_stages {fork : Fork} {s finish : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (applied : applySignedBlock config checks engine s signed true = .ok finish) :
    ∃ headed executed,
      processBlockHeader s signed.message = .ok headed ∧
      processBlockExecution config checks engine headed signed.message.body
        (Nat.le_trans (by decide) electra) = .ok executed := by
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  obtain ⟨_, _, started, _, _, _⟩ :=
    processBlock_operationsInput (applySignedBlock_ok applied).2.1
  obtain ⟨parented, headed, executed, revealed, paidOk, headedOk, executedOk, _, _⟩ := started
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at paidOk
  subst parented
  simp only [bellatrix, ↓reduceDIte] at executedOk
  exact ⟨headed, executed, headedOk, executedOk⟩
private theorem record_nonwithdrawal_filter {fork : Fork} {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {pre post : BalanceReplay preset fork} (different : source ≠ .withdrawals)
    (ok : recordBalance source limits action pre = .ok post) :
    post.2.filter (fun e => e.source == .withdrawals) =
      pre.2.filter (fun e => e.source == .withdrawals) := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, after, _, rfl⟩ := ok
  simp [List.filter_append, different]
private theorem carry_withdrawal_filter {fork : Fork}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {pre post : BalanceReplay preset fork} (ok : carryBalance action pre = .ok post) :
    post.2.filter (fun e => e.source == .withdrawals) =
      pre.2.filter (fun e => e.source == .withdrawals) := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  rfl
private theorem block_withdrawal_filter {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork) (electra : .pectra ≤ fork)
    {post : BalanceReplay preset fork}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) :
    ∃ headed executed credit debit,
      processBlockHeader s block = .ok headed ∧
      processBlockExecution config checks engine headed block.body
        (Nat.le_trans (by decide) electra) = .ok executed ∧
      post.2.filter (fun e => e.source == .withdrawals) =
        [⟨.withdrawals, ⟨fork, headed⟩, ⟨fork, executed⟩, credit, debit⟩] := by
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have preserve {pre post : BalanceReplay preset fork}
      {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
      (ok : carryBalance action pre = .ok post) :
      post.2.filter (fun e => e.source == .withdrawals) =
        pre.2.filter (fun e => e.source == .withdrawals) := carry_withdrawal_filter ok
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headerOk, ok⟩ := bind_ok_iff.mp ok
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at headerOk
  obtain ⟨head, header, rfl⟩ := headerOk
  simp only [bellatrix, ↓reduceDIte] at ok
  obtain ⟨executed, executionOk, rest⟩ := bind_ok_iff.mp ok
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at executionOk
  obtain ⟨⟨credit, debit⟩, _, after, execution, rfl⟩ := executionOk
  simp only [bind_ok_iff] at rest
  obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
    proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
    exited, exitOk, changed, changedOk, rest⟩ := rest
  have first := preserve randaoOk
  have second := (preserve votedOk).trans first
  have proposedKept := foldlM_ok_invariant
    (fun pre => pre.2.filter (fun e => e.source == .withdrawals) =
      [⟨.withdrawals, ⟨fork, head⟩, ⟨fork, after⟩, credit, debit⟩])
    (fun _ _ _ prior step => (record_nonwithdrawal_filter (by decide) step).trans prior)
    (by simpa using second) proposedOk
  have attestedKept := foldlM_ok_invariant _
    (fun _ _ _ prior step => (record_nonwithdrawal_filter (by decide) step).trans prior)
    proposedKept attestedOk
  have rewardedKept := foldlM_ok_invariant _
    (fun _ _ _ prior step => (record_nonwithdrawal_filter (by decide) step).trans prior)
    attestedKept rewardedOk
  have depositedKept := foldlM_ok_invariant _
    (fun _ _ _ prior step => (record_nonwithdrawal_filter (by decide) step).trans prior)
    rewardedKept depositOk
  have changedKept := (preserve changedOk).trans ((preserve exitOk).trans depositedKept)
  simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨deposits, depositsOk, withdrawals, withdrawalsOk, requested, requestsOk, rest⟩ := rest
  have requestedKept := foldlM_ok_invariant _
    (fun _ _ _ prior step => (record_nonwithdrawal_filter (by decide) step).trans prior)
    ((preserve withdrawalsOk).trans ((preserve depositsOk).trans changedKept)) requestsOk
  refine ⟨head, after, credit, debit, header, execution, ?_⟩
  split at rest
  · exact (record_nonwithdrawal_filter (by decide) rest).trans requestedKept
  · cases rest; exact requestedKept
private theorem partial_sum_filter (charged : PartialCost (config := config) (checks := checks)
      cost keep) (events : List (BalanceEvent preset)) :
    (events.map cost).sum =
      ((events.filter (fun e => e.source == .withdrawals)).map cost).sum := by
  induction events with
  | nil => rfl
  | cons e events ih =>
    by_cases source : e.source = .withdrawals
    · simpa [source] using congrArg (fun total => cost e + total) ih
    · simpa [source, charged.quiet e source] using ih
private theorem block_partial_sum (charged : PartialCost (config := config) (checks := checks)
      cost keep) {fork : Fork} {s finish : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, s⟩ = false}
    {applied : applySignedBlock config checks engine s signed true = .ok finish}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due applied).balanceEvents = .ok events) :
    (events.map cost).sum ≤
      ((((Step.block engine signed due applied).partialsRemoved).filter keep).map
        (·.amount.toNat)).sum ∧
    ∀ entry ∈ (Step.block engine signed due applied).partialsRemoved,
      entry.withdrawableEpoch ≤ getCurrentEpoch s := by
  obtain ⟨headed, executed, credit, debit, header, execution, filtered⟩ :=
    block_withdrawal_filter early engine signed.message electra
      (Step.balanceEvents_block early replayed)
  have bound :=
      block_execution_partial_bound charged (due := due)
      (applied := applied)
    (credit := credit) (debit := debit) electra early header execution
  rw [partial_sum_filter charged, filtered]
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    using bound
/-- Before Gloas, a computed consolidation churn limit reads a total active balance. -/
theorem consolidationChurnLimit_total {fork : Fork} {s : BeaconState preset fork}
    {rate : Gwei} (early : fork < .glamsterdam)
    (computed : getConsolidationChurnLimit config s = .ok rate) :
    ∃ total, getTotalActiveBalance s = .ok total := by
  simp only [getConsolidationChurnLimit,
    show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early, ↓reduceIte,
    getBalanceChurnLimit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, ⟨total, read, _⟩, _⟩ := computed
  exact ⟨total, read⟩
variable (slot_zero : ∀ {x y : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks x = .ok y) (_early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)},
    (Step.slot ok).balanceEvents = .ok events →
    (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
      partialDebit (UInt64.ofNat i) e).sum = 0)

private theorem step_partial_sum (charged : PartialCost (config := config) (checks := checks)
      cost keep) {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : step.balanceEvents = .ok events) :
    (events.map cost).sum ≤ ((step.partialsRemoved.filter keep).map (·.amount.toNat)).sum ∧
    ∀ entry ∈ step.partialsRemoved,
      entry.withdrawableEpoch ≤ getCurrentEpoch x.state := by
  cases step with
  | slot ok =>
    rw [charged.slot ok early replayed]
    exact ⟨Nat.zero_le _, by simp [Step.partialsRemoved, electra, Step.partialsTaken]⟩
  | block engine signed due applied =>
    exact block_partial_sum charged electra early replayed
private theorem run_partial_sum (charged : PartialCost (config := config) (checks := checks)
      cost keep) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map cost).sum ≤ ((tail.partialsRemoved.filter keep).map (·.amount.toNat)).sum ∧
    ∀ entry ∈ tail.partialsRemoved,
      entry.withdrawableEpoch ≤ getCurrentEpoch y.state := by
  induction tail generalizing events with
  | nil =>
    cases replayed
    exact ⟨by simp [Run.partialsRemoved], by simp [Run.partialsRemoved]⟩
  | @snoc middle last pre step ih =>
    have middleElectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    have first := ih middleEarly priorOk
    have later := step.chainStep.currentEpoch_le
    have lastDue : ∀ entry ∈ step.partialsRemoved,
        entry.withdrawableEpoch ≤ getCurrentEpoch last.state := by
      cases step with
      | slot ok => simp [Step.partialsRemoved, Step.partialsTaken]
      | block engine signed due applied =>
        obtain ⟨headed, executed, header, execution⟩ :=
          block_partial_stages middleElectra early applied
        have bound := block_execution_partial_bound charged (due := due) (applied := applied)
          (credit := 0) (debit := 0) middleElectra early header execution
        exact fun entry member => UInt64.le_trans (bound.2 entry member) later
    constructor
    · split at rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        have one := (step_partial_sum charged step middleElectra early addedOk).1
        simp only [List.map_append, List.sum_append, Run.partialsRemoved, List.filter_append]
        omega
      · cases rest
        simp only [Run.partialsRemoved, List.map_append, List.sum_append, List.filter_append]
        omega
    · intro entry member
      rcases List.mem_append.mp member with old | new
      · exact UInt64.le_trans (first.2 entry old) later
      · exact lastDue entry new
/-- The cost of the events of a branch is at most its selected entries due by a cutoff.

The entries are those of the queue at its start and those appended along it.

The cutoff is at or after its end.

The removed entries, then the queue at the end, are the start queue, then the appended ones. -/
private theorem run_partial_queue_due_of
    (charged : PartialCost (config := config) (checks := checks) cost keep)
    {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (cutoff : Nat) (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff)
    (added : List PendingPartialWithdrawal)
    (queue : tail.partialsRemoved ++
        (y.state.pendingPartialWithdrawals
          (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps))).data.toList =
      (x.state.pendingPartialWithdrawals electra).data.toList ++ added) :
    (events.map cost).sum +
      ((((y.state.pendingPartialWithdrawals
        (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps))).data.toList.filter
          keep).filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
            (·.amount.toNat)).sum ≤
      ((((x.state.pendingPartialWithdrawals electra).data.toList.filter keep).filter
        (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum +
      (((added.filter keep).filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
        (·.amount.toNat)).sum := by
  have replay := run_partial_sum charged tail electra early replayed
  have kept := congrArg (List.filter keep) queue
  simp only [List.filter_append] at kept
  exact (Nat.add_le_add_right replay.1 _).trans (partial_queue_telescope_due _ _ _ _ cutoff kept
    (fun entry member => (UInt64.le_iff_toNat_le.mp
      (replay.2 entry (List.mem_of_mem_filter member))).trans endpoint))
include slot_zero in
/-- The debits of all keys are a cost that selects every queued entry. -/
private theorem partialCost_all
    (partialDebit_eq : partialDebit = fun i event =>
  if event.source = .withdrawals then
    if electra : .pectra ≤ event.before.fork then
      match getPendingPartialWithdrawals event.before.state electra
          (event.before.state.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] with
      | .ok (partials, _, _) => withdrawnFrom partials i
      | .error _ => 0
    else 0
  else 0) :
    PartialCost (config := config) (checks := checks)
      (fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        partialDebit (UInt64.ofNat i) e) (fun _ => true) where
  quiet e source := by simp [partialDebit_eq, source]
  paid := by
    intro _ _ _ electra _ _ _ _ _ early computed
    simpa only [partialDebit_eq, electra, ↓reduceIte, ↓reduceDIte, computed, List.filter_true]
      using partial_withdrawals_total_le early computed
  slot ok early _ replayed := slot_zero ok early replayed
include slot_zero in
private theorem run_partial_queue_due
    (partialDebit_eq : partialDebit = fun i event =>
  if event.source = .withdrawals then
    if electra : .pectra ≤ event.before.fork then
      match getPendingPartialWithdrawals event.before.state electra
          (event.before.state.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] with
      | .ok (partials, _, _) => withdrawnFrom partials i
      | .error _ => 0
    else 0
  else 0) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (cutoff : Nat) (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff)
    (added : List PendingPartialWithdrawal)
    (queue : tail.partialsRemoved ++
        (y.state.pendingPartialWithdrawals
          (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps))).data.toList =
      (x.state.pendingPartialWithdrawals electra).data.toList ++ added) :
    (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
      partialDebit (UInt64.ofNat i) e).sum ≤
      (((x.state.pendingPartialWithdrawals electra).data.toList.filter
        (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum +
      ((added.filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
        (·.amount.toNat)).sum := by
  have net := run_partial_queue_due_of
    (partialCost_all slot_zero partialDebit_eq) tail electra early replayed cutoff endpoint
    added queue
  simp only [List.filter_true] at net
  exact Nat.le_of_add_right_le net
private theorem partials_entries_due_sum (calls : List (IndexedDepartureCall preset config))
    (cutoff : Nat) :
    (((calls.filterMap (·.entry)).filter
      (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum =
    ((calls.filter fun called => called.index.isNone &&
      decide (called.call.epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        cutoff)).map (·.call.amount.toNat)).sum := by
  induction calls with
  | nil => rfl
  | cons called rest ih =>
    cases entry : called.entry with
    | none =>
      have indexed : called.index.isNone = false := by
        cases index : called.index with
        | none => simpa [entry] using called.tagged.mp index
        | some _ => rfl
      simp [entry, indexed, ih]
    | some pending =>
      have unindexed : called.index = none := called.tagged.mpr (by simp [entry])
      have pushed := called.pushed pending entry
      have due : pending.withdrawableEpoch.toNat ≤ cutoff ↔
          called.call.epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            cutoff := by
        rw [pushed.2]
      by_cases ready : pending.withdrawableEpoch.toNat ≤ cutoff
      · simp [entry, unindexed, ready, due.mp ready, pushed.1, ih]
      · have late := mt due.mpr ready
        simp [entry, unindexed, ready, late, ih]
private theorem departure_charges_indexed {charges : List DepartureCharge}
    {calls : List (IndexedDepartureCall preset config)}
    (unique : (charges.map (·.index)).Nodup)
    (matched : ∀ charge ∈ charges, ∃ called ∈ calls,
      called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
        called.call.amount.toNat = charge.amount) (cutoff : Nat) :
    ((charges.filter fun charge => charge.epoch ≤ cutoff).map (·.amount)).sum ≤
      (((calls.filter (·.index.isSome)).filter
        (fun called => called.call.epoch.toNat ≤ cutoff)).map (·.call.amount.toNat)).sum := by
  apply departureCharges_le_calls unique
  intro charge member
  obtain ⟨called, present, index, epoch, amount⟩ := matched charge member
  refine ⟨called, List.mem_filter.mpr ⟨present, ?_⟩, index, epoch, amount⟩
  simp [index]
private theorem indexed_partial_calls_disjoint
    (calls : List (IndexedDepartureCall preset config)) (cutoff : Nat) :
    (((calls.filter (·.index.isSome)).filter
      (fun called => called.call.epoch.toNat ≤ cutoff)).map (·.call.amount.toNat)).sum +
    ((calls.filter fun called => called.index.isNone &&
      decide (called.call.epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        cutoff)).map (·.call.amount.toNat)).sum ≤
    ((calls.filter fun called => called.call.epoch.toNat ≤ cutoff).map
      (·.call.amount.toNat)).sum := by
  induction calls with
  | nil => exact Nat.le_refl _
  | cons called rest ih =>
    simp only [List.filter_filter] at ih
    cases index : called.index with
    | none =>
      by_cases due : called.call.epoch.toNat +
          config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤ cutoff
      · have before : called.call.epoch.toNat ≤ cutoff := by omega
        simp [index, due, before]; omega
      · by_cases before : called.call.epoch.toNat ≤ cutoff <;> simp [index, due, before] <;> omega
    | some i =>
      by_cases before : called.call.epoch.toNat ≤ cutoff <;> simp [index, before] <;> omega
include slot_zero in
/-- Joint departure charges and partial payments fit the two queue windows. -/
theorem run_joint_partial_window
    (partialDebit_eq : partialDebit = fun i event =>
  if event.source = .withdrawals then
    if electra : .pectra ≤ event.before.fork then
      match getPendingPartialWithdrawals event.before.state electra
          (event.before.state.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] with
      | .ok (partials, _, _) => withdrawnFrom partials i
      | .error _ => 0
    else 0
  else 0) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1) (cap : Nat)
    (rates : ∀ {u v : ForkedBeaconState preset} (step : Step config checks u v),
      tail.Contains step → .pectra ≤ u.fork →
      ∀ total, getTotalActiveBalance u.state = .ok total → ∀ rate : Gwei,
        getConsolidationChurnLimit config u.state = .ok rate → rate.toNat ≤ cap) :
    ((tail.departureCharges.filter fun charge => charge.epoch ≤ high + 1).map (·.amount)).sum +
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        partialDebit (UInt64.ofNat i) e).sum ≤
      (((x.state.pendingPartialWithdrawals electra).data.toList.filter
        (fun entry => entry.withdrawableEpoch.toNat ≤ high + 1)).map (·.amount.toNat)).sum +
      (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
        (x.state.exitBalanceToConsume electra).toNat else 0) +
      (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
        (x.state.consolidationBalanceToConsume electra).toNat else 0) +
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (x.state.earliestExitEpoch electra).toNat) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
      (high + 2 - max (getCurrentEpoch x.state).toNat
        (x.state.earliestConsolidationEpoch electra).toNat) * cap := by
  replace rates : ∀ site ∈ tail.consolidationSites, .pectra ≤ site.fork → ∀ rate : Gwei,
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap := by
    intro site member electra rate computed
    obtain ⟨_, _, step, contained, forks, same⟩ := consolidationSite_rate tail early site member
    have computed := same rate computed
    obtain ⟨_, _, _, sourceEarly, _⟩ := Apriori.Internal.Run.contains_step_facts contained early
    obtain ⟨total, read⟩ := consolidationChurnLimit_total sourceEarly computed
    exact rates step contained (forks electra) total read rate computed
  obtain ⟨calls, matched, queues, _, budget⟩ :=
    exit_calls_le_window_electra tail electra early high cap rates
  have target := Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)
  have partials :=
      run_partial_queue_due (partialDebit_eq := partialDebit_eq) (slot_zero := slot_zero) tail
      electra early replayed (high + 1) endpoint
    (calls.filterMap (·.entry)) (queues target).2
  rw [partials_entries_due_sum] at partials
  have charges := departure_charges_indexed (departureCharges_run_indices tail) matched (high + 1)
  have disjoint := indexed_partial_calls_disjoint calls (high + 1)
  omega

end

section
variable {x : ForkedBeaconState preset}
variable {ceilingValue exitEnvelope consEnvelope : Nat → Nat}
variable (callRate : ∀ {fork : Fork} {s : BeaconState preset fork}
    (_early : fork < .glamsterdam) (call : DepartureQueueCall),
    computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first →
    exitChurnLimit config s = .ok call.rate → ∀ {total : Gwei},
    getTotalActiveBalance s = .ok total →
    total.toNat ≤ ceilingValue ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat) →
    ∀ n, call.first.toNat ≤ n → call.earliest.toNat < n → n ≤ call.epoch.toNat →
    call.rate.toNat ≤ exitEnvelope (n - (getCurrentEpoch x.state).toNat))
variable (consRate : ∀ {fork : Fork} {s : BeaconState preset fork}
    (_early : fork < .glamsterdam) {total rate : Gwei},
    getTotalActiveBalance s = .ok total →
    getConsolidationChurnLimit config s = .ok rate → ∀ {atEpoch : Nat},
    total.toNat ≤ ceilingValue atEpoch → rate.toNat ≤ consEnvelope (ceilingValue atEpoch))
variable (consMono : Monotone (fun atEpoch => consEnvelope (ceilingValue atEpoch)))

/-- Before Gloas, a computed exit churn limit reads a total active balance. -/
theorem exitChurnLimit_total {fork : Fork} {s : BeaconState preset fork} {rate : Gwei}
    (early : fork < .glamsterdam) (computed : exitChurnLimit config s = .ok rate) :
    ∃ total, getTotalActiveBalance s = .ok total := by
  simp only [exitChurnLimit, show ¬ .glamsterdam ≤ fork from Nat.not_le_of_lt early,
    ↓reduceIte, getActivationExitChurnLimit, getBalanceChurnLimit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, ⟨total, read, _⟩, _⟩ := computed
  exact ⟨total, read⟩
include callRate in
private theorem registry_fold_exit_rates
    {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {activation : Epoch}
    {indices : List Nat}
    (later : (getCurrentEpoch s).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < activation.toNat)
    (ok : indices.foldlM (updateRegistryEntryElectra config activation) s = .ok t)
    (ceiling : ∀ total, getTotalActiveBalance s = .ok total → total.toNat ≤ ceilingValue
      ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      ∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat) := by
  obtain ⟨calls, trace, coverage, appended, sites⟩ :=
    registry_fold_exit_sites electra early later ok
  refine ⟨calls, trace, coverage, appended, ?_, ?_⟩
  · exact (callsFrom_of_sites (s := s) (calls := calls) fun called member => by
      obtain ⟨site, _, slot, _, first⟩ := sites called member
      exact ⟨site, slot, first⟩).mono (by omega)
  intro called member
  obtain ⟨site, kept, slot, rate, first⟩ := sites called member
  obtain ⟨total, totalRead⟩ := exitChurnLimit_total early rate
  have read : getTotalActiveBalance s = .ok total :=
    (exit_site_total_eq kept).symm.trans totalRead
  have siteCeiling : total.toNat ≤ ceilingValue
      ((getCurrentEpoch site).toNat - (getCurrentEpoch x.state).toNat) := by
    simpa only [getCurrentEpoch, slot] using ceiling total read
  exact callRate early called.call first rate totalRead siteCeiling
include callRate consRate in
private theorem block_exit_rates
    {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t)
    (ceiling : ∀ total, getTotalActiveBalance s = .ok total → total.toNat ≤ ceilingValue
      ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls cons : List (IndexedDepartureCall preset config),
      DepartureCoverage s t (calls ++ cons) ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      (t.pendingPartialWithdrawals electra).data.toList =
        (s.pendingPartialWithdrawals electra).data.toList.drop (blockPartialsTaken s block) ++
          calls.filterMap (·.entry) ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (cons.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      (∀ called ∈ cons, called.entry = none) ∧
      DepartureCallsFrom (getCurrentEpoch s).toNat cons ∧
      (∀ called ∈ cons, called.call.rate.toNat ≤ consEnvelope
        (ceilingValue
          ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat))) ∧
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      ∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat) := by
  obtain ⟨calls, cons, covered, trace, appended, consTrace, entries, consSites, sites⟩ :=
    block_exit_sites electra early ok
  refine ⟨calls, cons, covered, trace, appended, consTrace, entries, ?_, ?_, ?_, ?_⟩
  · exact (callsFrom_of_sites (s := s) (calls := cons) fun called member => by
      obtain ⟨site, _, slot, _, first⟩ := consSites called member
      exact ⟨site, slot, first⟩).mono (by omega)
  · intro called member
    obtain ⟨site, kept, _, rate, _⟩ := consSites called member
    obtain ⟨total, totalRead⟩ := consolidationChurnLimit_total early rate
    have read : getTotalActiveBalance s = .ok total :=
      (exit_site_total_eq kept).symm.trans totalRead
    exact consRate early totalRead rate (ceiling total read)
  · exact (callsFrom_of_sites (s := s) (calls := calls) fun called member => by
      obtain ⟨site, _, slot, _, first⟩ := sites called member
      exact ⟨site, slot, first⟩).mono (by omega)
  intro called member
  obtain ⟨site, kept, slot, rate, first⟩ := sites called member
  obtain ⟨total, totalRead⟩ := exitChurnLimit_total early rate
  have read : getTotalActiveBalance s = .ok total :=
    (exit_site_total_eq kept).symm.trans totalRead
  have siteCeiling : total.toNat ≤ ceilingValue
      ((getCurrentEpoch site).toNat - (getCurrentEpoch x.state).toNat) := by
    simpa only [getCurrentEpoch, slot] using ceiling total read
  exact callRate early called.call first rate totalRead siteCeiling
include callRate in
private theorem registry_updates_exit_rates
    {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    (ok : processRegistryUpdates config s = .ok t)
    (ceiling : ∀ total, getTotalActiveBalance s = .ok total → total.toNat ≤ ceilingValue
      ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ PartialsAppended electra s t calls ∧
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      ∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat) := by
  simp only [processRegistryUpdates, electra, ↓reduceIte, bind_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨activation, computed, entries⟩ := ok
  simp only [liftArith, mapError_ok_iff] at computed
  have exactEpoch := (computeActivationExitEpoch_ok_iff.mp computed).2
  have later : (getCurrentEpoch s).toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
      activation.toNat := by omega
  exact registry_fold_exit_rates (callRate := callRate)  electra early later entries ceiling
include callRate in
private theorem epoch_exit_rates
    {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    (ok : processEpoch config checks s = .ok t)
    (ceiling : ∀ total, getTotalActiveBalance s = .ok total → total.toNat ≤ ceilingValue
      ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧
      PartialsAppended electra s t calls ∧
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      ∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat) := by
  obtain ⟨rewarded, registered, entriesOk, slot, validators, cut⟩ :=
    epoch_registry_cut electra early ok
  have totalEq : getTotalActiveBalance rewarded = getTotalActiveBalance s := by
    simp only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getCurrentEpoch,
      slot, validators, getTotalBalance]
    rfl
  have rewardedCeiling : ∀ total, getTotalActiveBalance rewarded = .ok total →
      total.toNat ≤ ceilingValue
      ((getCurrentEpoch rewarded).toNat - (getCurrentEpoch x.state).toNat) := by
    intro total read
    simpa only [getCurrentEpoch, slot] using ceiling total (totalEq.symm.trans read)
  obtain ⟨calls, queued, covered, appended, firsts, rates⟩ :=
    registry_updates_exit_rates (callRate := callRate) electra early entriesOk rewardedCeiling
  obtain ⟨trace, coverage, partials⟩ := cut calls queued covered appended
  refine ⟨calls, trace, coverage, partials, ?_, rates⟩
  simpa only [getCurrentEpoch, slot] using firsts
include callRate in
private theorem slot_exit_rates
    {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    (ok : advanceSlot config checks s = .ok t)
    (ceiling : ∀ total, getTotalActiveBalance s = .ok total → total.toNat ≤ ceilingValue
      ((getCurrentEpoch s).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧
      PartialsAppended electra s t calls ∧
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      ∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat) := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨calls, trace, covered, appended, firsts, rates⟩ :=
      epoch_exit_rates (callRate := callRate)  electra early advance ceiling
    exact ⟨calls, trace, covered, appended, firsts, rates⟩
  · cases advance
    exact ⟨[], .nil _ _, .of_data rfl, .of_kept rfl, by simp [DepartureCallsFrom], by simp⟩
include callRate consRate in
private theorem step_exit_rates
    {u v : ForkedBeaconState preset}
    (step : Step config checks u v) (electra : .pectra ≤ u.fork)
    (early : v.fork < .glamsterdam) (targetElectra : .pectra ≤ v.fork)
    (ceiling : ∀ total, getTotalActiveBalance u.state = .ok total → total.toNat ≤ ceilingValue
      ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls cons : List (IndexedDepartureCall preset config),
      DepartureCoverage u.state v.state (calls ++ cons) ∧
      DepartureQueueTrace (u.state.earliestExitEpoch electra)
        (u.state.exitBalanceToConsume electra) (calls.map (·.call))
        (v.state.earliestExitEpoch targetElectra) (v.state.exitBalanceToConsume targetElectra) ∧
      (v.state.pendingPartialWithdrawals targetElectra).data.toList =
        (u.state.pendingPartialWithdrawals electra).data.toList.drop step.partialsTaken ++
          calls.filterMap (·.entry) ∧
      DepartureQueueTrace (u.state.earliestConsolidationEpoch electra)
        (u.state.consolidationBalanceToConsume electra) (cons.map (·.call))
        (v.state.earliestConsolidationEpoch targetElectra)
        (v.state.consolidationBalanceToConsume targetElectra) ∧
      (∀ called ∈ cons, called.entry = none) ∧
      DepartureCallsFrom (getCurrentEpoch u.state).toNat cons ∧
      (∀ called ∈ cons, called.call.rate.toNat ≤ consEnvelope
        (ceilingValue
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat))) ∧
      DepartureCallsFrom (getCurrentEpoch u.state).toNat calls ∧
      ∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat) := by
  have sourceEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    obtain ⟨frame, data⟩ := upgrades_departureQueues (s := ⟨u.fork, advanced⟩)
      electra early upgraded targetElectra
    obtain ⟨calls, trace, covered, appended, firsts, rates⟩ :=
      slot_exit_rates (callRate := callRate)  electra sourceEarly advancedOk ceiling
    have epoch := congrArg Prod.fst frame
    have balance := congrArg (fun q => q.2.1) frame
    have queue := congrArg (fun q => q.2.2.2.2.toList) frame
    change v.state.earliestExitEpoch targetElectra = advanced.earliestExitEpoch electra at epoch
    change v.state.exitBalanceToConsume targetElectra = advanced.exitBalanceToConsume electra
      at balance
    change (v.state.pendingPartialWithdrawals targetElectra).data.toList =
      (advanced.pendingPartialWithdrawals electra).data.toList at queue
    refine ⟨calls, [], ?_, ?_, ?_, ?_, by simp, by simp [DepartureCallsFrom],
      by simp, firsts, rates⟩
    · simpa only [List.append_nil] using
        (show DepartureCoverage u.state v.state calls from fun i old next before after =>
          covered i old next before (by simpa only [data] using after))
    · rw [epoch, balance]
      exact trace
    · rw [queue, appended]
      rfl
    · have both := (congrArg (fun q => q.2.2) frame).trans
        (slot_consolidationFrame electra sourceEarly advancedOk)
      have epoch := congrArg Prod.fst both
      have balance := congrArg (fun q => q.2.1) both
      change v.state.earliestConsolidationEpoch targetElectra =
        u.state.earliestConsolidationEpoch electra at epoch
      change v.state.consolidationBalanceToConsume targetElectra =
        u.state.consolidationBalanceToConsume electra at balance
      rw [epoch, balance]
      exact .nil _ _
  | block engine signed due ok =>
    exact block_exit_rates (callRate := callRate) (consRate := consRate)  electra early
        (applySignedBlock_ok ok).2.1 ceiling
include callRate consRate consMono in
private theorem run_exit_rates
    (electraX : .pectra ≤ x.fork) {y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (targetElectra : .pectra ≤ y.fork)
    (ceilings : ∀ {u v} (step : Step config checks u v), tail.Contains step →
      ∀ total, getTotalActiveBalance u.state = .ok total → total.toNat ≤
        ceilingValue
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls cons : List (IndexedDepartureCall preset config),
      (∀ charge ∈ tail.departureCharges, ∃ called ∈ calls ++ cons,
        called.index = some charge.index ∧ called.call.epoch.toNat = charge.epoch ∧
          called.call.amount.toNat = charge.amount) ∧
      DepartureQueueTrace (x.state.earliestExitEpoch electraX)
        (x.state.exitBalanceToConsume electraX) (calls.map (·.call))
        (y.state.earliestExitEpoch targetElectra) (y.state.exitBalanceToConsume targetElectra) ∧
      tail.partialsRemoved ++ (y.state.pendingPartialWithdrawals targetElectra).data.toList =
        (x.state.pendingPartialWithdrawals electraX).data.toList ++ calls.filterMap (·.entry) ∧
      DepartureQueueTrace (x.state.earliestConsolidationEpoch electraX)
        (x.state.consolidationBalanceToConsume electraX) (cons.map (·.call))
        (y.state.earliestConsolidationEpoch targetElectra)
        (y.state.consolidationBalanceToConsume targetElectra) ∧
      (∀ called ∈ cons, called.entry = none) ∧
      DepartureCallsFrom (getCurrentEpoch x.state).toNat cons ∧
      (∀ called ∈ cons, called.call.rate.toNat ≤ consEnvelope
        (ceilingValue
          ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat))) ∧
      DepartureCallsFrom (getCurrentEpoch x.state).toNat calls ∧
      ∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat) := by
  induction tail with
  | nil => exact ⟨[], [], by simp [Run.departureCharges], .nil _ _, by simp [Run.partialsRemoved],
      .nil _ _, by simp, by simp [DepartureCallsFrom], by simp,
      by simp [DepartureCallsFrom], by simp⟩
  | @snoc middle last pre step ih =>
    have middleElectra := Nat.le_trans electraX (fork_le_of_chainSteps pre.chainSteps)
    obtain ⟨one, firstCons, firstMatched, oneTrace, oneQueue, firstConsTrace, firstEntries,
      firstConsFrom, firstConsRates, oneFrom, oneRates⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) middleElectra
        (fun previous member => ceilings previous (.earlier member _))
    obtain ⟨two, lastCons, covered, twoTrace, twoQueue, lastConsTrace, lastEntries,
      lastConsFrom, lastConsRates, twoFrom, twoRates⟩ :=
      step_exit_rates (callRate := callRate) (consRate := consRate)  step middleElectra early
          targetElectra
        (ceilings step (.last _ _))
    have removed : step.partialsRemoved =
        (middle.state.pendingPartialWithdrawals middleElectra).data.toList.take
          step.partialsTaken := by
      unfold Step.partialsRemoved
      split
      · rfl
      · contradiction
    refine ⟨one ++ two, firstCons ++ lastCons, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro charge member
      rcases List.mem_append.mp member with earlier | latest
      · obtain ⟨called, present, paired⟩ := firstMatched charge earlier
        refine ⟨called, ?_, paired⟩
        simp only [List.mem_append] at present ⊢
        exact present.elim (fun h => .inl (.inl h)) (fun h => .inr (.inl h))
      · obtain ⟨called, present, paired⟩ := covered.step_charges step charge latest
        refine ⟨called, ?_, paired⟩
        simp only [List.mem_append] at present ⊢
        exact present.elim (fun h => .inl (.inr h)) (fun h => .inr (.inr h))
    · simpa only [List.map_append] using oneTrace.append twoTrace
    · rw [Run.partialsRemoved, removed, twoQueue, List.filterMap_append, List.append_assoc,
        ← List.append_assoc (List.take _ _), List.take_append_drop, ← List.append_assoc,
        oneQueue, List.append_assoc]
    · simpa only [List.map_append] using firstConsTrace.append lastConsTrace
    · intro called member
      exact (List.mem_append.mp member).elim (firstEntries called) (lastEntries called)
    · exact firstConsFrom.append (lastConsFrom.mono
        (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)))
    · have epochOrder := UInt64.le_iff_toNat_le.mp
        step.chainStep.currentEpoch_le
      have ordered : (getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat ≤
          (getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat := by omega
      have cap := consMono ordered
      intro called member
      exact (List.mem_append.mp member).elim
        (fun h => (firstConsRates called h).trans cap)
        (fun h => (lastConsRates called h).trans cap)
    · exact oneFrom.append (twoFrom.mono
        (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)))
    · intro called member
      exact (List.mem_append.mp member).elim (oneRates called) (twoRates called)

include callRate in
/-- Partial debits fit the initial queue and the appended exit-call trace. -/
theorem run_partial_queue_trace
    {partialDebit : ValidatorIndex → BalanceEvent preset → Nat}
    (partialDebit_eq : partialDebit = fun i event =>
      if event.source = .withdrawals then
        if electra : .pectra ≤ event.before.fork then
          match getPendingPartialWithdrawals event.before.state electra
              (event.before.state.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] with
          | .ok (partials, _, _) => withdrawnFrom partials i
          | .error _ => 0
        else 0
      else 0)
    (slot_zero : ∀ {u v : ForkedBeaconState preset}
      (ok : advanceSlotAcross config checks u = .ok v) (_early : v.fork < .glamsterdam)
      {events : List (BalanceEvent preset)}, (Step.slot ok).balanceEvents = .ok events →
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        partialDebit (UInt64.ofNat i) e).sum = 0)
    (high horizon : Nat)
    (electra : .pectra ≤ x.fork) {y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ horizon)
    (ceilings : ∀ {u v} (step : Step config checks u v), tail.Contains step →
      ∀ total, getTotalActiveBalance u.state = .ok total → total.toNat ≤
        ceilingValue ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)) :
    ∃ calls : List (IndexedDepartureCall preset config),
      DepartureQueueTrace (x.state.earliestExitEpoch electra)
        (x.state.exitBalanceToConsume electra) (calls.map (·.call))
        (y.state.earliestExitEpoch (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)))
        (y.state.exitBalanceToConsume
              (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps))) ∧
      DepartureCallsFrom (getCurrentEpoch x.state).toNat calls ∧
      (∀ called ∈ calls, ∀ n, called.call.first.toNat ≤ n → called.call.earliest.toNat < n →
        n ≤ called.call.epoch.toNat → called.call.rate.toNat ≤
          exitEnvelope (n - (getCurrentEpoch x.state).toNat)) ∧
      (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
        partialDebit (UInt64.ofNat i) e).sum ≤
        (((x.state.pendingPartialWithdrawals electra).data.toList.filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ horizon)).map (·.amount.toNat)).sum +
        ((calls.filter fun called => called.index.isNone &&
          decide (called.call.epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            horizon)).map (·.call.amount.toNat)).sum := by
  obtain ⟨calls, _, _, trace, queue, _, _, _, _, firsts, rates⟩ :=
    run_exit_rates (callRate := callRate) (consEnvelope := fun _ => 2 ^ 64)
      (consRate := by
        intro fork s early total rate read computed atEpoch bound
        exact (UInt64.toNat_lt rate).le)
      (consMono := monotone_const)
      electra tail early
      (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)) ceilings
  have partials := run_partial_queue_due (partialDebit_eq := partialDebit_eq)
    (slot_zero := slot_zero) tail electra early replayed horizon endpoint
    (calls.filterMap (·.entry)) queue
  rw [partials_entries_due_sum] at partials
  exact ⟨calls, trace, firsts, rates, partials⟩

/-- A branch's partial cost plus the kept due entries it leaves is at most those it had and added.

An entry is kept when `keep` selects it.

Every entry counted is due by the cutoff. -/
theorem run_partial_queue_net {cost : BalanceEvent preset → Nat}
    {keep : PendingPartialWithdrawal → Bool}
    (charged : PartialCost (config := config) (checks := checks) cost keep) (high cutoff : Nat)
    (electra : .pectra ≤ x.fork) {y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ cutoff) :
    -- The kept entries are those of the queue at the start, and those appended along the branch.
    ∃ added : List PendingPartialWithdrawal,
      -- Each appended entry is due no earlier than the withdrawal delay after the start.
      (∀ entry ∈ added, (getCurrentEpoch x.state).toNat +
        config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤ entry.withdrawableEpoch.toNat) ∧
      (events.map cost).sum +
        ((((y.state.pendingPartialWithdrawals
          (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps))).data.toList.filter
            keep).filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
              (·.amount.toNat)).sum ≤
        ((((x.state.pendingPartialWithdrawals electra).data.toList.filter keep).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum +
        (((added.filter keep).filter (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map
          (·.amount.toNat)).sum := by
  obtain ⟨calls, _, _, _, queue, _, _, _, _, firsts, _⟩ :=
    run_exit_rates (ceilingValue := fun _ => 2 ^ 64) (exitEnvelope := fun _ => 2 ^ 64)
      (callRate := by intros; exact (UInt64.toNat_lt _).le)
      (consEnvelope := fun _ => 2 ^ 64)
      (consRate := by intros; exact (UInt64.toNat_lt _).le)
      (consMono := monotone_const)
      electra tail early (Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps))
      (fun _ _ total _ => (UInt64.toNat_lt total).le)
  refine ⟨calls.filterMap (·.entry), ?_,
    run_partial_queue_due_of charged tail electra early replayed cutoff endpoint _ queue⟩
  intro entry member
  obtain ⟨called, present, found⟩ := List.mem_filterMap.mp member
  have pushed := (called.pushed entry found).2
  have spent := called.call.epoch_ge.2
  have first := firsts called present
  omega

end
end EthLib.Consensus.DirectSafety
