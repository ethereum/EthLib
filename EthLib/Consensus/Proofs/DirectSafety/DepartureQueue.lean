module

public import EthLib.Consensus.Proofs.DirectSafety.ChurnBounds
public import EthLib.Consensus.Proofs.DirectSafety.Execution
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Transition.RegistryIdentity
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Departure queue accounting

A queue call records its assigned epoch as well as the balance that it spends.

Partial withdrawals spend exit capacity without assigning a validator's exit.

The departure charges of a run fit the queue capacity of a window of epochs.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

/-- One successful balance-queue call, including the queue before and after it. -/
private structure DepartureQueueCall where
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

/-- A call cannot move the open queue epoch backwards. -/
private theorem DepartureQueueCall.epoch_mono (call : DepartureQueueCall) :
    call.earliest.toNat ≤ call.epoch.toNat := by
  have placed := UInt64.le_iff_toNat_le.mp (churnQueue_spend call.computed).1
  rw [Base.Uint64.toNat_max] at placed
  omega

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
private inductive DepartureQueueTrace : Epoch → Gwei → List DepartureQueueCall → Epoch → Gwei → Prop
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

/-- Once assigned, an exit cannot generate a second charge later in the run. -/
private theorem departureCharges_run_indices {x y : ForkedBeaconState preset}
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

/-- Calls carry the charged registry index, or no index for partial withdrawals. -/
private structure IndexedDepartureCall where
  index : Option Nat
  call : DepartureQueueCall

/-- Every call starts no earlier than the chosen epoch. -/
private def DepartureCallsFrom (start : Nat) (calls : List IndexedDepartureCall) : Prop :=
  ∀ called ∈ calls, start ≤ called.call.first.toNat

private theorem DepartureCallsFrom.mono {start later : Nat} {calls : List IndexedDepartureCall}
    (firsts : DepartureCallsFrom later calls) (ordered : start ≤ later) :
    DepartureCallsFrom start calls := fun called member => ordered.trans (firsts called member)

private theorem DepartureCallsFrom.append {start : Nat} {first second : List IndexedDepartureCall}
    (one : DepartureCallsFrom start first) (two : DepartureCallsFrom start second) :
    DepartureCallsFrom start (first ++ second) := by
  intro called member
  exact (List.mem_append.mp member).elim (one called) (two called)

private def ConsolidationCallSites (preset : Preset) (config : Config)
    (calls : List IndexedDepartureCall) (sites : List (ForkedBeaconState preset)) : Prop :=
  ∀ called ∈ calls, ∃ site ∈ sites,
    computeActivationExitEpoch preset (getCurrentEpoch site.state) = .ok called.call.first ∧
      getConsolidationChurnLimit config site.state = .ok called.call.rate

/-- Index uniqueness turns matching tagged calls into an injection of charges into calls. -/
private theorem departureCharges_inject {charges : List DepartureCharge}
    {calls : List IndexedDepartureCall} (unique : (charges.map (·.index)).Nodup)
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
    {calls : List IndexedDepartureCall} (unique : (charges.map (·.index)).Nodup)
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

/-- A first-epoch bound discards capacity in idle epochs before the chosen window. -/
private theorem DepartureQueueTrace.window_le_from {earliest epoch : Epoch} {available left : Gwei}
    {calls : List DepartureQueueCall}
    (trace : DepartureQueueTrace earliest available calls epoch left) (start high cap : Nat)
    (rates : ∀ call ∈ calls, call.rate.toNat ≤ cap)
    (firsts : ∀ call ∈ calls, start ≤ call.first.toNat) :
    ((calls.filter fun call => call.epoch.toNat ≤ high).map fun call => call.amount.toNat).sum ≤
      (if earliest.toNat ≤ high then available.toNat else 0) + (high + 1 - start) * cap := by
  cases trace with
  | nil => simp
  | cons call tail =>
    have rest := tail.window_le high cap
      (fun c member => rates c (List.mem_cons_of_mem _ member))
    by_cases inside : call.epoch.toNat ≤ high
    · by_cases before : start ≤ call.earliest.toNat
      · have initialInside := call.epoch_mono.trans inside
        have bound := (DepartureQueueTrace.cons call tail).window_le high cap rates
        have initial : departureQueuePotential high cap call.earliest call.available ≤
            (if call.earliest.toNat ≤ high then call.available.toNat else 0) +
              (high + 1 - start) * cap := by
          simp only [departureQueuePotential, initialInside, ↓reduceIte]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right cap (by omega)) _
        exact (Nat.le_add_right _ _).trans (bound.trans initial)
      · have first := firsts call (by simp)
        obtain ⟨placed, spent, _⟩ := churnQueue_spend call.computed
        have placed := UInt64.le_iff_toNat_le.mp placed
        rw [Uint64.toNat_max] at placed
        have reset : call.earliest < max call.earliest call.first := by
          rw [UInt64.lt_iff_toNat_lt, Uint64.toNat_max]
          omega
        rw [ite_eq_left reset, Uint64.toNat_max] at spent
        have one : call.left.toNat + call.amount.toNat ≤
            (call.epoch.toNat + 1 - start) * cap := by
          calc
            call.left.toNat + call.amount.toNat =
                (call.epoch.toNat - max call.earliest.toNat call.first.toNat + 1) *
                  call.rate.toNat := by rw [spent, Nat.add_mul, Nat.one_mul]; omega
            _ ≤ (call.epoch.toNat + 1 - start) * cap :=
              Nat.mul_le_mul (by omega) (rates call (by simp))
        have distance : (call.epoch.toNat + 1 - start) + (high - call.epoch.toNat) =
            high + 1 - start := by omega
        have combined := Nat.add_le_add_right one ((high - call.epoch.toNat) * cap)
        rw [← Nat.add_mul, distance] at combined
        simp only [departureQueuePotential, inside, ↓reduceIte] at rest
        simp only [List.filter_cons, decide_eq_true inside, ↓reduceIte,
          List.map_cons, List.sum_cons]
        omega
    · simp only [departureQueuePotential, inside, ↓reduceIte] at rest
      simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
      omega

/-- Tagged calls cover all newly assigned exits of existing registry entries. -/
private def DepartureCoverage {f h : Fork} (s : BeaconState preset f) (t : BeaconState preset h)
    (calls : List IndexedDepartureCall) : Prop :=
  ∀ i old next, s.validators.data[i]? = some old → t.validators.data[i]? = some next →
    old.exitEpoch = FAR_FUTURE_EPOCH → next.exitEpoch ≠ FAR_FUTURE_EPOCH →
    ∃ called ∈ calls, called.index = some i ∧ called.call.epoch = next.exitEpoch ∧
      called.call.amount = old.effectiveBalance

/-- Accessor-level matching covers every existing index in a pre-Gloas registry. -/
private theorem DepartureCoverage.of_accessor {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {calls : List IndexedDepartureCall} (early : f < .glamsterdam)
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
    {t : BeaconState preset h} {u : BeaconState preset k} {first second : List IndexedDepartureCall}
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
    {t : BeaconState preset h} {u : BeaconState preset k} {first second : List IndexedDepartureCall}
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
    DepartureCoverage s t [] := by
  intro i old next before after unset assigned
  exact False.elim (assigned ((epochs i old next before after).trans unset))

/-- An unchanged registry needs no departure call. -/
private theorem DepartureCoverage.of_data {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data) :
    DepartureCoverage s t [] := by
  apply DepartureCoverage.of_exit_epochs
  intro i old next before after
  rw [same, before] at after
  cases Option.some.inj after
  rfl

/-- Appending validators preserves the exit epochs of all existing entries. -/
private theorem DepartureCoverage.of_append {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {added : Array Validator}
    (same : t.validators.data = s.validators.data ++ added) : DepartureCoverage s t [] := by
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
    DepartureCoverage s t [] := by
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
    {t : BeaconState preset h} {u : BeaconState preset k} {calls : List IndexedDepartureCall}
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
    {t : BeaconState preset h} {u : BeaconState preset k} {calls : List IndexedDepartureCall}
    (covered : DepartureCoverage s t calls) (empty : DepartureCoverage t u [])
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
    (empty : ∀ a item b, operation a item = .ok b → DepartureCoverage a b [])
    (life : ∀ a item b, operation a item = .ok b → RegistryLifecycle a b)
    {s t : BeaconState preset f} {items : List α}
    (ok : items.foldlM operation s = .ok t) : DepartureCoverage s t [] := by
  have result := foldlM_ok_invariant
    (fun t => DepartureCoverage s t [] ∧ RegistryLifecycle s t)
    (fun a item b before stepped =>
      ⟨before.1.suffix_of_empty (empty a item b stepped) before.2 (life a item b stepped),
        before.2.trans (life a item b stepped)⟩)
    ⟨DepartureCoverage.of_data rfl, .refl s⟩ ok
  exact result.1

/-- A fold composes concrete calls when each operation preserves pre-scheduling balances. -/
private theorem DepartureCoverage.foldlM {f : Fork} {α ε : Type}
    {operation : BeaconState preset f → α → Except ε (BeaconState preset f)}
    (electra : .pectra ≤ f) (cap : Nat)
    (localTrace : ∀ s item t, operation s item = .ok t →
      ∃ calls : List IndexedDepartureCall,
        DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
        DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
          (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
        DepartureCoverage s t calls ∧ (∀ called ∈ calls, called.call.rate.toNat ≤ cap))
    (lifecycle : ∀ s item t, operation s item = .ok t → RegistryLifecycle s t)
    (effective : ∀ s item t, operation s item = .ok t →
      ∀ i, i < s.validators.data.size → effectiveAt ⟨f, t⟩ i = effectiveAt ⟨f, s⟩ i)
    (slots : ∀ s item t, operation s item = .ok t → t.slot = s.slot)
    {items : List α} {s t : BeaconState preset f}
    (ok : items.foldlM operation s = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls, called.call.rate.toNat ≤ cap) := by
  induction items generalizing s with
  | nil =>
    cases ok
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, DepartureCoverage.of_data rfl, by simp⟩
  | cons item items ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, stepped, rest⟩ := ok
    obtain ⟨first, firstFrom, firstTrace, firstCoverage, firstRates⟩ :=
      localTrace s item middle stepped
    obtain ⟨later, laterFrom, laterTrace, laterCoverage, laterRates⟩ := ih rest
    have epoch : getCurrentEpoch middle = getCurrentEpoch s := by
      simp only [getCurrentEpoch, slots _ _ _ stepped]
    rw [epoch] at laterFrom
    refine ⟨first ++ later, firstFrom.append laterFrom, ?_, ?_, ?_⟩
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
    (step : Step config checks x y) {calls : List IndexedDepartureCall}
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

/-- Partial withdrawals may spend exit capacity while leaving every validator unchanged. -/
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
        computeActivationExitEpoch preset (getCurrentEpoch s) = .ok call.first) := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨balance, _, kept, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨⟨queued, epoch⟩, called, _, _, _, _, rfl⟩ := ok
    obtain ⟨call, earliest, available, _, placed, left, rate, firstOk⟩ :=
      exitQueueCall_of_computed electra called
    obtain ⟨queuedEpoch, registry, _⟩ := computeExitEpochAndUpdateChurn_earliest called
    exact ⟨registry, .inr ⟨call, earliest, available, placed.trans queuedEpoch.symm,
      left, rate, firstOk⟩⟩
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
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨⟨queued, epoch⟩, called, withdrawable, _, changed, set, pending, _, rfl⟩ := ok
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
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨⟨queued, epoch⟩, called, withdrawable, _, changed, set, pending, _, rfl⟩ := ok
  change getValidator changed other = getValidator s other
  rw [getValidator_setValidator_of_ne set different]
  exact getValidator_of_validators_eq
    (computeConsolidationEpochAndUpdateChurn_earliest called).2.1 _

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
    ∃ called : IndexedDepartureCall,
      (getCurrentEpoch s).toNat ≤ called.call.first.toNat ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) [called.call]
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      getConsolidationChurnLimit config s = .ok called.call.rate ∧
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok called.call.first ∧
      ∀ other old next, getValidator s other = .ok old → getValidator t other = .ok next →
        old.exitEpoch = FAR_FUTURE_EPOCH → next.exitEpoch ≠ FAR_FUTURE_EPOCH →
        called.index = some other.toNat ∧ called.call.epoch = next.exitEpoch ∧
          called.call.amount = old.effectiveBalance := by
  obtain ⟨call, amount, earliest, available, placed, left, rate, firstOk, later, read, epoch⟩ :=
    queueConsolidation_call electra ok
  refine ⟨⟨some sourceIndex.toNat, call⟩, ?_, ?_, rate, firstOk, ?_⟩
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

/-- The two departure queues, excluding pending transfers and withdrawals. -/
private def departureQueues {fork : Fork} (electra : .pectra ≤ fork)
    (s : BeaconState preset fork) : Epoch × Gwei × Epoch × Gwei :=
  (s.earliestExitEpoch electra, s.exitBalanceToConsume electra,
    s.earliestConsolidationEpoch electra, s.consolidationBalanceToConsume electra)

private theorem departureQueues_increase {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {amount : Gwei}
    (ok : increaseBalance s index amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem departureQueues_decrease {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex} {amount : Gwei}
    (ok : decreaseBalance s index amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem allDeltas_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deltas : Array Gwei × Array Gwei}
    (ok : applyAllDeltas s deltas = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro a index b kept stepped
  simp only [applyDeltas, liftAccessor_ok, bind_ok_iff] at stepped
  obtain ⟨_, _, raised, increase, decrease⟩ := stepped
  exact (departureQueues_decrease electra decrease).trans
    ((departureQueues_increase electra increase).trans kept)

/-- Epoch rewards and penalties preserve departure capacity and queue epochs. -/
private theorem rewards_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processRewardsAndPenalties config s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  unfold processRewardsAndPenalties at ok
  split at ok
  · cases ok; rfl
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, folded⟩ := ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl folded
  intro a deltas b kept stepped
  exact (allDeltas_departureQueues electra stepped).trans kept

/-- Epoch slashing penalties debit balances without spending departure capacity. -/
private theorem slashingPenalties_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processSlashings s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [processSlashings, electra, ↓reduceIte, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, folded⟩ := ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl folded
  intro a index b kept stepped
  unfold applySlashingPenaltyElectra at stepped
  simp only [bind_ok_iff] at stepped
  obtain ⟨_, _, stepped⟩ := stepped
  split at stepped
  · simp only [bind_ok_iff] at stepped
    obtain ⟨_, _, stepped⟩ := stepped
    split at stepped
    · simp only [bind_ok_iff] at stepped
      obtain ⟨_, _, _, _, decreased⟩ := stepped
      exact (departureQueues_decrease electra (liftAccessor_ok.mp decreased)).trans kept
    · cases stepped; exact kept
  · cases stepped; exact kept

private theorem addValidator_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  simp only [addValidatorToRegistry, altair, ↓reduceDIte,
    addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
  rfl

private theorem applyDeposit_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {key : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (ok : applyDeposit config checks s key credentials amount signature = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [applyDeposit, electra, ↓reduceDIte] at ok
  unfold applyDepositElectra at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨middle, added, queued⟩ := ok
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
      exact (addValidator_departureQueues electra added :)
    · cases ok; rfl
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
    rfl

/-- Block deposits preserve departure capacity even when they append a validator. -/
private theorem deposit_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, _, _, _, credited⟩ := processDeposit_ok ok
  exact (applyDeposit_departureQueues electra credited :)

/-- Deposits append validators or change balances, without assigning existing validators exits. -/
private theorem deposit_coverage {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : DepartureCoverage s t [] := by
  obtain ⟨_, _, _, _, credited⟩ := processDeposit_ok ok
  have applyCoverage {a b : BeaconState preset fork} {key credentials amount signature}
      (applied : applyDeposit config checks a key credentials amount signature = .ok b) :
      DepartureCoverage a b [] := by
    simp only [applyDeposit, electra, ↓reduceDIte] at applied
    unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨added, admitted, queued⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        apply DepartureCoverage.of_append
        simpa only [Array.push_eq_append] using addValidatorToRegistry_validators_eq_push admitted
      · cases applied; exact DepartureCoverage.of_data rfl
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact DepartureCoverage.of_data rfl
  exact (applyCoverage credited :)

/-- Execution deposit requests append pending deposits without changing departure capacity. -/
private theorem depositRequest_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
  unfold recordDepositRequestsStart
  split <;> (try split) <;> rfl

/-- Attestation processing preserves departure queues before Gloas. -/
private theorem attestation_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processAttestation, altair, ↓reduceDIte] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok, notGloas, ↓reduceDIte,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, raised, rfl⟩ := ok
  rw [departureQueues_increase electra raised]
  unfold setEpochParticipation
  split <;> rfl

/-- A sync aggregate changes balances without consuming departure churn. -/
private theorem sync_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl folded
  intro a reward b kept stepped
  unfold applySyncReward at stepped
  split at stepped
  · simp only [bind_ok_iff, liftAccessor_ok] at stepped
    obtain ⟨_, raised, _, _, paid⟩ := stepped
    exact (departureQueues_increase electra paid).trans
      ((departureQueues_increase electra raised).trans kept)
  · exact (departureQueues_decrease electra (liftAccessor_ok.mp stepped)).trans kept

/-- Changing withdrawal credentials leaves both departure queues unchanged. -/
private theorem credentials_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- A withdrawal-credential change assigns no exit epoch. -/
private theorem credentials_coverage {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    DepartureCoverage s t [] := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  exact DepartureCoverage.setValidatorAt found set rfl

private theorem pendingDeposit_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; rfl
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact addValidator_departureQueues electra ok
    · cases ok; rfl
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact departureQueues_increase electra ok

private theorem passPendingDeposits_departureQueues {fork : Fork}
    (electra : .pectra ≤ fork) {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {s : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available s processed count postponed
        deposits = .ok pass → departureQueues electra pass.1.state = departureQueues electra s
  | [], _, _, _, _, _, ok => by cases ok; rfl
  | deposit :: rest, s, processed, count, postponed, pass, ok => by
    unfold passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; rfl
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (passPendingDeposits_departureQueues electra (deposits := rest) ‹_›).trans
        (pendingDeposit_departureQueues electra credited)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact passPendingDeposits_departureQueues electra (deposits := rest) ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; rfl
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact (passPendingDeposits_departureQueues electra (deposits := rest) ‹_›).trans
      (pendingDeposit_departureQueues electra credited)

/-- Crediting pending deposits preserves both departure queues. -/
private theorem pendingDeposits_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact passPendingDeposits_departureQueues electra ‹_›

private theorem applyWithdrawals_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {withdrawals : Array Withdrawal}
    (ok : applyWithdrawals s withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold applyWithdrawals at ok
  rw [← Array.foldlM_toList] at ok
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro a withdrawal b kept stepped
  simp only [applyWithdrawal, notGloas, false_and, ↓reduceDIte] at stepped
  exact (departureQueues_decrease electra stepped).trans kept

private theorem withdrawalIndex_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {withdrawals : Array Withdrawal}
    (ok : updateNextWithdrawalIndex s withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  unfold updateNextWithdrawalIndex at ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    rfl
  · cases ok; rfl

private theorem withdrawalValidatorIndex_departureQueues {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork)
    {capella : .shapella ≤ fork} {withdrawals : Array Withdrawal}
    (ok : updateNextWithdrawalValidatorIndex s capella withdrawals = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · cases ok
  · cases ok; rfl

/-- Paying withdrawals removes balances and pending entries without resetting churn. -/
private theorem withdrawals_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, _, _, _, applied⟩ := ok
  simp only [applyExpectedWithdrawals, notGloas, electra, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at applied
  obtain ⟨withdrawn, paid, indexed, moved, swept⟩ := applied
  have last := withdrawalValidatorIndex_departureQueues electra swept
  exact last.trans ((withdrawalIndex_departureQueues electra moved).trans
    (applyWithdrawals_departureQueues electra early paid))

/-- A slashing changes the departure queues only in its initial exit scheduling call. -/
private theorem slashValidator_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    ∃ exited, initiateValidatorExit config s index = .ok exited ∧
      departureQueues electra t = departureQueues electra exited := by
  obtain ⟨exited, _, _, _, _, _, _, _, _, _, _, _, exitedOk, _, _, markedOk, _, _, _,
    lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at done
  subst done
  refine ⟨exited, exitedOk, ?_⟩
  rw [departureQueues_increase electra final, departureQueues_increase electra raised,
    departureQueues_decrease electra lowered]
  obtain ⟨_, rfl⟩ := setValidator_ok markedOk
  rfl

private theorem passPendingConsolidations_departureQueues {fork : Fork}
    (electra : .pectra ≤ fork) {epoch : Epoch} :
    ∀ {items : List PendingConsolidation} {s : BeaconState preset fork} {result},
      passPendingConsolidations epoch s items = .ok result →
      departureQueues electra result.1 = departureQueues electra s
  | [], _, _, ok => by cases ok; rfl
  | item :: rest, s, result, ok => by
    unfold passPendingConsolidations at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i recur
      cases ok
      exact (passPendingConsolidations_departureQueues electra recur :)
    split at ok
    · cases ok; rfl
    split at ok
    · cases ok
    split at ok
    · cases ok
    rename_i lowered loweredOk
    split at ok
    · cases ok
    rename_i raised raisedOk
    split at ok
    · cases ok
    rename_i recur
    cases ok
    exact (passPendingConsolidations_departureQueues electra recur).trans
      ((departureQueues_increase electra (liftAccessor_ok.mp raisedOk)).trans
        (departureQueues_decrease electra (liftAccessor_ok.mp loweredOk)))

private theorem queueExcess_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rfl
  · cases ok; rfl

/-- Switching credentials cannot reset departure capacity. -/
private theorem switchToCompounding_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, _, set, queued⟩ := ok
  rw [queueExcess_departureQueues electra queued]
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- Effective-balance changes happen after scheduling and leave its queue fields unchanged. -/
private theorem effectiveBalances_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (ok : processEffectiveBalanceUpdates s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  refine foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra s)
    ?_ rfl ok
  intro before index after kept updated
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at updated
  obtain ⟨_, _, _, _, _, _, set⟩ := updated
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact kept

/-- The effective-balance pass assigns no exits and therefore preserves earlier charge amounts. -/
private theorem effectiveBalances_coverage {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEffectiveBalanceUpdates s = .ok t) : DepartureCoverage s t [] := by
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
    (ok : applyPendingDeposit config checks s deposit = .ok t) : DepartureCoverage s t [] := by
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact DepartureCoverage.of_data rfl
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · apply DepartureCoverage.of_append
      simpa only [Array.push_eq_append] using addValidatorToRegistry_validators_eq_push ok
    · cases ok; exact DepartureCoverage.of_data rfl
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact DepartureCoverage.of_data (congrArg (·.data) (increaseBalance_validators ok))

/-- Pending deposits assign no exits, independently of pending-source provenance. -/
private theorem pendingDeposits_coverage {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks s electra = .ok t) : DepartureCoverage s t [] := by
  have pass {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei} :
      ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
        {count : Nat} {postponed : Array PendingDeposit} {result},
        passPendingDeposits config checks stop nextEpoch available state processed count
          postponed deposits = .ok result → DepartureCoverage state result.1.state [] := by
    intro deposits
    induction deposits with
    | nil => intro state processed count postponed result ok; cases ok; exact .of_data rfl
    | cons deposit rest ih =>
      intro state processed count postponed result ok
      unfold passPendingDeposits at ok
      simp only [bind, Except.bind, pure, Except.pure] at ok
      split at ok
      · cases ok; exact .of_data rfl
      split at ok
      · cases ok
      split at ok
      · split at ok
        · cases ok
        rename_i credited
        split at ok
        · cases ok
        cases ok
        exact (pendingDeposit_coverage credited).suffix_of_empty (ih ‹_›)
          (registryLifecycle_applyPendingDeposit credited)
          (registryLifecycle_passPendingDeposits (deposits := rest) ‹_›)
      split at ok
      · split at ok
        · cases ok
        cases ok
        exact ih ‹_›
      split at ok
      · cases ok
      split at ok
      · cases ok; exact .of_data rfl
      split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (pendingDeposit_coverage credited).suffix_of_empty (ih ‹_›)
        (registryLifecycle_applyPendingDeposit credited)
        (registryLifecycle_passPendingDeposits (deposits := rest) ‹_›)
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

/-- Electra initializes its queues once; subsequent upgrade folds preserve all four fields. -/
private theorem electra_departure_initialization {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    ∃ first exitEpoch exitRate consolidationRate,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      Uint64.addChecked (s.validators.data.foldl (init := first) fun latest validator =>
        if validator.exitEpoch = FAR_FUTURE_EPOCH then latest else max latest validator.exitEpoch)
        1 = .ok exitEpoch ∧
      departureQueues (by decide) t = (exitEpoch, exitRate, first, consolidationRate) := by
  simp only [upgradeToElectra, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at ok
  obtain ⟨first, firstOk, exitEpoch, exitOk, exitRate, _, consolidationRate, _, middle,
    queued, compounded⟩ := ok
  have one := foldlM_ok_invariant
    (fun u => departureQueues (by decide) u = (exitEpoch, exitRate, first, consolidationRate))
    (fun a i b kept step => (preActivation_departureQueues (by decide) step).trans kept)
    rfl queued
  have two := foldlM_ok_invariant
    (fun u => departureQueues (by decide) u = (exitEpoch, exitRate, first, consolidationRate))
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

private theorem justification_departureQueues {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (ok : processJustificationAndFinalization s = .ok t) :
    departureQueues electra t = departureQueues electra s := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]
    rfl

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

/-- Every epoch stage keeps the slot. -/
private theorem epochStage_slot {fork : Fork} {stage : EpochStage} {s t : BeaconState preset fork}
    (edge : EpochStage.Edge config checks stage s t) : t.slot = s.slot := by
  cases stage <;> simp only [EpochStage.Edge] at edge
  case justification => exact (activeStep_processJustificationAndFinalization edge).1
  case rewards => exact (frame_processRewardsAndPenalties edge).slot
  case registry => exact (frame_processRegistryUpdates edge).slot
  case slashings => exact (frame_processSlashings edge).slot
  case effectiveBalances => exact (frame_processEffectiveBalanceUpdates edge).slot
  case slashingsReset => exact (frame_processSlashingsReset edge).slot
  case randaoReset => exact (frame_processRandaoMixesReset edge).slot
  case history =>
    split at edge
    · exact (frame_processHistoricalSummariesUpdate edge).slot
    · exact (frame_processHistoricalRootsUpdate edge).slot
  case participation =>
    split at edge
    · subst edge
      rfl
    · exact (frame_processParticipationRecordUpdates edge).slot
  all_goals split at edge
  case inactivity.isTrue => exact (frame_processInactivityUpdates edge).slot
  case eth1Reset.isTrue => exact (frame_processEth1DataReset edge).slot
  case pendingDeposits.isTrue => exact (frame_processPendingDeposits edge).slot
  case pendingConsolidations.isTrue => exact (frame_processPendingConsolidations edge).slot
  case payments.isTrue => rw [processBuilderPendingPayments_eq edge]
  case syncCommittees.isTrue => exact (frame_processSyncCommitteeUpdates edge).slot
  case proposerLookahead.isTrue => exact (frame_processProposerLookahead edge).slot
  case ptcWindow.isTrue =>
    simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
    obtain ⟨_, _, _, _, rfl⟩ := edge
    rfl
  all_goals exact edge ▸ rfl

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
    (other : stage ≠ .registry) : DepartureCoverage s t [] ∧ RegistryLifecycle s t := by
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

/-- Withdrawal requests either do nothing, initiate an exit, or spend partial-withdrawal churn. -/
private theorem withdrawalRequest_cases {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    t = s ∨ (∃ index, initiateValidatorExit config s index = .ok t) ∨
      ∃ index v owed,
        requestPartialWithdrawal config s electra index v request.amount owed = .ok t := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl rfl)
    | (cases ok)
    | exact .inr (.inl ⟨_, liftAccessor_ok.mp ok⟩)
    | exact .inr (.inr ⟨_, _, _, ok⟩)

/-- An exit trace tags its call and covers every newly assigned validator exit. -/
private theorem initiateExit_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) ∧
      ∀ other old next, getValidator s other = .ok old → getValidator t other = .ok next →
        old.exitEpoch = FAR_FUTURE_EPOCH → next.exitEpoch ≠ FAR_FUTURE_EPOCH →
        ∃ called ∈ calls, called.index = some other.toNat ∧
          called.call.epoch = next.exitEpoch ∧ called.call.amount = old.effectiveBalance := by
  obtain same | ⟨v, call, found, _, amount, earliest, available, placed, left, rate,
    firstOk, later, read, epoch⟩ := initiateExit_call electra ok
  · subst t
    refine ⟨[], by simp [DepartureCallsFrom], .nil _ _, by simp, ?_⟩
    intro other old next before after unset assigned
    have equal := Except.ok.inj (before.symm.trans after)
    exact False.elim (assigned (equal ▸ unset))
  · refine ⟨[⟨some index.toNat, call⟩], ?_, ?_, ?_, ?_⟩
    · intro called member
      obtain rfl := List.mem_singleton.mp member
      have first := (computeActivationExitEpoch_ok_iff.mp firstOk).2
      dsimp only
      omega
    · change DepartureQueueTrace _ _ [call] _ _
      rw [← earliest, ← available, ← placed, ← left]
      exact .cons call (.nil _ _)
    · intro called member
      obtain rfl := List.mem_singleton.mp member
      exact exitChurnLimit_le_cap early rate
    · intro other old next before after unset assigned
      have sameIndex := (initiateExit_charge electra ok before after unset assigned).1
      subst other
      have oldSame := Except.ok.inj (found.symm.trans before)
      have nextSame := Except.ok.inj (read.symm.trans after)
      subst old next
      exact ⟨_, List.mem_singleton_self _, rfl, epoch.symm, amount⟩

/-- Registry ejections supply tagged calls; activation-only updates generate no charge. -/
private theorem registryEntry_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {activation : Epoch} {index : Nat}
    (ok : updateRegistryEntryElectra config activation s index = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨epoch, _, set⟩ := ok
    have covered := DepartureCoverage.setValidatorAt found set rfl
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, covered, by simp⟩
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validatorIndex, _, exited⟩ := ok
    obtain ⟨calls, firsts, trace, rates, covered⟩ := initiateExit_indexedTrace electra early exited
    exact ⟨calls, firsts, trace, DepartureCoverage.of_accessor early covered, rates⟩
  split at ok
  · have set := liftAccessor_ok.mp ok
    have covered := DepartureCoverage.setValidatorAt found set rfl
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, covered, by simp⟩
  · cases ok
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, DepartureCoverage.of_data rfl, by simp⟩

/-- The Electra registry fold matches ejection charges before effective balances change. -/
private theorem registryEntries_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {activation : Epoch}
    {indices : List Nat}
    (ok : indices.foldlM (updateRegistryEntryElectra config activation) s = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  apply DepartureCoverage.foldlM electra _
    (fun _ _ _ stepped => registryEntry_indexedTrace electra early stepped) ?_ ?_
    (fun _ _ _ stepped => (frame_updateRegistryEntryElectra stepped).slot) ok
  · intro a index b stepped
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at stepped
    obtain ⟨validator, found, stepped⟩ := stepped
    split at stepped
    · simp only [bind_ok_iff, liftAccessor_ok] at stepped
      obtain ⟨_, _, set⟩ := stepped
      exact .setValidatorAt found set ⟨fun _ => rfl, fun _ => rfl⟩
    split at stepped
    · simp only [bind_ok_iff, liftAccessor_ok] at stepped
      obtain ⟨_, _, exited⟩ := stepped
      exact registryLifecycle_initiateValidatorExit exited
    split at stepped
    · rename_i eligible
      have far := activationEpoch_of_isEligibleForActivation eligible
      exact .setValidatorAt found (liftAccessor_ok.mp stepped)
        ⟨fun set => absurd far set, fun _ => rfl⟩
    · cases stepped; exact .refl _
  · intro a index b stepped
    exact effectiveKept_registryElectra stepped

/-- A partial withdrawal's capacity call has no departure index. -/
private theorem partialWithdrawal_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    t.validators = s.validators ∧ ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      ∀ called ∈ calls, called.index = none ∧
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
  obtain ⟨registry, same | ⟨call, earliest, available, placed, left, rate, firstOk⟩⟩ :=
    partialWithdrawal_call electra ok
  · subst t
    exact ⟨rfl, [], by simp [DepartureCallsFrom], .nil _ _, by simp⟩
  · refine ⟨registry, [⟨none, call⟩], ?_, ?_, ?_⟩
    · intro called member
      obtain rfl := List.mem_singleton.mp member
      have first := (computeActivationExitEpoch_ok_iff.mp firstOk).2
      dsimp only
      omega
    · change DepartureQueueTrace _ _ [call] _ _
      rw [← earliest, ← available, ← placed, ← left]
      exact .cons call (.nil _ _)
    · intro called member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl, exitChurnLimit_le_cap early rate⟩

/-- Slashing preserves the exit call's index, amount and assigned epoch. -/
private theorem slashing_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  obtain ⟨exited, validator, withdrawable, marked, _, _, _, _, _, _, _, last, exitedOk,
    found, _, markedOk, _, _, _, lowered, _, _, raised, final, done⟩ := slashValidator_ok ok
  obtain ⟨calls, firsts, trace, rates, covered⟩ := initiateExit_indexedTrace electra early exitedOk
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
  refine ⟨calls, firsts, ?_, DepartureCoverage.of_accessor early ?_, rates⟩
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

/-- Consecutive queue traces compose without adding capacity at their shared state. -/
private theorem DepartureQueueTrace.append {a b c : Epoch} {x y z : Gwei}
    {first second : List DepartureQueueCall}
    (one : DepartureQueueTrace a x first b y) (two : DepartureQueueTrace b y second c z) :
    DepartureQueueTrace a x (first ++ second) c z := by
  induction one with
  | nil => exact two
  | cons call tail ih => exact .cons call (ih two)

private theorem slashableFold_indexedTrace {fork : Fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {indices : List ValidatorIndex} {s t : BeaconState preset fork} {flag nextFlag : Bool}
    (ok : indices.foldlM (slashIfSlashable config) (s, flag) = .ok (t, nextFlag)) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  induction indices generalizing s flag with
  | nil =>
    cases ok
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, DepartureCoverage.of_data rfl, by simp⟩
  | cons index rest ih =>
    obtain ⟨⟨middle, flag'⟩, stepped, remaining⟩ := bind_ok_iff.mp ok
    obtain ⟨later, laterFrom, tail, laterCoverage, laterRates⟩ := ih remaining
    have slot : middle.slot = s.slot := (frame_slashIfSlashable stepped).slot
    have epoch : getCurrentEpoch middle = getCurrentEpoch s := by
      simp only [getCurrentEpoch, slot]
    rw [epoch] at laterFrom
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
      obtain ⟨first, firstFrom, head, firstCoverage, firstRates⟩ :=
        slashing_indexedTrace electra early slashed
      refine ⟨first ++ later, firstFrom.append laterFrom, ?_, ?_, ?_⟩
      · simpa only [List.map_append] using head.append tail
      · exact firstCoverage.append_of_effectiveKept laterCoverage
          (registryLifecycle_slashValidator slashed) tailLifecycle (effectiveKept_slash slashed)
      · intro called member
        exact (List.mem_append.mp member).elim (firstRates called) (laterRates called)
    · cases stepped; exact ⟨later, laterFrom, tail, laterCoverage, laterRates⟩

/-- Attester slashings retain charge coverage through their slashable-validator fold. -/
private theorem attesterSlashing_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, flag⟩, foldedOk, ok⟩ := ok
  simp only [pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact slashableFold_indexedTrace electra early foldedOk

/-- A proposer slashing retains the charged index of its exit call. -/
private theorem proposerSlashing_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashing_indexedTrace electra early slashed

/-- An Electra epoch spends departure capacity only in the registry's exit calls. -/
private theorem epoch_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : processEpoch config checks s = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  -- Cut the schedule at registry updates, the only stage that calls the exit queue.
  have trace := processEpoch_trace ok
  change EpochTrace _ ([.justification, .inactivity, .rewards] ++ .registry ::
    ([.slashings, .eth1Reset, .pendingDeposits, .pendingConsolidations] ++
      EpochStage.middleStages ++ EpochStage.tailStages)) _ _ at trace
  obtain ⟨rewarded, head, rest⟩ := EpochTrace.append_iff.mp trace
  obtain ⟨registered, registeredOk, tail⟩ : ∃ registered,
      EpochStage.action config checks .registry rewarded = .ok registered ∧
      EpochTrace (EpochStage.action config checks)
        ([.slashings, .eth1Reset, .pendingDeposits, .pendingConsolidations] ++
          EpochStage.middleStages ++ EpochStage.tailStages) registered t := by
    cases rest with
    | cons first rest => exact ⟨_, first, rest⟩
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
    exact ⟨epochStage_slot edge, edge.validators_eq ⟨other, by rintro rfl; simp at member,
      by rintro rfl; simp at member⟩, epochStage_departureQueues electra early edge other⟩
  -- The stages after it keep both queues and assign no exit.
  have tailKept : departureQueues electra t = departureQueues electra registered ∧
      DepartureCoverage registered t [] ∧ RegistryLifecycle registered t := by
    apply tail.transport (fun a b => departureQueues electra b = departureQueues electra a ∧
        DepartureCoverage a b [] ∧ RegistryLifecycle a b) (fun _ => ⟨rfl, .of_data rfl, .refl _⟩)
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
  have entriesOk : processRegistryUpdates config rewarded = .ok registered :=
    EpochStage.action_cases.mp registeredOk
  have registryLife := registryLifecycle_processRegistryUpdates entriesOk
  simp only [processRegistryUpdates, electra, ↓reduceIte, bind_ok_iff] at entriesOk
  obtain ⟨_, _, entries⟩ := entriesOk
  obtain ⟨calls, firsts, queued, covered, rates⟩ :=
    registryEntries_indexedTrace electra early entries
  have headEpoch : getCurrentEpoch rewarded = getCurrentEpoch s := by
    simp only [getCurrentEpoch, headKept.1]
  rw [headEpoch] at firsts
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
  refine ⟨calls, firsts, queued, ?_, rates⟩
  intro i old next a b
  apply covered.suffix_of_empty tailKept.2.1 registryLife tailKept.2.2 i old next _ b
  simpa only [headKept.2.1] using a

/-- Slot caching and increment preserve epoch charge coverage and its pre-update amounts. -/
private theorem slot_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (ok : advanceSlot config checks s = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, cached, cache, advanced, advance, rfl⟩ := ok
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
  unfold epochIfLast at advance
  split at advance
  · obtain ⟨calls, firsts, trace, covered, rates⟩ := epoch_indexedTrace electra early advance
    exact ⟨calls, firsts, trace, covered, rates⟩
  · cases advance
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, .of_data rfl, by simp⟩

/-- After Electra and before Gloas, upgrades carry both departure queues unchanged. -/
private theorem upgrades_departureQueues {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) (targetElectra : .pectra ≤ t.fork) :
    departureQueues targetElectra t.state =
      departureQueues electra s.state := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    have nextElectra := Nat.le_trans electra (Nat.le_of_lt next.property)
    have nextEarly := Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early
    have later := ih next nextElectra early rest targetElectra
    rw [later]
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
      simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
      obtain ⟨_, _, rfl⟩ := upgraded
      rfl
    · simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨_, _, rfl⟩ := nextOk
      exact False.elim (Nat.lt_irrefl _ nextEarly)
  | case2 s notDue => cases ok; rfl

/-- Withdrawal requests cover full departures while retaining unmatched partial calls. -/
private theorem withdrawalRequest_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam) {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) ∧
      ∀ other old next, getValidator s other = .ok old → getValidator t other = .ok next →
        old.exitEpoch = FAR_FUTURE_EPOCH → next.exitEpoch ≠ FAR_FUTURE_EPOCH →
        ∃ called ∈ calls, called.index = some other.toNat ∧
          called.call.epoch = next.exitEpoch ∧ called.call.amount = old.effectiveBalance := by
  rcases withdrawalRequest_cases ok with same | ⟨index, exited⟩ | ⟨index, v, owed, withdrawn⟩
  · subst t
    refine ⟨[], by simp [DepartureCallsFrom], .nil _ _, by simp, ?_⟩
    intro other old next before after unset assigned
    have equal := Except.ok.inj (before.symm.trans after)
    exact False.elim (assigned (equal ▸ unset))
  · exact initiateExit_indexedTrace electra early exited
  · obtain ⟨registry, calls, firsts, trace, rates⟩ :=
      partialWithdrawal_indexedTrace electra early withdrawn
    refine ⟨calls, firsts, trace, fun called member => (rates called member).2, ?_⟩
    intro other old next before after unset assigned
    have unchanged := getValidator_of_validators_eq registry other
    have equal := Except.ok.inj (before.symm.trans (unchanged ▸ after))
    exact False.elim (assigned (equal ▸ unset))

/-- The withdrawal-request fold retains charge coverage and all capacity-consuming calls. -/
private theorem withdrawalRequests_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {requests : List WithdrawalRequest}
    (ok : requests.foldlM (processWithdrawalRequest config · electra ·) s = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  apply DepartureCoverage.foldlM electra _ ?_
    (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok) ?_
    (fun _ _ _ ok => (frame_processWithdrawalRequest ok).slot) ok
  · intro a request b stepped
    obtain ⟨calls, firsts, trace, rates, coverage⟩ :=
      withdrawalRequest_indexedTrace electra early stepped
    exact ⟨calls, firsts, trace, DepartureCoverage.of_accessor early coverage, rates⟩
  · intro a request b stepped
    exact effectiveKept_withdrawalRequest stepped

/-- The validator-count churn is bounded by the registry size, not just active entries. -/
private theorem validatorChurnLimit_le_cohortCap {fork : Fork} (s : BeaconState preset fork)
    (bound : Nat) (bounded : s.validators.data.size ≤ bound) :
    (getValidatorChurnLimit config s).toNat ≤ cohortCap config bound := by
  have active : (getActiveValidatorIndices s (getCurrentEpoch s)).length ≤
      s.validators.data.size := by
    exact (List.length_filterMap_le _ _).trans (by simp)
  have converted : (getActiveValidatorIndices s (getCurrentEpoch s)).length.toUInt64.toNat ≤
      bound := (Nat.mod_le _ _).trans (active.trans bounded)
  simp only [getValidatorChurnLimit, Uint64.toNat_max, UInt64.toNat_div, cohortCap]
  exact max_le_max_left _ (Nat.div_le_div_right converted)

/-- A finite pre-Electra exit is assigned only while its count cohort has room. -/
private theorem exitQueue_count_room {fork : Fork} {s queued : BeaconState preset fork}
    (early : fork < .pectra) {amount : Gwei} {epoch : Epoch}
    (ok : exitQueue config s amount = .ok (queued, epoch))
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (bound : Nat)
    (bounded : s.validators.data.size ≤ bound) :
    queued = s ∧
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length <
        max 1 (cohortCap config bound) := by
  have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt early
  simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at ok
  obtain ⟨placed, scheduled, rfl, rfl⟩ := ok
  exact ⟨rfl, (exitQueueEpoch_churn scheduled finite).trans_le
    (max_le_max_left _ (validatorChurnLimit_le_cohortCap s bound bounded))⟩

/-- A successful voluntary exit reaches the exit scheduler with the original state. -/
private theorem voluntaryExit_initiates {fork : Fork} {s t : BeaconState preset fork}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) :
    initiateValidatorExit config s signed.message.validatorIndex = .ok t := by
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact exited

/-- Voluntary exits retain concrete charge coverage across their entire operation fold. -/
private theorem voluntaryExits_indexedTrace {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {exits : List SignedVoluntaryExit}
    (ok : exits.foldlM (processVoluntaryExit config checks) s = .ok t) :
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) := by
  apply DepartureCoverage.foldlM electra _ ?_
    (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok) ?_
    (fun _ _ _ ok => (frame_processVoluntaryExit ok).slot) ok
  · intro a signed b stepped
    obtain ⟨calls, firsts, trace, rates, covered⟩ :=
      initiateExit_indexedTrace electra early (voluntaryExit_initiates stepped)
    exact ⟨calls, firsts, trace, DepartureCoverage.of_accessor early covered, rates⟩
  · intro a signed b stepped
    exact effectiveKept_voluntaryExit stepped

/-- Successful consolidation requests record the input to their balance-queue call.

Credential switches and ignored requests do not call that queue. -/
def consolidationRequestCalls {fork : Fork} (config : Config)
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

def consolidationRequestSites {fork : Fork} (config : Config)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (request : ConsolidationRequest) :
    Except TransitionError (List (ForkedBeaconState preset)) := do
  return if ← consolidationRequestCalls config state electra request then [⟨fork, state⟩] else []

/-- A request either preserves the scheduling queues or schedules its actual source. -/
private theorem consolidationRequest_cases {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    departureQueues electra t = departureQueues electra s ∨
      ∃ sourceIndex source targetIndex,
        getValidator s sourceIndex = .ok source ∧
        queueConsolidation config s electra sourceIndex source targetIndex = .ok t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl rfl)
    | (cases ok)
    | exact .inl (switchToCompounding_departureQueues electra (liftAccessor_ok.mp ok))
    | exact .inr ⟨_, _, _, getValidator_eq_ok_iff.mpr
        (getElem?_toNat_of_ofNatChecked (by assumption)), ok⟩

/-- Consolidation requests never spend the separate exit queue. -/
private theorem consolidationRequest_exitFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) :
    t.earliestExitEpoch electra = s.earliestExitEpoch electra ∧
      t.exitBalanceToConsume electra = s.exitBalanceToConsume electra := by
  rcases consolidationRequest_cases electra ok with frame | ⟨i, v, j, _, called⟩
  · exact ⟨congrArg Prod.fst frame, congrArg (fun q => q.2.1) frame⟩
  · simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at called
    obtain ⟨⟨queued, epoch⟩, scheduled, _, _, changed, set, _, _, rfl⟩ := called
    obtain ⟨_, rfl⟩ := setValidator_ok set
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at scheduled
    obtain ⟨_, _, _, _, ⟨_, _⟩, _, rfl, _⟩ := scheduled
    exact ⟨rfl, rfl⟩

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
    DepartureCoverage s t [] := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨validator, found, changed, set, queued⟩ := ok
  have setAt := set
  rw [setValidator_eq_setValidatorAt] at setAt
  have covered := DepartureCoverage.setValidatorAt
    (by rwa [← getValidator_eq_getValidatorAt] : getValidatorAt s index.toNat = .ok validator)
    setAt rfl
  apply covered.suffix (RegistryLifecycle.setValidator found set ⟨fun _ => rfl, fun _ => rfl⟩)
  intro i old next before after
  rw [queueExcess_registry electra queued] at after
  cases Option.some.inj (before.symm.trans after)
  rfl

/-- A request classified as not calling churn preserves both departure queues. -/
private theorem consolidationRequest_notCalled {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok false) :
    departureQueues electra t = departureQueues electra s := by
  unfold processConsolidationRequest at ok
  unfold consolidationRequestCalls at classified
  simp only [bind, Except.bind, pure, Except.pure] at ok classified
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)
    | exact switchToCompounding_departureQueues electra (liftAccessor_ok.mp ok)
    | (simp_all only [↓reduceIte, Bool.false_eq_true]; cases classified)

/-- A consolidation request without a churn call assigns no exit epoch. -/
private theorem consolidationRequest_notCalled_coverage {fork : Fork}
    {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    (classified : consolidationRequestCalls config s electra request = .ok false) :
    DepartureCoverage s t [] := by
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
def consolidationRequestsSites {fork : Fork} (config : Config) (electra : .pectra ≤ fork)
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
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (calls.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      DepartureCoverage s t calls ∧ (∀ called ∈ calls, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config calls sites := by
  induction requests generalizing s sites with
  | nil =>
    cases ok
    exact ⟨[], by simp [DepartureCallsFrom], .nil _ _, DepartureCoverage.of_data rfl,
      by simp, by simp [ConsolidationCallSites]⟩
  | cons request rest ih =>
    simp only [consolidationRequestsSites, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨here, recorded, middle, stepped, ⟨last, later⟩, replayed, rfl, rfl⟩ := ok
    obtain ⟨tailCalls, tailFrom, tail, tailCoverage, tailRates, tailSites⟩ := ih replayed
      (fun site mem h rate computed => rates site (List.mem_append_right _ mem) h rate computed)
    have epoch : getCurrentEpoch middle = getCurrentEpoch s := by
      simp only [getCurrentEpoch, (frame_processConsolidationRequest stepped).slot]
    rw [epoch] at tailFrom
    have tailLifecycle : RegistryLifecycle middle last := by
      have result : rest.foldlM (processConsolidationRequest config · electra ·) middle =
          .ok last := by
        clear tailFrom tail tailCoverage tailRates tailSites rates recorded stepped ih epoch
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
      have balance := congrArg (fun q => q.2.2.2) frame
      change middle.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra
        at epoch
      change middle.consolidationBalanceToConsume electra =
        s.consolidationBalanceToConsume electra at balance
      rw [epoch, balance] at tail
      refine ⟨tailCalls, tailFrom, tail, ?_, tailRates, ?_⟩
      · exact DepartureCoverage.append_of_effectiveKept
          (consolidationRequest_notCalled_coverage electra stepped classified) tailCoverage
            (registryLifecycle_processConsolidationRequest stepped) tailLifecycle
            (effectiveKept_consolidationRequest stepped)
      · simpa using tailSites
    | true =>
      obtain ⟨sourceIndex, source, targetIndex, found, scheduled⟩ :=
        consolidationRequest_called electra stepped classified
      obtain ⟨call, first, head, rate, firstOk, covered⟩ :=
        queueConsolidation_indexedTrace_site electra found scheduled
      have coverage : DepartureCoverage s middle [call] :=
        DepartureCoverage.of_accessor early (by
          intro other old next before after unset assigned
          exact ⟨call, List.mem_singleton_self _,
            covered other old next before after unset assigned⟩)
      refine ⟨call :: tailCalls, ?_, head.append tail, ?_, ?_, ?_⟩
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
      .ok (t, sites)) (cap : Nat)
    (rates : ∀ site ∈ sites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat (exits ++ consolidations) ∧
      DepartureCoverage s t (exits ++ consolidations) ∧
      DepartureQueueTrace (deposited.earliestExitEpoch electra)
        (deposited.exitBalanceToConsume electra) (exits.map (·.call))
        (withdrawn.earliestExitEpoch electra) (withdrawn.exitBalanceToConsume electra) ∧
      DepartureQueueTrace (withdrawn.earliestConsolidationEpoch electra)
        (withdrawn.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations sites := by
  have depositsData : deposited.validators = s.validators :=
    foldlM_ok_invariant (fun t => t.validators = s.validators)
      (fun _ _ _ kept ok => (processDepositRequest_ok ok).2.1.trans kept) rfl depositedOk
  obtain ⟨exitCalls, exitFrom, exitTrace, exitCoverage, exitRates⟩ :=
    withdrawalRequests_indexedTrace electra early withdrawnOk
  obtain ⟨consolidationCalls, consolidationFrom, consolidationTrace,
    consolidationCoverage, consolidationRates, consolidationSites⟩ :=
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
  refine ⟨exitCalls, consolidationCalls, exitFrom.append consolidationFrom,
    ?_, exitTrace, consolidationTrace,
    exitRates, consolidationRates, consolidationSites⟩
  intro i old next before after
  apply coverage i old next _ after
  simpa only [depositsData] using before

/-- The pre-Gloas operation prefix covers all exits before execution requests. -/
private theorem operationsPrefix_coverage {fork : Fork} (electra : .pectra ≤ fork)
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
    ∃ calls : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat calls ∧ DepartureCoverage s changed calls ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (calls.map (·.call)) (changed.earliestExitEpoch electra)
        (changed.exitBalanceToConsume electra) ∧
      (∀ called ∈ calls,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) ∧
      RegistryLifecycle s changed ∧
      (∀ i, i < s.validators.data.size →
        effectiveAt ⟨fork, changed⟩ i = effectiveAt ⟨fork, s⟩ i) := by
  obtain ⟨one, oneFrom, oneTrace, oneCoverage, oneRates⟩ := DepartureCoverage.foldlM electra _
    (fun _ _ _ ok => proposerSlashing_indexedTrace electra early ok)
    (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok)
    (fun _ _ _ ok => effectiveKept_proposerSlashing ok)
    (fun _ _ _ ok => (frame_processProposerSlashing ok).slot) proposedOk
  obtain ⟨two, twoFrom, twoTrace, twoCoverage, twoRates⟩ := DepartureCoverage.foldlM electra _
    (fun _ _ _ ok => attesterSlashing_indexedTrace electra early ok)
    (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
    (fun _ _ _ ok => effectiveKept_attesterSlashing ok)
    (fun _ _ _ ok => (frame_processAttesterSlashing ok).slot) attestedOk
  obtain ⟨three, threeFrom, threeTrace, threeCoverage, threeRates⟩ :=
    voluntaryExits_indexedTrace electra early exitedOk
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
      (fun _ _ _ kept ok => (attestation_departureQueues electra early ok).trans kept) rfl votedOk
  have depositsFrame : departureQueues electra deposited = departureQueues electra voted :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra voted)
      (fun _ _ _ kept ok => (deposit_departureQueues electra ok).trans kept) rfl depositedOk
  have changesFrame : departureQueues electra changed = departureQueues electra exited :=
    foldlM_ok_invariant (fun t => departureQueues electra t = departureQueues electra exited)
      (fun _ _ _ kept ok => (credentials_departureQueues electra ok).trans kept) rfl changedOk
  refine ⟨(one ++ two) ++ three, (oneFrom.append twoFrom).append threeFrom,
    prefixCoverage.suffix_of_empty changesCoverage
    ((((firstLife.trans secondLife).trans votesLife).trans depositsLife).trans exitsLife)
    changesLife, ?_, ?_, ?_, ?_⟩
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
def blockConsolidationSites {fork : Fork} (config : Config) (checks : SignatureChecks)
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

/-- Successful block processing cannot lose its consolidation sites through a replay error. -/
private theorem blockConsolidationSites_result {fork : Fork}
    {engine : ExecutionEngine preset fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) :
    ∃ sites, blockConsolidationSites config checks engine s block = .ok sites := by
  by_cases electra : .pectra ≤ fork ∧ fork < .glamsterdam
  · have altair : .altair ≤ fork := Nat.le_trans (by decide) electra.1
    have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra.1
    have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
    have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt electra.2
    simp only [processBlock, processBlockAltair, altair, bellatrix, before, notGloas,
      ↓reduceDIte, pure_bind, bind_ok_iff] at ok
    obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
      operated, operatedOk, _⟩ := ok
    simp only [processOperations, notGloas, electra.1, ↓reduceDIte,
      bind_ok_iff, ensure_ok_iff] at operatedOk
    obtain ⟨expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
      votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
      requestsOk⟩ := operatedOk
    simp only [processExecutionRequests, bind_ok_iff] at requestsOk
    obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidated⟩ := requestsOk
    obtain ⟨sites, replayed⟩ := consolidationRequestsSites_result
      (by simpa only [← Array.foldlM_toList] using consolidated)
    have ensured : ensure ((block.body.deposits before).data.size = expected)
        (TransitionError.wrongDepositCount (block.body.deposits before).data.size expected) =
          .ok () := ensure_ok_iff.mpr count
    refine ⟨sites, ?_⟩
    rw [blockConsolidationSites, dite_eq_left electra]
    simp only [headedOk, executedOk,
      revealedOk, votedOk, expectedOk, ensured, proposedOk, attestedOk,
      votedAttOk, depositedOk, exitedOk, changedOk, requestedOk, withdrawnOk,
      replayed, pure, Except.pure, bind, Except.bind]
  · exact ⟨[], by simp only [blockConsolidationSites, electra, ↓reduceDIte]; rfl⟩

private theorem withdrawals_registry {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {capella : .shapella ≤ fork} {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : processWithdrawals s capella payload = .ok t) : t.validators = s.validators := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, _, _, _, applied⟩ := ok
  simp only [applyExpectedWithdrawals, notGloas, electra, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at applied
  obtain ⟨withdrawn, paid, indexed, moved, swept⟩ := applied
  have paidData : withdrawn.validators = s.validators := by
    unfold applyWithdrawals at paid
    rw [← Array.foldlM_toList] at paid
    refine foldlM_ok_invariant (fun t => t.validators = s.validators) ?_ rfl paid
    intro a withdrawal b kept stepped
    simp only [applyWithdrawal, notGloas, false_and, ↓reduceDIte] at stepped
    exact (decreaseBalance_validators stepped).trans kept
  have movedData : indexed.validators = withdrawn.validators := by
    unfold updateNextWithdrawalIndex at moved
    split at moved
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at moved
      obtain ⟨_, _, rfl⟩ := moved
      rfl
    · cases moved; rfl
  have sweptData : t.validators = indexed.validators := by
    simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at swept
    obtain ⟨_, _, swept⟩ := swept
    split at swept
    · cases swept
    · cases swept; rfl
  exact sweptData.trans (movedData.trans paidData)

private theorem sync_registry {fork : Fork} {s t : BeaconState preset fork}
    {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) :
    t.validators = s.validators := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun t => t.validators = s.validators) ?_ rfl folded
  intro a reward b kept stepped
  unfold applySyncReward at stepped
  split at stepped
  · simp only [bind_ok_iff, liftAccessor_ok] at stepped
    obtain ⟨_, raised, _, _, paid⟩ := stepped
    exact (increaseBalance_validators paid).trans ((increaseBalance_validators raised).trans kept)
  · exact (decreaseBalance_validators (liftAccessor_ok.mp stepped)).trans kept

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

private theorem slashing_consolidationFrame {fork : Fork} {s t : BeaconState preset fork}
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  obtain ⟨exited, initiated, frame⟩ := slashValidator_departureQueues electra early ok
  exact (congrArg (fun q => q.2.2) frame).trans
    (initiateExit_consolidationFrame electra initiated)

private theorem proposerSlashing_consolidationFrame {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashing_consolidationFrame electra early slashed

private theorem attesterSlashing_consolidationFrame {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
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
    exact (slashing_consolidationFrame electra early slashed).trans kept
  · cases stepped; exact kept

private theorem withdrawalRequest_consolidationFrame {fork : Fork}
    {s t : BeaconState preset fork} (electra : .pectra ≤ fork) {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) :
    (departureQueues electra t).2.2 = (departureQueues electra s).2.2 := by
  rcases withdrawalRequest_cases ok with rfl | ⟨index, initiated⟩ | ⟨index, v, owed, paid⟩
  · rfl
  · exact initiateExit_consolidationFrame electra initiated
  · simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok] at paid
    obtain ⟨_, _, _, _, paid⟩ := paid
    split at paid
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at paid
      obtain ⟨⟨queued, epoch⟩, called, _, _, _, _, rfl⟩ := paid
      change (departureQueues electra queued).2.2 = (departureQueues electra s).2.2
      exact exitUpdate_consolidationFrame electra called
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

private theorem block_indexedTrace_sites {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    {sites : List (ForkedBeaconState preset)}
    (ok : processBlock config checks engine s block = .ok t)
    (recorded : blockConsolidationSites config checks engine s block = .ok sites)
    (cap : Nat)
    (rates : ∀ site ∈ sites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch s).toNat (exits ++ consolidations) ∧
      DepartureCoverage s t (exits ++ consolidations) ∧
      DepartureQueueTrace (s.earliestExitEpoch electra) (s.exitBalanceToConsume electra)
        (exits.map (·.call)) (t.earliestExitEpoch electra) (t.exitBalanceToConsume electra) ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (consolidations.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      (∀ called ∈ exits,
        called.call.rate.toNat ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat) ∧
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) ∧
      ConsolidationCallSites preset config consolidations sites := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [processBlock, processBlockAltair, altair, bellatrix, before, notGloas,
    ↓reduceDIte, pure_bind, bind_ok_iff] at ok
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
    operated, operatedOk, syncedOk⟩ := ok
  simp only [processOperations, notGloas, electra, ↓reduceDIte,
    bind_ok_iff, ensure_ok_iff] at operatedOk
  obtain ⟨expected, expectedOk, _, count, proposed, proposedOk, attested, attestedOk,
    votedAtt, votedAttOk, deposited, depositedOk, exited, exitedOk, changed, changedOk,
    requestsOk⟩ := operatedOk
  have requestsLife := registryLifecycle_processExecutionRequests requestsOk
  simp only [processExecutionRequests, bind_ok_iff] at requestsOk
  obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidatedOk⟩ := requestsOk
  obtain ⟨actualSites, replayed⟩ := consolidationRequestsSites_result
    (by simpa only [← Array.foldlM_toList] using consolidatedOk)
  have ensured : ensure ((block.body.deposits before).data.size = expected)
      (TransitionError.wrongDepositCount (block.body.deposits before).data.size expected) =
        .ok () := ensure_ok_iff.mpr count
  -- Both traversals reach the same withdrawal output before recording consolidation sites.
  have same : actualSites = sites := by
    rw [blockConsolidationSites, dite_eq_left ⟨electra, early⟩] at recorded
    simp only [headedOk, executedOk, revealedOk, votedOk, expectedOk, ensured,
      proposedOk, attestedOk, votedAttOk, depositedOk, exitedOk, changedOk,
      requestedOk, withdrawnOk, replayed, pure, Except.pure, bind, Except.bind,
      Except.ok.injEq] at recorded
    exact recorded
  subst actualSites
  rw [← Array.foldlM_toList] at proposedOk attestedOk votedAttOk depositedOk exitedOk
  rw [← Array.foldlM_toList] at requestedOk withdrawnOk consolidatedOk
  obtain ⟨first, firstFrom, firstCoverage, firstTrace, firstRates, firstLife, firstBalances⟩ :=
    operationsPrefix_coverage electra early proposedOk attestedOk votedAttOk depositedOk
      exitedOk changedOk
  obtain ⟨exits, consolidations, requestsFrom, covered, exitTrace, consolidationTrace,
    exitRates, consolidationRates, consolidationSites⟩ :=
    executionRequests_coverage_sites electra early requestedOk withdrawnOk consolidatedOk
      replayed cap rates
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
  have withdrawnFrame : (departureQueues electra withdrawn).2.2 =
      (departureQueues electra requested).2.2 :=
    foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra requested).2.2)
      (fun _ _ _ kept ok => (withdrawalRequest_consolidationFrame electra ok).trans kept)
      rfl withdrawnOk
  have operatedFrame : operated.earliestExitEpoch electra = withdrawn.earliestExitEpoch electra ∧
      operated.exitBalanceToConsume electra = withdrawn.exitBalanceToConsume electra :=
    foldlM_ok_invariant (fun t =>
      t.earliestExitEpoch electra = withdrawn.earliestExitEpoch electra ∧
      t.exitBalanceToConsume electra = withdrawn.exitBalanceToConsume electra)
      (fun _ _ _ kept ok =>
        let frame := consolidationRequest_exitFrame electra ok
        ⟨frame.1.trans kept.1, frame.2.trans kept.2⟩) ⟨rfl, rfl⟩ consolidatedOk
  have prefixFrame : (departureQueues electra changed).2.2 =
      (departureQueues electra voted).2.2 := by
    have one := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (proposerSlashing_consolidationFrame electra early ok).trans kept) rfl proposedOk
    have two := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (attesterSlashing_consolidationFrame electra early ok).trans kept) one attestedOk
    have three := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (congrArg (fun q => q.2.2) (attestation_departureQueues electra early ok)).trans kept)
      two votedAttOk
    have four := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (congrArg (fun q => q.2.2) (deposit_departureQueues electra ok)).trans kept)
      three depositedOk
    have five := foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (initiateExit_consolidationFrame electra (voluntaryExit_initiates ok)).trans kept)
      four exitedOk
    simp only [processBlsToExecutionChanges, capella, ↓reduceDIte,
      ← Array.foldlM_toList] at changedOk
    exact foldlM_ok_invariant
      (fun t => (departureQueues electra t).2.2 = (departureQueues electra voted).2.2)
      (fun _ _ _ kept ok =>
        (congrArg (fun q => q.2.2) (credentials_departureQueues electra ok)).trans kept)
      five changedOk
  have headFrame : departureQueues electra voted = departureQueues electra s := by
    have voteFrame := congrArg (departureQueues electra) (processEth1Data_eq votedOk).2.2
    change departureQueues electra voted = departureQueues electra revealed at voteFrame
    rw [voteFrame]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    simp only [processBlockExecution, notGloas, capella, ↓reduceDIte,
      bind_ok_iff] at executedOk
    obtain ⟨middle, withdrawn, payload⟩ := executedOk
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
    change departureQueues electra middle = departureQueues electra s
    rw [withdrawals_departureQueues electra early withdrawn]
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    rfl
  have tailFrame := sync_departureQueues electra syncedOk
  have operatedCoverage : DepartureCoverage voted operated
      ((first ++ exits) ++ consolidations) := by
    simpa only [List.append_assoc] using
      firstCoverage.append_of_effectiveKept covered firstLife requestsLife firstBalances
  have headData : voted.validators = s.validators := by
    have voteData : voted.validators = revealed.validators := by
      have eq := congrArg (·.validators) (processEth1Data_eq votedOk).2.2
      exact eq
    rw [voteData]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
    simp only [processBlockExecution, notGloas, capella, ↓reduceDIte,
      bind_ok_iff] at executedOk
    obtain ⟨middle, withdrawn, payload⟩ := executedOk
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
    change middle.validators = s.validators
    rw [withdrawals_registry electra early withdrawn]
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    rfl
  have tailData := sync_registry syncedOk
  refine ⟨first ++ exits, consolidations, ?_, ?_, ?_, ?_, ?_, consolidationRates,
    consolidationSites⟩
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
      ((congrArg (fun q => q.2.2) requestedFrame).trans
        (prefixFrame.trans (congrArg (fun q => q.2.2) headFrame)))
    have firstEpoch := congrArg Prod.fst initial
    have firstBalance := congrArg Prod.snd initial
    have lastEpoch := congrArg (fun q => q.2.2.1) tailFrame
    have lastBalance := congrArg (fun q => q.2.2.2) tailFrame
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

def _root_.EthLib.Consensus.Step.consolidationSites {x y : ForkedBeaconState preset}
    (step : Step config checks x y) : List (ForkedBeaconState preset) :=
  match step with
  | .slot _ => []
  | .block engine signed _ _ =>
    ((blockConsolidationSites config checks engine x.state signed.message).toOption).getD []

def _root_.EthLib.Consensus.Run.consolidationSites {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List (ForkedBeaconState preset)
  | _, .nil => []
  | _, .snoc pre step => pre.consolidationSites ++ step.consolidationSites

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

private theorem upgrades_registry {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) :
    t.state.validators.data = s.state.validators.data := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    have nextElectra := Nat.le_trans electra (Nat.le_of_lt next.property)
    have nextEarly := Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early
    rw [ih next nextElectra early rest]
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
      exact (upgradeToFulu_spec upgraded).1
    · simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at nextOk
      obtain ⟨_, _, rfl⟩ := nextOk
      exact False.elim (Nat.lt_irrefl _ nextEarly)
  | case2 s notDue => cases ok; rfl

private theorem step_indexedTrace_sites {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap : Nat)
    (rates : ∀ site ∈ step.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch x.state).toNat (exits ++ consolidations) ∧
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
      ConsolidationCallSites preset config consolidations step.consolidationSites := by
  have sourceEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    have frame := upgrades_departureQueues (s := ⟨x.fork, advanced⟩)
      electra early upgraded targetElectra
    have data := upgrades_registry (s := ⟨x.fork, advanced⟩) electra early upgraded
    obtain ⟨calls, firsts, trace, covered, exitRates⟩ :=
      slot_indexedTrace electra sourceEarly advancedOk
    have consolidationFrame := slot_consolidationFrame electra sourceEarly advancedOk
    have first := congrArg Prod.fst frame
    have left := congrArg (fun q => q.2.1) frame
    change y.state.earliestExitEpoch targetElectra = advanced.earliestExitEpoch electra at first
    change y.state.exitBalanceToConsume targetElectra = advanced.exitBalanceToConsume electra
      at left
    refine ⟨calls, [], ?_, ?_, ?_, ?_, exitRates, by simp,
      by simp [ConsolidationCallSites]⟩
    · simpa only [List.append_nil] using firsts
    · simpa only [List.append_nil] using
        (show DepartureCoverage x.state y.state calls from fun i old next before after =>
          covered i old next before (by simpa only [data] using after))
    · rw [first, left]
      exact trace
    · have both := (congrArg (fun q => q.2.2) frame).trans consolidationFrame
      have epoch := congrArg Prod.fst both
      have balance := congrArg Prod.snd both
      change y.state.earliestConsolidationEpoch targetElectra =
        x.state.earliestConsolidationEpoch electra at epoch
      change y.state.consolidationBalanceToConsume targetElectra =
        x.state.consolidationBalanceToConsume electra at balance
      rw [epoch, balance]
      exact .nil _ _
  | block engine signed due ok =>
    have processed := (applySignedBlock_ok ok).2.1
    obtain ⟨sites, recorded⟩ := blockConsolidationSites_result processed
    have bounded : ∀ site ∈ sites, ∀ (h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap := by
      intro site member h rate computed
      apply rates site ?_ h rate computed
      simpa only [Step.consolidationSites, recorded, Except.toOption, Option.getD_some] using member
    simpa only [Step.consolidationSites, recorded, Except.toOption, Option.getD_some] using
      block_indexedTrace_sites electra early processed recorded cap bounded

private theorem run_indexedTrace_sites {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap : Nat)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch x.state).toNat (exits ++ consolidations) ∧
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
      ConsolidationCallSites preset config consolidations tail.consolidationSites := by
  induction tail with
  | nil =>
    exact ⟨[], [], by simp [DepartureCallsFrom], by simp [Run.departureCharges],
      .nil _ _, .nil _ _, by simp, by simp, by simp [ConsolidationCallSites]⟩
  | snoc pre step ih =>
    have middleElectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
    obtain ⟨firstExits, firstConsolidations, firstFrom, firstMatched, firstExitTrace,
      firstConsolidationTrace, firstExitRates, firstConsolidationRates, firstSites⟩ := ih
        (Nat.lt_of_le_of_lt step.chainStep.fork_le early) middleElectra
        (fun site member h rate computed =>
          rates site (List.mem_append_left _ member) h rate computed)
    obtain ⟨lastExits, lastConsolidations, lastFrom, covered, lastExitTrace,
      lastConsolidationTrace, lastExitRates, lastConsolidationRates, lastSites⟩ :=
      step_indexedTrace_sites step middleElectra early targetElectra cap
        (fun site member h rate computed =>
          rates site (List.mem_append_right _ member) h rate computed)
    refine ⟨firstExits ++ lastExits, firstConsolidations ++ lastConsolidations,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have ordered := UInt64.le_iff_toNat_le.mp
        (currentEpoch_le_of_chainSteps pre.chainSteps)
      have lastFrom := DepartureCallsFrom.mono lastFrom ordered
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

/-- Run charges match tagged calls without identifying partial withdrawals with departures. -/
private theorem run_indexedTrace {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (targetElectra : .pectra ≤ y.fork) (cap : Nat)
    (rates : ∀ site ∈ tail.consolidationSites,
      ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate → rate.toNat ≤ cap) :
    ∃ exits consolidations : List IndexedDepartureCall,
      DepartureCallsFrom (getCurrentEpoch x.state).toNat (exits ++ consolidations) ∧
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
      (∀ called ∈ consolidations, called.call.rate.toNat ≤ cap) := by
  obtain ⟨exits, consolidations, firsts, covered, exitTrace, consolidationTrace,
    exitRates, consolidationRates, _⟩ :=
    run_indexedTrace_sites tail electra early targetElectra cap rates
  exact ⟨exits, consolidations, firsts, covered, exitTrace, consolidationTrace,
    exitRates, consolidationRates⟩

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
      (high + 2 - (getCurrentEpoch x.state).toNat) *
        (config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + cap) := by
  have targetElectra := Nat.le_trans electra (fork_le_of_chainSteps tail.chainSteps)
  obtain ⟨exits, consolidations, firsts, matched, exitTrace, consolidationTrace,
    exitRates, consolidationRates⟩ := run_indexedTrace tail electra early targetElectra cap rates
  have charges := departureCharges_le_calls (departureCharges_run_indices tail) matched (high + 1)
  have queueBound {calls : List IndexedDepartureCall} {first last : Epoch} {available left : Gwei}
      (trace : DepartureQueueTrace first available (calls.map (·.call)) last left) (cap : Nat)
      (rates : ∀ called ∈ calls, called.call.rate.toNat ≤ cap)
      (firsts : DepartureCallsFrom (getCurrentEpoch x.state).toNat calls) :
      ((calls.filter fun called => called.call.epoch.toNat ≤ high + 1).map
        fun called => called.call.amount.toNat).sum ≤
          (if first.toNat ≤ high + 1 then available.toNat else 0) +
            (high + 2 - (getCurrentEpoch x.state).toNat) * cap := by
    have budget := trace.window_le_from (getCurrentEpoch x.state).toNat (high + 1) cap
      (by
        intro call member
        obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
        exact rates called present)
      (by
        intro call member
        obtain ⟨called, present, rfl⟩ := List.mem_map.mp member
        exact firsts called present)
    simpa only [List.filter_map, List.map_map, Function.comp_def,
      Nat.add_assoc, Nat.reduceAdd] using budget
  have exitBound := queueBound exitTrace _ exitRates
    (fun called member => firsts called (List.mem_append_left _ member))
  have consolidationBound := queueBound consolidationTrace cap consolidationRates
    (fun called member => firsts called (List.mem_append_right _ member))
  simp only [List.filter_append, List.map_append, List.sum_append] at charges
  rw [Nat.mul_add]
  omega

private def ExitCohortsBounded {fork : Fork} (cap : Nat) (s : BeaconState preset fork) : Prop :=
  ∀ epoch : Epoch, epoch ≠ FAR_FUTURE_EPOCH →
    s.validators.data.toList.countP (·.exitEpoch == epoch) ≤ cap

private structure CountCohortStep {f h : Fork} (config : Config) (bound : Nat)
    (s : BeaconState preset f) (t : BeaconState preset h) : Prop where
  grows : s.validators.data.size ≤ t.validators.data.size
  bounded : t.validators.data.size ≤ bound →
    ExitCohortsBounded (max 1 (cohortCap config bound)) s →
    ExitCohortsBounded (max 1 (cohortCap config bound)) t
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
    fun size capped => two.bounded size (one.bounded (two.grows.trans size) capped),
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

private theorem CountCohortStep.setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {i : Nat} {v w : Validator} (bound : Nat) (found : getValidatorAt s i = .ok v)
    (room : w.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch ≠ w.exitEpoch →
      s.validators.data.size ≤ bound →
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
  · intro size capped epoch finite
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
      · have room := room finite previous (by simpa [BeaconState.putValidator] using size)
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
  .setValidatorAt bound found (fun _ different _ => False.elim (different same.symm)) ok
    (.inl same)

private theorem CountCohortStep.exit {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t) : CountCohortStep config bound s t := by
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
    · intro finite _ size
      simpa only [List.countP_eq_length_filter] using
        (exitQueue_count_room early queue finite bound size).2

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
    (ok : slashValidator config s index whistleblower = .ok t) :
    CountCohortStep config bound s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  have first := (CountCohortStep.exit early bound exited).trans
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
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact .refl _ bound
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact .add bound ok
    · cases ok; exact .refl _ bound
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact .increase bound ok

private theorem CountCohortStep.processDeposit {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    CountCohortStep config bound s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  have notElectra : ¬ .pectra ≤ f := Nat.not_le_of_lt early
  simp only [applyDeposit, notElectra, ↓reduceDIte] at credited
  exact (CountCohortStep.data bound (s := s)
    (t := { s with eth1DepositIndex := fun _ => next })).trans (.deposit bound credited)

private theorem CountCohortStep.registryEntry {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {index : Nat}
    (ok : updateRegistryEntry config s index = .ok t) : CountCohortStep config bound s t := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, queued, queue, marked, set, ok⟩ := ok
  have same : queued.exitEpoch = v.exitEpoch := by
    unfold queueForActivation at queue
    split at queue
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
      obtain ⟨_, _, rfl⟩ := queue
      rfl
    · cases queue; rfl
  have first := CountCohortStep.setExitUnchanged (config := config) bound found set same
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact first.trans (.exit early bound exited)
  · cases ok; exact first

private theorem CountCohortStep.activate {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {index : ValidatorIndex} (ok : activateValidator s index = .ok t) :
    CountCohortStep config bound s t := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, set⟩ := ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  exact .setExitUnchanged bound found set rfl

private theorem CountCohortStep.registry {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) (ok : processRegistryUpdates config s = .ok t) :
    CountCohortStep config bound s t := by
  have notElectra : ¬ .pectra ≤ f := Nat.not_le_of_lt early
  simp only [processRegistryUpdates, notElectra, ↓reduceIte, bind_ok_iff] at ok
  obtain ⟨_, updated, activated⟩ := ok
  exact (CountCohortStep.fold (fun _ _ _ => CountCohortStep.registryEntry early bound)
    updated).trans (.fold (fun _ _ _ => CountCohortStep.activate bound) activated)

private theorem CountCohortStep.proposerSlashing {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) :
    CountCohortStep config bound s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact .slash early bound slashed

private theorem CountCohortStep.attesterSlashing {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) :
    CountCohortStep config bound s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  refine foldlM_ok_invariant (fun step => CountCohortStep config bound s step.1)
    ?_ (.refl _ bound) folded
  intro step i next previous computed
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact previous.trans (.slash early bound slashed)
  · cases computed; exact previous

private theorem CountCohortStep.blsChange {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) :
    CountCohortStep config bound s t := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  rw [getValidator_eq_getValidatorAt] at found
  rw [setValidator_eq_setValidatorAt] at set
  exact .setExitUnchanged bound found set rfl

private theorem CountCohortStep.operations {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {body : BeaconBlockBody preset f} {parentSlot : Slot}
    (ok : processOperations config checks s body parentSlot = .ok t) :
    CountCohortStep config bound s t := by
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt (early.trans (by decide))
  unfold processOperations at ok
  simp only [notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changesOk, requestsOk⟩ := ok
  have changes : CountCohortStep config bound exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact .fold (fun _ _ _ => CountCohortStep.blsChange bound) changesOk
    · cases changesOk; exact .refl _ bound
  have same : t = changed := by
    split at requestsOk
    · exact False.elim (Nat.not_le_of_lt early (by assumption))
    · cases requestsOk; rfl
  subst t
  exact (CountCohortStep.fold (fun _ _ _ => CountCohortStep.proposerSlashing early bound)
    proposers).trans <|
    (CountCohortStep.fold (fun _ _ _ => CountCohortStep.attesterSlashing early bound)
      attesters).trans <|
    (CountCohortStep.fold (fun _ _ _ computed => CountCohortStep.data bound
      (by rw [(processAttestation_registry computed).1])
      (by simp only [getCurrentEpoch, (frame_processAttestation computed).slot]
          exact Nat.le_refl _)) attestations).trans <|
    (CountCohortStep.fold (fun _ _ _ => CountCohortStep.processDeposit early bound)
      deposits).trans <|
    (CountCohortStep.fold (fun _ _ _ computed =>
      CountCohortStep.exit early bound (voluntaryExit_initiates computed)) exits).trans changes

private theorem CountCohortStep.effective {f : Fork} {s t : BeaconState preset f}
    (bound : Nat) (ok : processEffectiveBalanceUpdates s = .ok t) :
    CountCohortStep config bound s t := by
  unfold processEffectiveBalanceUpdates at ok
  refine CountCohortStep.fold (fun _ _ _ computed => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, found, _, _, _, _, set⟩ := computed
  exact .setExitUnchanged bound found set rfl

private theorem CountCohortStep.epoch {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) (ok : processEpoch config checks s = .ok t) :
    CountCohortStep config bound s t := by
  apply (processEpoch_trace ok).transport (CountCohortStep config bound)
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
  case effectiveBalances => exact .effective bound edge
  all_goals
    exact .data bound (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))
      (by simp only [getCurrentEpoch, epochStage_slot edge]; exact Nat.le_refl _)

private theorem CountCohortStep.withdrawals {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {capella : .shapella ≤ f}
    {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (ok : processWithdrawals s capella payload = .ok t) : CountCohortStep config bound s t := by
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt (Nat.lt_trans early (by decide))
  have notElectra : ¬ .pectra ≤ f := Nat.not_le_of_lt early
  have slot := (frame_processWithdrawals ok).slot
  simp only [processWithdrawals, notGloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at ok
  obtain ⟨expected, _, _, _, applied⟩ := ok
  simp only [applyExpectedWithdrawals, notGloas, notElectra, ↓reduceDIte, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at applied
  obtain ⟨withdrawn, paid, indexed, moved, swept⟩ := applied
  have paidData : withdrawn.validators = s.validators := by
    unfold applyWithdrawals at paid
    rw [← Array.foldlM_toList] at paid
    refine foldlM_ok_invariant (fun t => t.validators = s.validators) ?_ rfl paid
    intro a withdrawal b kept stepped
    simp only [applyWithdrawal, notGloas, false_and, ↓reduceDIte] at stepped
    exact (decreaseBalance_validators stepped).trans kept
  have movedData : indexed.validators = withdrawn.validators := by
    unfold updateNextWithdrawalIndex at moved
    split at moved
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at moved
      obtain ⟨_, _, rfl⟩ := moved
      rfl
    · cases moved; rfl
  have sweptData : t.validators = indexed.validators := by
    simp only [updateNextWithdrawalValidatorIndex, bind_ok_iff] at swept
    obtain ⟨_, _, swept⟩ := swept
    split at swept
    · cases swept
    · cases swept; rfl
  exact .data bound (congrArg (·.data) (sweptData.trans (movedData.trans paidData)))
    (by simp only [getCurrentEpoch, slot]; exact Nat.le_refl _)

private theorem CountCohortStep.block {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) {engine : ExecutionEngine preset f}
    {block : BeaconBlock preset f} (ok : processBlock config checks engine s block = .ok t) :
    CountCohortStep config bound s t := by
  have data {a b : BeaconState preset f} (same : b.validators = a.validators)
      (slot : b.slot = a.slot) : CountCohortStep config bound a b :=
    .data bound (congrArg (·.data) same)
      (by simp only [getCurrentEpoch, slot]; exact Nat.le_refl _)
  have header {a b : BeaconState preset f} {block : BeaconBlock preset f}
      (computed : processBlockHeader a block = .ok b) : CountCohortStep config bound a b := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
    exact .data bound rfl
  have randao {a b : BeaconState preset f} {body : BeaconBlockBody preset f}
      (computed : processRandao config checks a body = .ok b) :
      CountCohortStep config bound a b := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
    exact .data bound rfl
  have vote {a b : BeaconState preset f} {body : BeaconBlockBody preset f} {before : f < .hegota}
      (computed : processEth1Data before a body = .ok b) : CountCohortStep config bound a b := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
    rw [← rest]
    exact .data bound rfl
  have execution {a b : BeaconState preset f} {body : BeaconBlockBody preset f}
      {bellatrix : .bellatrix ≤ f}
      (computed : processBlockExecution config checks engine a body bellatrix = .ok b) :
      CountCohortStep config bound a b := by
    have payload {a b : BeaconState preset f} {bellatrix : .bellatrix ≤ f ∧ f < .glamsterdam}
        (computed : processExecutionPayload config engine a body bellatrix = .ok b) :
        CountCohortStep config bound a b := by
      obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
      exact .data bound rfl
    unfold processBlockExecution at computed
    split at computed
    · exact False.elim (Nat.not_le_of_lt
        (Nat.lt_trans early (by decide : Fork.pectra < .glamsterdam)) (by assumption))
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, withdrawn, paid⟩ := computed
      exact (CountCohortStep.withdrawals early bound withdrawn).trans (payload paid)
    · dsimp only at computed
      split at computed
      · exact payload computed
      · cases computed; exact .refl _ bound
  unfold processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := ok
    have paidSame : paid = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt
          (Nat.lt_trans early (by decide : Fork.pectra < .glamsterdam)) (by assumption))
      · cases paidOk; rfl
    subst paid
    have executionStep : CountCohortStep config bound headed executed := by
      split at executedOk
      · exact execution executedOk
      · cases executedOk; exact .refl _ bound
    have votedStep : CountCohortStep config bound revealed voted := by
      split at votedOk
      · exact vote votedOk
      · cases votedOk; exact .refl _ bound
    exact (header headedOk).trans <| executionStep.trans <| (randao revealedOk).trans <|
      votedStep.trans <| (CountCohortStep.operations early bound operatedOk).trans <|
      data (sync_registry synced) (frame_processSyncAggregate synced).slot
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, headed, _, revealed, _, voted, operated⟩ := ok
    exact (header headed).trans <| (randao revealed).trans <| (vote voted).trans <|
      CountCohortStep.operations early bound operated

private theorem CountCohortStep.slot {f : Fork} {s t : BeaconState preset f}
    (early : f < .pectra) (bound : Nat) (ok : advanceSlot config checks s = .ok t) :
    CountCohortStep config bound s t := by
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
      exact ⟨.epoch early bound advanced,
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
    (targetEarly : t.fork < .glamsterdam) :
    CountCohortStep config bound s.state t.state := by
  cases step with
  | block engine signed due ok =>
    exact CountCohortStep.block early bound (applySignedBlock_ok ok).2.1
  | slot ok =>
    obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
    exact (CountCohortStep.slot early bound slotOk).trans
      (CountCohortStep.upgrades bound upgrades targetEarly)

private theorem CountCohortStep.step {s t : ForkedBeaconState preset} (bound : Nat)
    (step : Step config checks s t) (early : t.fork < .pectra) :
    CountCohortStep config bound s.state t.state :=
  .crossing bound step (Nat.lt_of_le_of_lt step.chainStep.fork_le early)
    (Nat.lt_trans early (by decide))

private theorem CountCohortStep.run {s t : ForkedBeaconState preset} (bound : Nat)
    (run : Run config checks s t) (early : t.fork < .pectra) :
    CountCohortStep config bound s.state t.state := by
  induction run with
  | nil => exact .refl _ bound
  | snoc pre step ih =>
    exact (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early)).trans
      (CountCohortStep.step bound step early)

private theorem genesis_cohorts {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) (bound : Nat)
    (size : g.state.validators.data.size ≤ bound) :
    ExitCohortsBounded (max 1 (cohortCap config bound)) g.state := by
  obtain ⟨hash, time, deposits, ok⟩ := genesis
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    equal⟩ := initializeBeaconStateFromEth1_ok ok
  have first := CountCohortStep.fold (bound := bound) (config := config)
    (fun a entry b computed => by
      simp only [genesisDeposit, bind_ok_iff] at computed
      obtain ⟨depositRoot, _, paid⟩ := computed
      exact (CountCohortStep.data bound (s := a)
        (t := { a with eth1Data := fun _ => { a.eth1Data _ with depositRoot } })).trans
          (CountCohortStep.processDeposit (Nat.lt_trans before (by decide)) bound paid))
    depositedOk
  have second := CountCohortStep.fold (bound := bound) (config := config)
    (fun a i b computed => by
      simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨validator, found, balance, _, set⟩ := computed
      apply CountCohortStep.setExitUnchanged bound found set
      split <;> rfl) activatedOk
  rw [equal]
  apply (first.trans second).bounded
  · simpa only [equal] using size
  · intro epoch finite
    simp [emptyGenesisState]

private theorem run_cohorts {g y : ForkedBeaconState preset}
    (run : Run config checks g y) (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .pectra) (bound : Nat) (size : y.state.validators.data.size ≤ bound) :
    ExitCohortsBounded (max 1 (cohortCap config bound)) y.state := by
  have kept := CountCohortStep.run bound run early
  exact kept.bounded size (genesis_cohorts genesis bound (kept.grows.trans size))

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
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at assigned
      have placed :=
        (CountCohortStep.crossing 0 step early targetEarly).future i old next found after
      have lower : (getCurrentEpoch x.state).toNat ≤ next.exitEpoch.toNat := by
        rcases placed with same | lower
        · exact False.elim (assigned.2 (same.trans assigned.1))
        · exact lower
      have capped := shared.effectiveBalance_capped genesis caps.activation caps.compounding
        (Nat.lt_trans early (by decide)) old (Array.mem_of_getElem? found)
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
      exact ⟨(CountCohortStep.run 0 pre middleEarly).epochs.trans bounds.1, bounds.2⟩

private theorem charge_count_le_cohort {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (epoch : Nat) :
    tail.departureCharges.countP (fun charge => charge.epoch == epoch) ≤
      y.state.validators.data.toList.countP (fun v => v.exitEpoch.toNat == epoch) := by
  let selected := tail.departureCharges.filter (fun charge => charge.epoch == epoch)
  let validators := y.state.validators.data.toList.zipIdx.filter
    (fun entry => entry.1.exitEpoch.toNat == epoch)
  have unique : (selected.map (·.index)).Nodup :=
    ((List.filter_sublist).map DepartureCharge.index).nodup (departureCharges_run_indices tail)
  have subset : selected.map (·.index) ⊆ validators.map Prod.snd := by
    intro i member
    obtain ⟨charge, selectedMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨chargeMember, same⟩ := List.mem_filter.mp selectedMember
    obtain ⟨v, found, _, exit⟩ := tail.departure_charge_exit charge chargeMember
    apply List.mem_map.mpr
    refine ⟨(v, charge.index), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using found
    · simpa only [exit] using same
  have bound := unique.length_le_of_subset subset
  simp only [List.length_map] at bound
  have count : validators.length =
      y.state.validators.data.toList.countP (fun v => v.exitEpoch.toNat == epoch) := by
    dsimp only [validators]
    rw [← List.countP_eq_length_filter]
    have mapped := List.countP_map (l := y.state.validators.data.toList.zipIdx)
      (f := Prod.fst) (p := fun v => v.exitEpoch.toNat == epoch)
    simpa only [List.zipIdx_map_fst, Function.comp_def] using mapped.symm
  simpa only [selected, ← List.countP_eq_length_filter, count] using bound

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
    (cohorts : ExitCohortsBounded cap y.state)
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
    exact (charge_count_le_cohort tail epoch).trans (by
      rw [predicates]
      exact cohorts v.exitEpoch finite)
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
    (size : y.state.validators.data.size ≤ bound) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high).map (·.amount)).sum ≤
      (high + 1 - (getCurrentEpoch x.state).toNat) *
        (max 1 (cohortCap config bound) * preset.MAX_EFFECTIVE_BALANCE.toNat) :=
  charges_le_window_of_cohorts tail _ high _ _
    (run_cohorts (shared.append tail) genesis early bound size)
    (pre_electra_charge_bounds shared tail genesis caps early)

private theorem crossing_charges_le_window {g x middle y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x middle)
    (step : Step config checks middle y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : middle.fork < .pectra) (targetEarly : y.fork < .glamsterdam) (high bound : Nat)
    (size : y.state.validators.data.size ≤ bound) :
    (((pre.snoc step).departureCharges.filter fun c => c.epoch ≤ high).map (·.amount)).sum ≤
      (high + 1 - (getCurrentEpoch x.state).toNat) *
        (max 1 (cohortCap config bound) * preset.MAX_EFFECTIVE_BALANCE.toNat) := by
  have kept := CountCohortStep.crossing bound step early targetEarly
  apply charges_le_window_of_cohorts (pre.snoc step) _ high _ _
    (kept.bounded size (run_cohorts (shared.append pre) genesis early bound
      (kept.grows.trans size)))
  intro charge member
  rcases List.mem_append.mp member with earlier | latest
  · exact pre_electra_charge_bounds shared pre genesis caps early charge earlier
  · have bounds := pre_electra_charge_step_bounds (shared.append pre) step genesis caps
      early targetEarly charge latest
    exact ⟨(CountCohortStep.run 0 pre early).epochs.trans bounds.1, bounds.2⟩

private theorem slot_same_epoch_registry {fork : Fork} {s t : BeaconState preset fork}
    (ok : advanceSlot config checks s = .ok t) (epoch : getCurrentEpoch t = getCurrentEpoch s) :
    t.validators.data = s.validators.data := by
  obtain ⟨next, cached, epoched, sum, cachedOk, advanced, rfl⟩ := advanceSlot_ok ok
  have cachedData : cached.validators.data = s.validators.data := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have quotient : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
      s.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simpa only [getCurrentEpoch_toNat] using congrArg UInt64.toNat epoch
  have notLast : next % preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro last
    have remainder : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa only [UInt64.toNat_mod, UInt64.reduceToNat] using congrArg UInt64.toNat last
    have before := Nat.mod_add_div s.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have after := Nat.mod_add_div next.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [quotient, remainder] at after
    omega
  simp only [epochIfLast, notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at advanced
  subst epoched
  exact cachedData

private theorem step_same_epoch_effective {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam)
    (epoch : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    ∀ i, i < x.state.validators.data.size → effectiveAt y i = effectiveAt x i := by
  cases step with
  | block engine signed due ok =>
    exact effectiveKept_block early (applySignedBlock_ok ok).2.1
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    have slot := processUpgrades_slot upgraded
    have intermediateEpoch : getCurrentEpoch advanced = getCurrentEpoch x.state := by
      simpa only [getCurrentEpoch, slot] using epoch
    have data := (upgrades_registry (s := ⟨x.fork, advanced⟩) electra early upgraded).trans
      (slot_same_epoch_registry advancedOk intermediateEpoch)
    intro i _
    simp only [effectiveAt, data]

private theorem run_same_epoch_effective {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam)
    (epoch : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    ∀ i, i < x.state.validators.data.size → effectiveAt y i = effectiveAt x i := by
  induction tail with
  | nil => intro _ _; rfl
  | snoc pre step ih =>
    have middleEpoch : getCurrentEpoch _ = getCurrentEpoch x.state :=
      UInt64.le_antisymm
        (by simpa only [epoch] using step.chainStep.currentEpoch_le)
        (currentEpoch_le_of_chainSteps pre.chainSteps)
    have one := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) middleEpoch
    have two := step_same_epoch_effective step
      (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) early
      (epoch.trans middleEpoch.symm)
    intro i inside
    exact (two i (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps))).trans
      (one i inside)

private theorem total_active_congr {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (before : f < .glamsterdam) (after : h < .glamsterdam)
    (active : ActiveKept (getCurrentEpoch s) s t) (epoch : getCurrentEpoch t = getCurrentEpoch s)
    (effective : ∀ i, i < s.validators.data.size →
      effectiveAt ⟨h, t⟩ i = effectiveAt ⟨f, s⟩ i) :
    getTotalActiveBalance t = getTotalActiveBalance s := by
  classical
  let indices := getActiveValidatorIndices s (getCurrentEpoch s)
  have checked := active.getActiveValidatorIndicesChecked_eq (UInt64.le_refl _)
  have inside (i : ValidatorIndex) (member : i ∈ indices) : i.toNat < s.validators.data.size := by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (s.validators.bound before)).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have targetIndices := active.getActiveValidatorIndices_eq (UInt64.le_refl _)
  have targetInside (i : ValidatorIndex) (member : i ∈ indices) :
      i.toNat < t.validators.data.size := by
    change i ∈ getActiveValidatorIndices s (getCurrentEpoch s) at member
    rw [← targetIndices] at member
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (t.validators.bound after)).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have sum : Models.stake (fun i => balanceAt t i.toNat) indices.toFinset =
      Models.stake (fun i => balanceAt s i.toNat) indices.toFinset := by
    apply Finset.sum_congr rfl
    intro i member
    exact effective i.toNat (inside i (List.mem_toFinset.mp member))
  have sourceNone : indices.find? (s.validators.data.size ≤ ·.toNat) = none := by
    apply List.find?_eq_none.mpr
    intro i member
    have bound := inside i member
    simp only [decide_eq_true_eq]
    omega
  have targetNone : indices.find? (t.validators.data.size ≤ ·.toNat) = none := by
    apply List.find?_eq_none.mpr
    intro i member
    have bound := targetInside i member
    simp only [decide_eq_true_eq]
    omega
  unfold getTotalActiveBalance
  rw [epoch, checked, getActiveValidatorIndicesChecked_of_within
    (state := s) (s.validators.bound before)]
  simp only [bind, Except.bind]
  change getTotalBalance t indices = getTotalBalance s indices
  simp only [getTotalBalance, sourceNone, targetNone, sumMarked_markIndices_eq_stake, sum]

private structure SitePrefix {fork : Fork} (s t : BeaconState preset fork) : Prop where
  identity : RegistryIdentity s t
  active : ActiveStep s t
  effective : EffectiveKept s t

private theorem SitePrefix.refl {fork : Fork} (s : BeaconState preset fork) : SitePrefix s s :=
  ⟨.refl _, .refl _, effectiveKept_refl _⟩

private theorem SitePrefix.trans {fork : Fork} {s t u : BeaconState preset fork}
    (one : SitePrefix s t) (two : SitePrefix t u) : SitePrefix s u :=
  ⟨one.identity.trans two.identity, one.active.trans two.active,
    effectiveKept_trans one.effective two.effective
      (by simpa [validatorKeys] using one.identity.kept.length_le)⟩

private theorem SitePrefix.fold {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (kept : ∀ s a t, action s a = .ok t → SitePrefix s t)
    {s t : BeaconState preset fork} {items : List α}
    (ok : items.foldlM action s = .ok t) : SitePrefix s t :=
  foldlM_ok_invariant (SitePrefix s)
    (fun _ _ _ previous computed => previous.trans (kept _ _ _ computed)) (.refl s) ok

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
        (frame_processConsolidationRequest stepped).toFrame.registryIdentity
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
    have head : SitePrefix s headed := by
      refine ⟨(frame_processBlockHeader headedOk).toFrame.registryIdentity,
        activeStep_processBlockHeader headedOk, ?_⟩
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact effectiveKept_refl _
    have execution : SitePrefix headed executed := by
      refine ⟨(frame_processBlockExecution executedOk).toFrame.registryIdentity,
        activeStep_processBlockExecution executedOk, ?_⟩
      have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt electra.2
      have capella : .shapella ≤ fork := Nat.le_trans (by decide) electra.1
      simp only [processBlockExecution, notGloas, capella, ↓reduceDIte,
        bind_ok_iff] at executedOk
      obtain ⟨middle, withdrawn, payload⟩ := executedOk
      obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok payload
      simpa only [EffectiveKept, effectiveAt] using effectiveKept_withdrawals withdrawn
    have randao : SitePrefix executed revealed := by
      refine ⟨(frame_processRandao revealedOk).toFrame.registryIdentity,
        activeStep_processRandao revealedOk, ?_⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq revealedOk
      exact effectiveKept_refl _
    have vote : SitePrefix revealed voted := by
      refine ⟨(frame_processEth1Data votedOk).toFrame.registryIdentity,
        activeStep_processEth1Data votedOk, ?_⟩
      obtain ⟨_, _, rest⟩ := processEth1Data_eq votedOk
      exact effectiveKept_data (congrArg (·.validators.data) rest)
    have proposers : SitePrefix voted proposed := SitePrefix.fold
      (fun _ _ _ h => ⟨(frame_processProposerSlashing h).toFrame.registryIdentity,
        activeStep_processProposerSlashing h, effectiveKept_proposerSlashing h⟩) proposedOk
    have attesters : SitePrefix proposed attested := SitePrefix.fold
      (fun _ _ _ h => ⟨(frame_processAttesterSlashing h).toFrame.registryIdentity,
        activeStep_processAttesterSlashing h, effectiveKept_attesterSlashing h⟩) attestedOk
    have attestations : SitePrefix attested votedAtt := SitePrefix.fold
      (fun _ _ _ h => ⟨(frame_processAttestation h).registryIdentity,
        activeStep_processAttestation h,
        effectiveKept_data (by rw [(processAttestation_registry h).1])⟩) votedAttOk
    have deposits : SitePrefix votedAtt deposited := SitePrefix.fold
      (fun _ _ _ h => ⟨(frame_processDeposit h).toFrame.registryIdentity,
        activeStep_processDeposit h, effectiveKept_processDeposit h⟩) depositedOk
    have exits : SitePrefix deposited exited := SitePrefix.fold
      (fun _ _ _ h => ⟨(frame_processVoluntaryExit h).toFrame.registryIdentity,
        activeStep_processVoluntaryExit h, effectiveKept_voluntaryExit h⟩) exitedOk
    have changes : SitePrefix exited changed := by
      unfold processBlsToExecutionChanges at changedOk
      split at changedOk
      · rw [← Array.foldlM_toList] at changedOk
        exact SitePrefix.fold (fun _ _ _ h =>
          ⟨(frame_processBlsToExecutionChange h).toFrame.registryIdentity,
          activeStep_processBlsToExecutionChange h, effectiveKept_blsChange h⟩) changedOk
      · cases changedOk; exact .refl _
    have requests : SitePrefix changed requested := SitePrefix.fold
      (fun _ _ _ h => ⟨(frame_processDepositRequest h).toFrame.registryIdentity,
        activeStep_processDepositRequest h, effectiveKept_depositRequest h⟩) requestedOk
    have withdrawals : SitePrefix requested withdrawn := SitePrefix.fold
      (fun _ _ _ h => ⟨(frame_processWithdrawalRequest h).toFrame.registryIdentity,
        activeStep_processWithdrawalRequest h, effectiveKept_withdrawalRequest h⟩) withdrawnOk
    obtain ⟨u, same, kept⟩ := consolidationRequestsSites_prefix replayed site member
    exact ⟨u, same, head.trans (execution.trans (randao.trans (vote.trans (proposers.trans
      (attesters.trans (attestations.trans (deposits.trans (exits.trans (changes.trans
        (requests.trans (withdrawals.trans kept)))))))))))⟩
  · cases ok; simp at member

private theorem consolidationSite_epoch_total {x y : ForkedBeaconState preset}
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
              (Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) middleEarly)
              middleEarly
              ((activeKept_of_chainSteps pre.chainSteps).mono
                (getCurrentEpoch_le_activityFixedEpoch x.state))
              (epoch.symm.trans same)
              (run_same_epoch_effective pre electra middleEarly (epoch.symm.trans same))
            have second := total_active_congr middleEarly middleEarly
              (kept.active.2.mono (getCurrentEpoch_le_activityFixedEpoch before)) epoch
              kept.effective
            exact second.trans first

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
    · have rest := tail.window_le high cap
        (fun c member => rates c (List.mem_cons_of_mem _ member))
      by_cases inside : call.epoch.toNat ≤ high
      · obtain ⟨placed, spent, _⟩ := churnQueue_spend call.computed
        have placed := UInt64.le_iff_toNat_le.mp placed
        have reset' : call.earliest < max call.earliest call.first := by
          rw [UInt64.lt_iff_toNat_lt, Uint64.toNat_max]
          exact Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp reset) (Nat.le_max_right _ _)
        rw [ite_eq_left reset', Uint64.toNat_max] at spent
        rw [Uint64.toNat_max] at placed
        have one : call.left.toNat + call.amount.toNat ≤
            (call.epoch.toNat + 1 - start) * cap := by
          calc
            _ = (call.epoch.toNat - max call.earliest.toNat call.first.toNat + 1) *
                call.rate.toNat := by rw [spent, Nat.add_mul, Nat.one_mul]; omega
            _ ≤ _ := Nat.mul_le_mul (by omega) (rates call (by simp))
        have distance : (call.epoch.toNat + 1 - start) + (high - call.epoch.toNat) =
            high + 1 - start := by omega
        have combined := Nat.add_le_add_right one ((high - call.epoch.toNat) * cap)
        rw [← Nat.add_mul, distance] at combined
        simp only [departureQueuePotential, inside, ↓reduceIte] at rest
        simp only [List.filter_cons, decide_eq_true inside, ↓reduceIte,
          List.map_cons, List.sum_cons]
        omega
      · simp only [departureQueuePotential, inside, ↓reduceIte] at rest
        simp only [List.filter_cons, decide_eq_false inside, Bool.false_eq_true, ↓reduceIte]
        omega

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
  have fields := upgrades_departureQueues electra early ok targetElectra
  have data := upgrades_registry electra early ok
  have epoch : getCurrentEpoch t.state = getCurrentEpoch s.state := by
    simp only [getCurrentEpoch, processUpgrades_slot ok]
  have sourceEarly := Nat.lt_of_le_of_lt (processUpgrades_fork_le ok) early
  have total := total_active_congr sourceEarly early (ActiveKept.of_validators data _) epoch
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
  have consolidationBalance := congrArg (fun q => q.2.2.2) fields
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
    exitRates, consolidationRates, sites⟩ :=
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

/-- The departure charges of a run, for exit epochs up to `high + 1`, fit a window of epochs.

A charge is a validator's effective balance, counted when its unset exit epoch becomes assigned.

The bound is the carry at `x` plus `H` times the per-epoch caps, where `H = high + 2 - e`.

Here `e` is the current epoch of `x`, so `H` counts the epochs from `e` to `high + 1` inclusively.

From Electra the carry is the unspent capacity of the exit and consolidation queues at `x`.

The carry is unspent queue capacity, not departures that are already assigned.

The caps are `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` and `consolidationCap`.

If `x` is before Electra, the caps add the count-limited cohort cap times `MAX_EFFECTIVE_BALANCE`.

The cohort cap reads `registryBound`, which bounds the size of the registry at `y`.

`consolidationCap` is a hypothesis: it bounds each consolidation churn rate at a call site. -/
theorem departure_charges_le_window {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high registryBound consolidationCap : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (registryBounded : y.state.validators.data.size ≤ registryBound)
    (rates : ∀ site ∈ tail.consolidationSites,
      .pectra ≤ site.fork → ∀ (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate →
          rate.toNat ≤ consolidationCap) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      (if electra : .pectra ≤ x.fork then
        (if (x.state.earliestExitEpoch electra).toNat ≤ high + 1 then
          (x.state.exitBalanceToConsume electra).toNat else 0) +
        (if (x.state.earliestConsolidationEpoch electra).toNat ≤ high + 1 then
          (x.state.consolidationBalanceToConsume electra).toNat else 0)
       else 0) +
      (high + 2 - (getCurrentEpoch x.state).toNat) *
        ((if x.fork < .pectra then max 1 (cohortCap config registryBound) *
          preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
         config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + consolidationCap) := by
  by_cases electra : .pectra ≤ x.fork
  · have bound := departure_charges_le_window_electra tail electra early high
      consolidationCap rates
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    simpa only [electra, ↓reduceDIte, notBefore, ↓reduceIte, Nat.zero_add,
      Nat.add_assoc] using bound
  · have before : x.fork < .pectra := Nat.lt_of_not_ge electra
    simp only [electra, ↓reduceDIte, before, ↓reduceIte, Nat.zero_add]
    by_cases targetBefore : y.fork < .pectra
    · have bound := pre_electra_charges_le_window shared tail genesis caps targetBefore
        (high + 1) registryBound registryBounded
      apply bound.trans
      apply Nat.mul_le_mul_left
      omega
    · obtain ⟨u, v, pre, crossing, post, uBefore, vElectra, same⟩ :=
        split_electra_crossing tail before (Nat.le_of_not_lt targetBefore)
      subst tail
      have vEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
      have legacy := crossing_charges_le_window shared pre crossing genesis caps uBefore
        vEarly (high + 1) registryBound
        ((registryGrows_of_chainSteps post.chainSteps).trans registryBounded)
      have balance := initialized_charges_le_window post vElectra early (high + 1)
        consolidationCap (crossing_initialized crossing uBefore vElectra vEarly)
        (by
          intro site member h rate computed
          apply rates site _ h rate computed
          have appended : ∀ {a b c : ForkedBeaconState preset}
              (one : Run config checks a b) (two : Run config checks b c),
              (one.append two).consolidationSites =
                one.consolidationSites ++ two.consolidationSites := by
            intro a b c one two
            induction two with
            | nil => simp [Run.append, Run.consolidationSites]
            | snoc two step ih =>
              simp only [Run.append, Run.consolidationSites, ih, List.append_assoc]
          rw [appended]
          exact List.mem_append_right _ member)
      -- Convert the endpoint epoch bound to a slot horizon, then carry it back along the run.
      have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
        have slots := parameters.slots
        omega
      have slotMono : ∀ {a b : ForkedBeaconState preset} (run : Run config checks a b),
          a.state.slot.toNat ≤ b.state.slot.toNat := by
        intro a b run
        induction run with
        | nil => exact Nat.le_refl _
        | @snoc middle last head step ih =>
          apply ih.trans
          cases step with
          | slot ok =>
            obtain ⟨advanced, slotOk, upgraded⟩ := bind_ok_iff.mp ok
            rw [processUpgrades_slot upgraded, advanceSlot_slot slotOk]
            exact Nat.le_succ _
          | block engine signed due ok =>
            rw [(frame_processBlock (applySignedBlock_ok ok).2.1).slot]
      have horizon : y.state.slot.toNat <
          (high + 2) * preset.SLOTS_PER_EPOCH.toNat := by
        apply (Nat.div_lt_iff_lt_mul positive).mp
        simpa only [getCurrentEpoch_toNat] using Nat.lt_succ_of_le endEpoch
      have startWindow : (getCurrentEpoch x.state).toNat < high + 2 := by
        rw [getCurrentEpoch_toNat]
        exact (Nat.div_lt_iff_lt_mul positive).mpr
          ((slotMono ((pre.snoc crossing).append post)).trans_lt horizon)
      have ordered := UInt64.le_iff_toNat_le.mp
        (currentEpoch_le_of_chainSteps (pre.snoc crossing).chainSteps)
      have length : high + 2 = (getCurrentEpoch x.state).toNat +
          (high + 2 - (getCurrentEpoch x.state).toNat) := by omega
      have suffix : high + 2 - (getCurrentEpoch v.state).toNat ≤
          high + 2 - (getCurrentEpoch x.state).toNat := by
        conv_lhs => rw [length]
        omega
      have balance := balance.trans (Nat.mul_le_mul_right
        (config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + consolidationCap) suffix)
      have charges : ∀ {a b c : ForkedBeaconState preset}
          (one : Run config checks a b) (two : Run config checks b c),
          (one.append two).departureCharges = one.departureCharges ++ two.departureCharges := by
        intro a b c one two
        induction two with
        | nil => simp [Run.append, Run.departureCharges]
        | snoc two step ih =>
          simp only [Run.append, Run.departureCharges, ih, List.append_assoc]
      rw [charges, List.filter_append, List.map_append, List.sum_append]
      simp only [Nat.add_assoc, Nat.reduceAdd] at legacy balance
      rw [Nat.add_assoc, Nat.mul_add]
      exact Nat.add_le_add legacy balance

end EthLib.Consensus.DirectSafety

