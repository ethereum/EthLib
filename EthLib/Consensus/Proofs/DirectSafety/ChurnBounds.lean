module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Churn
import EthLib.Consensus.Proofs.Transition.Committees

/-!
# Departure charges and the Electra crossing

A departure charge is a validator's effective balance.

It is counted when the validator's unset exit epoch becomes assigned.

Electra exits spend balance churn, and consolidations spend their own queue's churn.

The Electra upgrade starts both queues with the churn of the upgraded state.

The balance queues are specified by [EIP-7251].

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The pre-Electra validator-count churn limit of a registry with `size` entries. -/
def cohortCap (config : Config) (size : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT.toNat (size / config.CHURN_LIMIT_QUOTIENT.toNat)

/-- Variable-rate calls spend at most initial capacity plus the cap per elapsed queue epoch.

The first eligible epoch may also vary; a reset discards rather than preserves old capacity. -/
theorem churnQueue_window_le (cap : Nat) :
    ∀ (calls : List (UInt64 × UInt64 × UInt64)) (earliest available epoch left : UInt64),
      (∀ call ∈ calls, call.2.1.toNat ≤ cap) →
      calls.foldlM (fun (queue : UInt64 × UInt64) call =>
        churnQueue queue.1 call.1 call.2.1 queue.2 call.2.2) (earliest, available) =
          .ok (epoch, left) →
      earliest.toNat ≤ epoch.toNat ∧
        left.toNat + (calls.map fun c => c.2.2.toNat).sum ≤
          available.toNat + (epoch.toNat - earliest.toNat) * cap := by
  intro calls
  induction calls with
  | nil =>
    intro earliest available epoch left _ computed
    cases Except.ok.inj computed
    simp
  | cons call rest ih =>
    intro earliest available epoch left rates computed
    simp only [List.foldlM_cons, Base.bind_ok_iff] at computed
    obtain ⟨⟨middle, remaining⟩, queued, restOk⟩ := computed
    obtain ⟨placed, spent, _⟩ := churnQueue_spend queued
    have rate := rates call (by simp)
    have later := UInt64.le_iff_toNat_le.mp placed
    rw [Base.Uint64.toNat_max] at later
    have firstLe : earliest.toNat ≤ middle.toNat := Nat.le_trans (Nat.le_max_left _ _) later
    obtain ⟨lastLe, tailBound⟩ := ih middle remaining epoch left
      (fun c hc => rates c (List.mem_cons_of_mem _ hc)) restOk
    have oneBound : remaining.toNat + call.2.2.toNat ≤
        available.toNat + (middle.toNat - earliest.toNat) * cap := by
      split at spent
      · rename_i reset
        have reset := UInt64.lt_iff_toNat_lt.mp reset
        rw [Base.Uint64.toNat_max] at reset
        have distance : middle.toNat - max earliest.toNat call.1.toNat + 1 ≤
            middle.toNat - earliest.toNat := by omega
        rw [Base.Uint64.toNat_max] at spent
        have product := Nat.mul_le_mul distance rate
        rw [Nat.add_mul, Nat.one_mul] at product
        omega
      · rw [Base.Uint64.toNat_max] at spent
        have distance : middle.toNat - max earliest.toNat call.1.toNat ≤
            middle.toNat - earliest.toNat := by omega
        have product := Nat.mul_le_mul distance rate
        omega
    refine ⟨Nat.le_trans firstLe lastLe, ?_⟩
    have distance : epoch.toNat - earliest.toNat =
        (epoch.toNat - middle.toNat) + (middle.toNat - earliest.toNat) := by omega
    simp only [List.map_cons, List.sum_cons]
    rw [distance, Nat.add_mul]
    omega

/-- The charge visible when a selected transition assigns a previously unset exit epoch. -/
structure DepartureCharge where
  index : Nat
  epoch : Nat
  amount : Nat

/-- Effective balances are read before scheduling, not after the later effective-balance pass. -/
def _root_.EthLib.Consensus.Step.departureCharges {x y : ForkedBeaconState preset}
    (_step : Step config checks x y) : List DepartureCharge :=
  x.state.validators.data.toList.zipIdx.filterMap fun (v, i) =>
    match y.state.validators.data[i]? with
    | none => none
    | some next => if v.exitEpoch == FAR_FUTURE_EPOCH && next.exitEpoch != FAR_FUTURE_EPOCH then
        some ⟨i, next.exitEpoch.toNat, v.effectiveBalance.toNat⟩
      else none

/-- The departure charges of a run, step by step in order. -/
def _root_.EthLib.Consensus.Run.departureCharges {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → List DepartureCharge
  | _, .nil => []
  | _, .snoc pre step => pre.departureCharges ++ step.departureCharges


/-- Every recorded charge names an exit that remains assigned at the interval endpoint. -/
theorem _root_.EthLib.Consensus.Run.departure_charge_exit
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (charge : DepartureCharge) (member : charge ∈ tail.departureCharges) :
    ∃ v, y.state.validators.data[charge.index]? = some v ∧
      v.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ v.exitEpoch.toNat = charge.epoch := by
  induction tail with
  | nil => simp [Run.departureCharges] at member
  | snoc pre step ih =>
    rcases List.mem_append.mp member with earlier | latest
    · obtain ⟨v, found, assigned, epoch⟩ := ih earlier
      obtain ⟨w, foundLater, kept⟩ :=
        (RegistryLifecycle.chainStep step.chainStep).validators charge.index v found
      exact ⟨w, foundLater, by simpa [kept.exitEpoch assigned] using assigned,
        by simpa [kept.exitEpoch assigned] using epoch⟩
    · obtain ⟨⟨old, i⟩, _, added⟩ := List.mem_filterMap.mp latest
      dsimp only at added
      split at added
      · cases added
      · rename_i v found
        split at added
        · rename_i assigned
          cases Option.some.inj added
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at assigned
          exact ⟨v, found, assigned.2, rfl⟩
        · cases added

/-- An exit already assigned at the reference state is never charged again. -/
theorem _root_.EthLib.Consensus.Run.departure_charge_ne_of_assigned
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (charge : DepartureCharge) (member : charge ∈ tail.departureCharges) :
    charge.index ≠ i := by
  induction tail with
  | nil => simp [Run.departureCharges] at member
  | snoc pre step ih =>
    rcases List.mem_append.mp member with earlier | latest
    · exact ih earlier
    · obtain ⟨w, foundLater, kept⟩ := pre.registryLifecycle.validators i v found
      obtain ⟨⟨old, index⟩, present, added⟩ := List.mem_filterMap.mp latest
      dsimp only at added
      split at added
      · cases added
      · split at added
        · rename_i pending
          cases Option.some.inj added
          intro equal
          change index = i at equal
          subst index
          have oldFound : _ = some old :=
            (List.mem_zipIdx_iff_getElem?.mp present)
          rw [Array.getElem?_toList] at oldFound
          have same : old = w := Option.some.inj (oldFound.symm.trans foundLater)
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at pending
          exact assigned ((kept.exitEpoch assigned).symm.trans (same ▸ pending.1))
        · cases added

/-- Queueing deposits keeps the queue fields and the effective balances of activated validators. -/
private structure ElectraQueuesKept (a b : BeaconState preset .pectra) : Prop where
  slot : b.slot = a.slot
  exitEpoch : b.earliestExitEpoch = a.earliestExitEpoch
  exitCapacity : b.exitBalanceToConsume = a.exitBalanceToConsume
  consolidationCapacity : b.consolidationBalanceToConsume = a.consolidationBalanceToConsume
  size : b.validators.data.size = a.validators.data.size
  validators : ∀ (i : Nat) (v : Validator), a.validators.data[i]? = some v →
    ∃ w : Validator, b.validators.data[i]? = some w ∧
      w.activationEpoch = v.activationEpoch ∧ w.exitEpoch = v.exitEpoch ∧
      (v.activationEpoch ≠ FAR_FUTURE_EPOCH → w.effectiveBalance = v.effectiveBalance)

private theorem ElectraQueuesKept.refl (a : BeaconState preset .pectra) :
    ElectraQueuesKept a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ v found => ⟨v, found, rfl, rfl, fun _ => rfl⟩⟩

private theorem ElectraQueuesKept.trans {a b c : BeaconState preset .pectra}
    (ab : ElectraQueuesKept a b) (bc : ElectraQueuesKept b c) : ElectraQueuesKept a c := by
  refine ⟨bc.slot.trans ab.slot, bc.exitEpoch.trans ab.exitEpoch,
    bc.exitCapacity.trans ab.exitCapacity,
    bc.consolidationCapacity.trans ab.consolidationCapacity, bc.size.trans ab.size, ?_⟩
  intro i v found
  obtain ⟨w, hw, ha, he, hb⟩ := ab.validators i v found
  obtain ⟨z, hz, hza, hze, hzb⟩ := bc.validators i w hw
  exact ⟨z, hz, hza.trans ha, hze.trans he,
    fun assigned => (hzb (ha ▸ assigned)).trans (hb assigned)⟩

private theorem queues_preActivation {a b : BeaconState preset .pectra}
    {index : ValidatorIndex}
    (pending : ∀ v, a.validators.data[index.toNat]? = some v →
      v.activationEpoch = FAR_FUTURE_EPOCH)
    (ok : queuePreActivation a (by decide) index = .ok b) : ElectraQueuesKept a b := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, balance, _, validator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok balance
  obtain ⟨inside, rfl⟩ := setValidator_ok validator
  have read : a.validators.data[index.toNat]? = some v := by
    unfold getValidator at found
    split at found <;> simp_all
  refine ⟨rfl, rfl, rfl, rfl, by simp [BeaconState.putValidator, BeaconState.putBalance], ?_⟩
  intro i old oldFound
  simp only [BeaconState.putValidator, BeaconState.putBalance,
    Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set]
  split
  · rename_i equal
    subst i
    have same := Option.some.inj (oldFound.symm.trans read)
    subst old
    exact ⟨{ v with effectiveBalance := 0, activationEligibilityEpoch := FAR_FUTURE_EPOCH },
      rfl, rfl, rfl, fun assigned => False.elim (assigned (pending v read))⟩
  · exact ⟨old, oldFound, rfl, rfl, fun _ => rfl⟩

private theorem queues_compounding {a b : BeaconState preset .pectra} {index : Nat}
    (ok : queueCompoundingExcess a (by decide) index = .ok b) : ElectraQueuesKept a b := by
  unfold queueCompoundingExcess at ok
  split at ok
  · split at ok
    · have queued := liftAccessor_ok.mp ok
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok set
        exact ⟨rfl, rfl, rfl, rfl, rfl,
          fun _ v found => ⟨v, found, rfl, rfl, fun _ => rfl⟩⟩
      · cases queued
        exact .refl _
    · cases ok
      exact .refl _
  · cases ok
    exact .refl _

private theorem queues_preActivation_fold (a b : BeaconState preset .pectra)
    (ok : (preActivationIndices a).foldlM
      (fun s i => queuePreActivation s (by decide) i) a = .ok b) :
    ElectraQueuesKept a b := by
  have pending : ∀ index ∈ preActivationIndices a, ∃ v,
      a.validators.data[index.toNat]? = some v ∧ v.activationEpoch = FAR_FUTURE_EPOCH := by
    -- Sorting changes the order, but every selected position still has an unset activation.
    intro index member
    obtain ⟨⟨v, i⟩, sorted, rfl⟩ := List.mem_map.mp member
    rw [List.mem_mergeSort] at sorted
    obtain ⟨member, waiting⟩ := List.mem_filter.mp sorted
    have found : a.validators.data[i]? = some v := by
      simpa using List.mem_zipIdx_iff_getElem?.mp member
    have small := toNat_toUInt64_of_lt (state := a) (a.validators.bound (by decide))
      (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨v, by simpa [small] using found, by simpa using waiting⟩
  generalize hs : preActivationIndices a = xs at ok
  rw [hs] at pending
  have run : ∀ (xs : List ValidatorIndex) (s t : BeaconState preset .pectra),
      (∀ index ∈ xs, ∃ v, a.validators.data[index.toNat]? = some v ∧
        v.activationEpoch = FAR_FUTURE_EPOCH) → ElectraQueuesKept a s →
      xs.foldlM (fun s i => queuePreActivation s (by decide) i) s = .ok t →
      ElectraQueuesKept a t := by
    intro xs
    induction xs with
    | nil => intro s t _ kept ok; cases ok; exact kept
    | cons i rest ih =>
      intro s t pending kept ok
      obtain ⟨m, step, tail⟩ := bind_ok_iff.mp ok
      have queued := queues_preActivation (a := s) (b := m) (index := i) (by
        intro v found
        obtain ⟨old, oldFound, waiting⟩ := pending i (by simp)
        obtain ⟨w, hw, ha, _, _⟩ := kept.validators i.toNat old oldFound
        have same := Option.some.inj (found.symm.trans hw)
        exact same ▸ ha.trans waiting) step
      exact ih m t (fun i hi => pending i (List.mem_cons_of_mem _ hi))
        (kept.trans queued) tail
  exact run xs a b pending (.refl a) ok

private theorem ElectraQueuesKept.active {a b : BeaconState preset .pectra}
    (kept : ElectraQueuesKept a b) (bound : Epoch) : ActiveKept bound a b := by
  intro epoch _ i
  cases found : a.validators.data[i]? with
  | none =>
    have outside := Array.getElem?_eq_none_iff.mp found
    simp [isActiveAt, found, Array.getElem?_eq_none (kept.size ▸ outside)]
  | some v =>
    obtain ⟨w, hw, ha, he, _⟩ := kept.validators i v found
    simp [isActiveAt, found, hw, isActiveValidator, ha, he]

private theorem ElectraQueuesKept.total {a b : BeaconState preset .pectra}
    (kept : ElectraQueuesKept a b) : getTotalActiveBalance b = getTotalActiveBalance a := by
  have epoch : getCurrentEpoch b = getCurrentEpoch a := by
    simp only [getCurrentEpoch, kept.slot]
  have active := kept.active (getCurrentEpoch a)
  have checked := active.getActiveValidatorIndicesChecked_eq (UInt64.le_refl _)
  have sum : sumMarked b.validators.data
      (markIndices b.validators.data.size (getActiveValidatorIndices a (getCurrentEpoch a))) =
      sumMarked a.validators.data
      (markIndices a.validators.data.size (getActiveValidatorIndices a (getCurrentEpoch a))) := by
    rw [sumMarked_eq_sum, sumMarked_eq_sum, kept.size]
    congr 1
    apply List.map_congr_left
    intro i member
    by_cases marked : (markIndices a.validators.data.size
        (getActiveValidatorIndices a (getCurrentEpoch a)))[i]?.getD false = true
    · have inside := List.mem_range.mp member
      rw [getElem?_markIndices, ite_eq_left inside, Option.getD_some,
        List.any_eq_true] at marked
      obtain ⟨index, listed, equal⟩ := marked
      have isActive := (mem_getActiveValidatorIndices (state := a)
        (a.validators.bound (by decide))).mp listed
      rw [beq_iff_eq.mp equal] at isActive
      obtain ⟨v, found, act⟩ := isActive
      obtain ⟨w, hw, _, _, hb⟩ := kept.validators i v found
      -- An active validator cannot have the largest epoch as its activation epoch.
      have assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
        intro equal
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at act
        have := v.exitEpoch.toNat_lt
        simp [equal, FAR_FUTURE_EPOCH] at act
        omega
      simp [found, hw, hb assigned]
    · simp [marked]
  unfold getTotalActiveBalance
  rw [epoch, checked, getActiveValidatorIndicesChecked_of_within (state := a)
    (a.validators.bound (by decide))]
  simp only [bind, Except.bind]
  rw [kept.size] at sum
  simp only [getTotalBalance, kept.size, sum]

/-- A reachable Electra upgrade starts the exit queue after all previously scheduled exits. -/
theorem electra_crossing_queues {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (ok : upgradeToElectra config pre = .ok post) :
    getCurrentEpoch post = getCurrentEpoch pre ∧
    (∀ (i : Nat) (v : Validator), pre.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch < post.earliestExitEpoch (by decide)) ∧
    exitChurnLimit config post = .ok (post.exitBalanceToConsume (by decide)) ∧
    getConsolidationChurnLimit config post =
      .ok (post.consolidationBalanceToConsume (by decide)) := by
  simp only [upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨activation, activationOk, earliest, earliestOk, exitRate, exitOk,
    consolidationRate, consolidationOk, middle, queued, compounded⟩ := ok
  -- Both folds preserve the initialized queues and the active balance used to fill them.
  have first := queues_preActivation_fold _ _ queued
  have kept := foldlM_ok_invariant (ElectraQueuesKept _)
    (fun _ _ _ before step => before.trans (queues_compounding step)) first compounded
  refine ⟨by simpa only [getCurrentEpoch, carryFields] using
      congrArg (computeEpochAtSlot preset) kept.slot,
    ?_, ?_, ?_⟩
  · intro i v found assigned
    rw [kept.exitEpoch]
    have latest : ∀ (vs : List Validator) (start : UInt64),
        start ≤ vs.foldl (fun latest validator =>
          if validator.exitEpoch = FAR_FUTURE_EPOCH then latest
          else max latest validator.exitEpoch) start ∧
        ∀ w ∈ vs, w.exitEpoch ≠ FAR_FUTURE_EPOCH →
          w.exitEpoch ≤ vs.foldl (fun latest validator =>
            if validator.exitEpoch = FAR_FUTURE_EPOCH then latest
            else max latest validator.exitEpoch) start := by
      intro vs
      induction vs with
      | nil => intro start; exact ⟨UInt64.le_refl _, by simp⟩
      | cons w rest ih =>
        intro start
        obtain ⟨monotone, members⟩ := ih
          (if w.exitEpoch = FAR_FUTURE_EPOCH then start else max start w.exitEpoch)
        have startLe : start ≤
            (if w.exitEpoch = FAR_FUTURE_EPOCH then start else max start w.exitEpoch) := by
          split
          · exact UInt64.le_refl _
          · rw [UInt64.le_iff_toNat_le, Uint64.toNat_max]
            exact Nat.le_max_left _ _
        refine ⟨UInt64.le_trans startLe monotone, ?_⟩
        intro u member set
        rcases List.mem_cons.mp member with rfl | member
        · apply UInt64.le_trans _ monotone
          rw [ite_eq_right set, UInt64.le_iff_toNat_le, Uint64.toNat_max]
          exact Nat.le_max_right _ _
        · exact members u member set
    have bound := (latest pre.validators.data.toList activation).2 v
      (by simpa using Array.mem_of_getElem? found) assigned
    have addition := Uint64.addChecked_ok_iff.mp
      (mapError_ok_iff.mp (liftAccessor_ok.mp earliestOk))
    rw [← Array.foldl_toList] at addition
    change v.exitEpoch < earliest
    rw [UInt64.lt_iff_toNat_lt]
    have := UInt64.le_iff_toNat_le.mp bound
    simp only [UInt64.reduceToNat] at addition
    exact Nat.lt_of_le_of_lt this (by rw [addition.2]; exact Nat.lt_succ_self _)
  · have same := kept.total
    rw [kept.exitCapacity]
    change getActivationExitChurnLimit config post = .ok exitRate
    unfold getActivationExitChurnLimit getBalanceChurnLimit
    rw [same]
    exact liftAccessor_ok.mp exitOk
  · have same := kept.total
    rw [kept.consolidationCapacity]
    change getConsolidationChurnLimit config post = .ok consolidationRate
    unfold getConsolidationChurnLimit getActivationExitChurnLimit getBalanceChurnLimit
    rw [same]
    exact liftAccessor_ok.mp consolidationOk

/-- The entire crossing step includes its preceding epoch and any simultaneous upgrades. -/
theorem split_electra_crossing {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : x.fork < .pectra) (late : .pectra ≤ y.fork) :
    ∃ u v, ∃ head : Run config checks x u, ∃ step : Step config checks u v,
      ∃ rest : Run config checks v y,
        u.fork < .pectra ∧ .pectra ≤ v.fork ∧ (head.snoc step).append rest = tail := by
  induction tail with
  | nil => exact False.elim (Nat.not_lt_of_ge late early)
  | @snoc middle last pre step ih =>
    by_cases crossed : .pectra ≤ middle.fork
    · obtain ⟨u, v, head, crossing, rest, before, after, same⟩ := ih crossed
      exact ⟨u, v, head, crossing, rest.snoc step, before, after,
        congrArg (fun run => run.snoc step) same⟩
    · exact ⟨middle, last, pre, step, .nil, Nat.lt_of_not_ge crossed, late, rfl⟩

end EthLib.Consensus.DirectSafety
