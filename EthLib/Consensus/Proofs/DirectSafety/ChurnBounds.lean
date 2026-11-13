module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Churn
public import EthLib.Consensus.Proofs.DirectSafety.Drift
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.Cohorts
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import Mathlib.Order.Interval.Finset.Nat

/-!
# Departure charges and the Electra crossing

A departure charge is a validator's effective balance.

It is counted when the validator's unset exit epoch becomes assigned.

Electra exits spend balance churn, and consolidations spend their own queue's churn.

The Electra upgrade starts both queues with the churn of the upgraded state.

Before Electra, the validator-count churn bounds the stake that leaves or joins a window.

The boundary support is the unslashed cohort that exits at the current epoch.

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


/-- An existing validator whose exit becomes assigned has a charge at that exit epoch. -/
private theorem _root_.EthLib.Consensus.Run.departure_charge_of_assigned
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (i : Nat) (old current : Validator)
    (before : x.state.validators.data[i]? = some old)
    (after : y.state.validators.data[i]? = some current)
    (unset : old.exitEpoch = FAR_FUTURE_EPOCH)
    (assigned : current.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ charge ∈ tail.departureCharges,
      charge.index = i ∧ charge.epoch = current.exitEpoch.toNat := by
  induction tail generalizing current with
  | nil =>
    have same : old = current := Option.some.inj (before.symm.trans after)
    exact False.elim (assigned (same ▸ unset))
  | snoc pre step ih =>
    obtain ⟨middle, found, _⟩ := pre.registryLifecycle.validators i old before
    by_cases pending : middle.exitEpoch = FAR_FUTURE_EPOCH
    · refine ⟨⟨i, current.exitEpoch.toNat, middle.effectiveBalance.toNat⟩,
        List.mem_append_right _ ?_, rfl, rfl⟩
      apply List.mem_filterMap.mpr
      refine ⟨(middle, i), ?_, ?_⟩
      · simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using found
      · simp [after, pending, assigned]
    · obtain ⟨charge, member, index, epoch⟩ := ih middle found pending
      obtain ⟨last, lastFound, kept⟩ :=
        (RegistryLifecycle.chainStep step.chainStep).validators i middle found
      have same : last = current := Option.some.inj (lastFound.symm.trans after)
      refine ⟨charge, List.mem_append_left _ member, index, ?_⟩
      rw [epoch, ← kept.exitEpoch pending, same]

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

/-- Every assigned exit of a validator present at the start was inherited or charged. -/
private theorem _root_.EthLib.Consensus.Run.departure_origin
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (i : Nat) (inside : i < x.state.validators.data.size)
    (v : Validator) (found : y.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    (∃ old, x.state.validators.data[i]? = some old ∧ old.exitEpoch = v.exitEpoch) ∨
      ∃ charge ∈ tail.departureCharges, charge.index = i ∧ charge.epoch = v.exitEpoch.toNat := by
  induction tail generalizing v with
  | nil => exact Or.inl ⟨v, found, rfl⟩
  | @snoc middle last pre step ih =>
    -- The registry never shrinks, so the validator is present before the last step too.
    have present : i < middle.state.validators.data.size :=
      Nat.lt_of_lt_of_le inside pre.registryLifecycle.size_le
    let old := middle.state.validators.data[i]
    have oldFound : middle.state.validators.data[i]? = some old := by simp [old, present]
    by_cases pending : old.exitEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨charge, member, index, epoch⟩ :=
        (Run.nil.snoc step).departure_charge_of_assigned i old v oldFound found pending assigned
      exact Or.inr ⟨charge, List.mem_append_right _ member, index, epoch⟩
    · obtain ⟨w, current, kept⟩ :=
        (RegistryLifecycle.chainStep step.chainStep).validators i old oldFound
      have same : w = v := Option.some.inj (current.symm.trans found)
      have exit : v.exitEpoch = old.exitEpoch := same ▸ kept.exitEpoch pending
      rcases ih old oldFound pending with inherited | charged
      · obtain ⟨initial, initialFound, epoch⟩ := inherited
        exact Or.inl ⟨initial, initialFound, epoch.trans exit.symm⟩
      · obtain ⟨charge, member, index, epoch⟩ := charged
        exact Or.inr ⟨charge, List.mem_append_left _ member, index, by simpa [exit] using epoch⟩

/-- The baseline lookup either selects this exit's charge or falls back to an inherited exit.

The validator must be present at the start of the run. -/
theorem _root_.EthLib.Consensus.Run.departure_baseline
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (i : Nat) (inside : i < x.state.validators.data.size) (v : Validator)
    (found : y.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    match tail.departureCharges.find? (fun c => c.index == i) with
    | some charge => charge.index = i ∧ charge.epoch = v.exitEpoch.toNat
    | none => ∃ old, x.state.validators.data[i]? = some old ∧ old.exitEpoch = v.exitEpoch := by
  cases selected : tail.departureCharges.find? (fun c => c.index == i) with
  | some charge =>
    have index : charge.index = i := by simpa using List.find?_some selected
    obtain ⟨w, present, _, epoch⟩ :=
      tail.departure_charge_exit charge (List.mem_of_find?_eq_some selected)
    rw [index] at present
    have same : w = v := Option.some.inj (present.symm.trans found)
    exact ⟨index, by simpa [same] using epoch.symm⟩
  | none =>
    rcases tail.departure_origin i inside v found assigned with inherited | charged
    · exact inherited
    · obtain ⟨charge, member, index, _⟩ := charged
      exact False.elim ((List.find?_eq_none.mp selected charge member) (by simp [index]))

/-! ## The boundary and the joining stake before Electra -/

/-- Reference weights of the one inherited cohort, including the initial boundary. -/
def inheritedCohort (x : ForkedBeaconState preset) (epoch : Nat) : Nat :=
  (x.state.validators.data.toList.filter fun v =>
    v.activationEpoch.toNat < epoch && v.exitEpoch.toNat == epoch).foldl
      (fun n v => n + v.effectiveBalance.toNat) 0

/-- Previous-only voting support consists exactly of the cohort exiting at the current epoch. -/
theorem previous_only_iff_exit {fork : Fork} (state : BeaconState preset fork) (v : Validator) :
    (isActiveValidator v (getPreviousEpoch state) = true ∧
      isActiveValidator v (getCurrentEpoch state) = false) ↔
    v.activationEpoch.toNat < (getCurrentEpoch state).toNat ∧
      v.exitEpoch.toNat = (getCurrentEpoch state).toNat := by
  simp only [isActiveValidator, Bool.and_eq_true, Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat]
  omega

private theorem run_unique {g x : ForkedBeaconState preset} (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) : PubkeysDistinct x.state := by
  have ⟨_, _, _, initialized⟩ := genesis
  exact (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized run.chainSteps).2

private theorem key_preserved {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (i : Nat) (old : Validator) (found : x.state.validators.data[i]? = some old) :
    ∃ current, y.state.validators.data[i]? = some current ∧ current.pubkey = old.pubkey :=
  validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 found

/-- A key slashed at the start of a run is slashed at its end: slashing persists forward. -/
private theorem slashedAt_forward {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {key : Cryptography.Bls.BLSPubkey}
    (slashed : SlashedAt x.state key) : SlashedAt y.state key := by
  obtain ⟨v, member, keyEq, flag⟩ := slashed
  obtain ⟨i, found⟩ := Array.getElem?_of_mem (by simpa using member)
  obtain ⟨w, wFound, wFlag⟩ := tail.slashedPersistence i v found flag
  obtain ⟨u, uFound, uKey⟩ := key_preserved tail i v found
  have same : u = w := Option.some.inj (uFound.symm.trans wFound)
  exact ⟨w, by simpa using Array.mem_of_getElem? wFound, same ▸ uKey.trans keyEq, wFlag⟩

private theorem mem_keysAt_epoch {fork : Fork} {state : BeaconState preset fork}
    (early : fork < .glamsterdam) (epoch : Epoch) (key : Cryptography.Bls.BLSPubkey) :
    key ∈ keysAt state (getActiveValidatorIndices state epoch) ↔
      ∃ (i : Nat) (v : Validator), state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        isActiveValidator v epoch = true := by
  have within := state.validators.bound early
  simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨index, active, read⟩
    obtain ⟨v, found, active⟩ := (mem_getActiveValidatorIndices within).mp active
    exact ⟨index.toNat, v, found, by simpa [found] using read, active⟩
  · rintro ⟨i, v, found, same, active⟩
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have numeric := toNat_toUInt64_of_lt within inside
    refine ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr
      ⟨v, by simpa [numeric] using found, active⟩, ?_⟩
    simp [numeric, found, same]

private theorem effectiveWeight_of_member {fork : Fork} {state : BeaconState preset fork}
    (unique : PubkeysDistinct state) {v : Validator} (member : v ∈ state.validators.data.toList) :
    effectiveWeight state v.pubkey = v.effectiveBalance.toNat := by
  have lookup (vs : List Validator) (distinct : (vs.map (·.pubkey)).Nodup)
      (v : Validator) (member : v ∈ vs) :
      vs.find? (fun w => w.pubkey == v.pubkey) = some v := by
    induction vs with
    | nil => simp at member
    | cons w ws ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : w.pubkey ≠ v.pubkey := by
          intro same
          exact distinct.1 (List.mem_map.mpr ⟨v, member, same.symm⟩)
        simp [different, ih distinct.2 member]
  simp [effectiveWeight, lookup _ unique v member]

/-- Distinct registry keys identify the boundary support with this epoch's exiting cohort.

The boundary support is unslashed, so the exiting validator is unslashed too. -/
private theorem mem_boundary_iff {fork : Fork} (state : BeaconState preset fork)
    (early : fork < .glamsterdam) (unique : PubkeysDistinct state)
    (key : Cryptography.Bls.BLSPubkey) :
    key ∈ recentKeys state \ activeKeys state ↔
      (∃ (i : Nat) (v : Validator), state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch.toNat < (getCurrentEpoch state).toNat ∧
        v.exitEpoch.toNat = (getCurrentEpoch state).toNat) ∧ ¬ SlashedAt state key := by
  classical
  have sameValidator {i j : Nat} {v w : Validator}
      (one : state.validators.data[i]? = some v)
      (two : state.validators.data[j]? = some w)
      (keys : v.pubkey = w.pubkey) : v = w := by
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp one
    obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp two
    have same : i = j := unique.eq_of_getElem_eq
      (by simpa [validatorKeys] using hi) (by simpa [validatorKeys] using hj)
      (by simpa [validatorKeys] using keys)
    subst j
    rfl
  have member := mem_keysAt_epoch (state := state) early
  simp only [Finset.mem_sdiff, recentKeys, Finset.mem_filter, Finset.mem_union, activeKeys]
  constructor
  · rintro ⟨⟨current | previous, unslashed⟩, absent⟩
    · exact False.elim (absent current)
    · obtain ⟨i, v, found, same, active⟩ := (member _ key).mp previous
      have inactive : isActiveValidator v (getCurrentEpoch state) = false := by
        cases h : isActiveValidator v (getCurrentEpoch state) with
        | false => rfl
        | true => exact False.elim (absent ((member _ key).mpr ⟨i, v, found, same, h⟩))
      exact ⟨⟨i, v, found, same, (previous_only_iff_exit state v).mp ⟨active, inactive⟩⟩,
        unslashed⟩
  · rintro ⟨⟨i, v, found, same, cohort⟩, unslashed⟩
    obtain ⟨previous, inactive⟩ := (previous_only_iff_exit state v).mpr cohort
    refine ⟨⟨Or.inr ((member _ key).mpr ⟨i, v, found, same, previous⟩), unslashed⟩, ?_⟩
    intro active
    obtain ⟨j, w, other, keySame, active⟩ := (member _ key).mp active
    have equal := sameValidator found other (same.trans keySame.symm)
    rw [← equal, inactive] at active
    cases active

/-- Boundary weight is at most the effective stake of the cohort exiting at this epoch.

The boundary support is unslashed, so slashed members of the cohort are not counted. -/
theorem boundaryStake_le_cohort (y : ForkedBeaconState preset)
    (early : y.fork < .glamsterdam) (unique : PubkeysDistinct y.state) :
    boundaryStake y ≤ inheritedCohort y (getCurrentEpoch y.state).toNat := by
  classical
  let cohort := y.state.validators.data.toList.filter fun v =>
    v.activationEpoch.toNat < (getCurrentEpoch y.state).toNat &&
      v.exitEpoch.toNat == (getCurrentEpoch y.state).toNat
  have selected : recentKeys y.state \ activeKeys y.state ⊆
      (cohort.map (·.pubkey)).toFinset := by
    intro key member
    obtain ⟨⟨i, v, found, same, active, exited⟩, _⟩ :=
      (mem_boundary_iff y.state early unique key).mp member
    simp only [cohort, List.mem_toFinset, List.mem_map, List.mem_filter,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨v, ⟨by simpa using Array.mem_of_getElem? found, active, exited⟩, same⟩
  have distinct : (cohort.map (·.pubkey)).Nodup :=
    unique.sublist ((List.filter_sublist).map _)
  have weights : (cohort.map fun v => effectiveWeight y.state v.pubkey).sum =
      (cohort.map fun v => v.effectiveBalance.toNat).sum := by
    congr 1
    apply List.map_congr_left
    intro v member
    exact effectiveWeight_of_member unique (List.mem_filter.mp member).1
  unfold boundaryStake Models.stake
  refine (Finset.sum_le_sum_of_subset_of_nonneg selected (fun _ _ _ => Nat.zero_le _)).trans ?_
  rw [List.sum_toFinset _ distinct, List.map_map]
  change (cohort.map fun v => effectiveWeight y.state v.pubkey).sum ≤ _
  rw [weights, List.sum_eq_foldl, List.foldl_map]
  exact Nat.le_refl _

private theorem effectiveWeight_le_cap {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (early : x.fork < .pectra) (key : Cryptography.Bls.BLSPubkey) :
    effectiveWeight x.state key ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
  have capped := run.effectiveBalance_capped genesis caps.activation caps.compounding
    (Nat.lt_trans early (by decide))
  unfold effectiveWeight
  cases found : x.state.validators.data.toList.find? (fun v => v.pubkey == key) with
  | none => simp
  | some v =>
    have member := List.mem_of_find?_eq_some found
    have bound := capped v (by simpa using member)
    have noElectra : ¬ Fork.pectra ≤ x.fork := Nat.not_le_of_lt early
    simpa [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, noElectra] using
      (UInt64.le_iff_toNat_le.mp bound)

private theorem count_epoch_window (vs : List Validator) (field : Validator → Epoch)
    (lo hi cap : Nat)
    (bounded : ∀ n ∈ Finset.Ioc lo hi, vs.countP (fun v => (field v).toNat == n) ≤ cap) :
    (vs.filter fun v => lo < (field v).toNat && (field v).toNat ≤ hi).length ≤ (hi - lo) * cap := by
  classical
  have partition : ∀ xs : List Validator,
      (xs.filter fun v => lo < (field v).toNat && (field v).toNat ≤ hi).length =
        ∑ n ∈ Finset.Ioc lo hi, xs.countP (fun v => (field v).toNat == n) := by
    intro xs
    induction xs with
    | nil => simp
    | cons v xs ih =>
      simp only [List.countP_cons, Finset.sum_add_distrib]
      have singleton : (∑ n ∈ Finset.Ioc lo hi, if (field v).toNat == n then 1 else 0) =
          if lo < (field v).toNat ∧ (field v).toNat ≤ hi then 1 else 0 := by
        by_cases member : (field v).toNat ∈ Finset.Ioc lo hi
        · rw [Finset.sum_eq_single (field v).toNat]
          · simp [Finset.mem_Ioc.mp member]
          · intro n _ different
            simp [Ne.symm different]
          · exact fun absent => False.elim (absent member)
        · rw [Finset.sum_eq_zero (fun n inside => by
            have different : (field v).toNat ≠ n := fun same => member (same ▸ inside)
            simp [different])]
          simp only [Finset.mem_Ioc] at member
          simp [member]
      rw [singleton]
      by_cases inside : lo < (field v).toNat ∧ (field v).toNat ≤ hi
      · simp [inside.1, inside.2, ih, Nat.add_comm]
      · have no : ¬ (lo < (field v).toNat && (field v).toNat ≤ hi) := by simpa using inside
        simp [no, ih, inside]
  rw [partition]
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc lo hi, cap := Finset.sum_le_sum bounded
    _ = (hi - lo) * cap := by simp

private theorem new_recent_key_activation {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .pectra)
    {key : Cryptography.Bls.BLSPubkey} (member : key ∈ recentKeys y.state \ recentKeys x.state) :
    ∃ v ∈ y.state.validators.data.toList, v.pubkey = key ∧
      (getCurrentEpoch x.state).toNat < v.activationEpoch.toNat ∧
      v.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat := by
  classical
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨recent, absent⟩ := Finset.mem_sdiff.mp member
  obtain ⟨recent, unslashed⟩ := Finset.mem_filter.mp recent
  -- A key slashed at the reference would still be slashed now, so it is unslashed there too.
  have unslashedX : ¬ SlashedAt x.state key := fun slashed =>
    unslashed (slashedAt_forward tail slashed)
  have witness : ∃ (i : Nat) (w : Validator), y.state.validators.data[i]? = some w ∧
      w.pubkey = key ∧ (isActiveValidator w (getCurrentEpoch y.state) = true ∨
        isActiveValidator w (getPreviousEpoch y.state) = true) := by
    rcases Finset.mem_union.mp recent with h | h
    · obtain ⟨i, w, found, same, active⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact ⟨i, w, found, same, Or.inl active⟩
    · obtain ⟨i, w, found, same, active⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact ⟨i, w, found, same, Or.inr active⟩
  obtain ⟨i, v, found, keyEq, active⟩ := witness
  have inactive (e : Epoch) (le : e ≤ getCurrentEpoch x.state)
      (selected : e = getCurrentEpoch x.state ∨ e = getPreviousEpoch x.state) :
      ¬ isActiveValidator v e = true := by
    intro h
    have kept := activeKept_of_chainSteps tail.chainSteps e
      (UInt64.le_trans le (getCurrentEpoch_le_activityFixedEpoch _)) i
    have oldActive : isActiveAt x.state e i = true := by
      rw [← kept]
      simp [isActiveAt, found, h]
    obtain ⟨old, oldFound, oldActive⟩ := isActiveAt_eq_true_iff.mp oldActive
    obtain ⟨later, laterFound, same⟩ := key_preserved tail i old oldFound
    have equal : later = v := Option.some.inj (laterFound.symm.trans found)
    have member := (mem_keysAt_epoch (Nat.lt_trans xEarly (by decide)) e key).mpr
      ⟨i, old, oldFound, same.symm.trans (equal ▸ keyEq), oldActive⟩
    apply absent
    refine Finset.mem_filter.mpr ⟨?_, unslashedX⟩
    rcases selected with rfl | rfl
    · exact Finset.mem_union_left _ member
    · exact Finset.mem_union_right _ member
  have now := inactive _ (UInt64.le_refl _) (Or.inl rfl)
  have prev := inactive _ (getPreviousEpoch_le _) (Or.inr rfl)
  have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have px := getPreviousEpoch_toNat x.state
  have py := getPreviousEpoch_toNat y.state
  refine ⟨v, by simpa using Array.mem_of_getElem? found, keyEq, ?_⟩
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active now prev
  rcases active with h | h <;> omega

private theorem carry_key_same_epoch {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .pectra)
    {key : Cryptography.Bls.BLSPubkey}
    (member : key ∈ (recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) :
    getCurrentEpoch y.state = getCurrentEpoch x.state := by
  classical
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨both, absent⟩ := Finset.mem_sdiff.mp member
  obtain ⟨⟨i, old, found, keyEq, activation, exit⟩, _⟩ :=
    (mem_boundary_iff x.state (Nat.lt_trans xEarly (by decide))
      (run_unique shared genesis) key).mp
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp both).2, absent⟩)
  obtain ⟨v, current, kept⟩ := tail.registryLifecycle.validators i old found
  have assigned : old.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro h
    exact getCurrentEpoch_ne_farFuture twoSlots x.state
      ((UInt64.toNat_inj.mp exit).symm.trans h)
  have exitSame := kept.exitEpoch assigned
  obtain ⟨w, wFound, wKey⟩ := key_preserved tail i old found
  have equal : w = v := Option.some.inj (wFound.symm.trans current)
  have vKey : v.pubkey = key := equal ▸ wKey.trans keyEq
  have active : isActiveValidator v (getCurrentEpoch y.state) = true ∨
      isActiveValidator v (getPreviousEpoch y.state) = true := by
    have recent := (Finset.mem_filter.mp (Finset.mem_inter.mp both).1).1
    have unique := run_unique (shared.append tail) genesis
    have identify {j : Nat} {z : Validator} (zFound : y.state.validators.data[j]? = some z)
        (zKey : z.pubkey = key) : z = v := by
      obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp current
      obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp zFound
      have eq : j = i := unique.eq_of_getElem_eq
        (by simpa [validatorKeys] using hj) (by simpa [validatorKeys] using hi)
        (by simpa [validatorKeys] using zKey.trans vKey.symm)
      subst j
      rfl
    rcases Finset.mem_union.mp recent with h | h
    · obtain ⟨j, z, zFound, zKey, h⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact Or.inl (identify zFound zKey ▸ h)
    · obtain ⟨j, z, zFound, zKey, h⟩ :=
        (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mp h
      exact Or.inr (identify zFound zKey ▸ h)
  have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have py := getPreviousEpoch_toNat y.state
  have exitNat := congrArg UInt64.toNat exitSame
  apply UInt64.toNat_inj.mp
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
  rcases active with h | h <;> omega

private theorem leaving_key_exit {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .pectra)
    {key : Cryptography.Bls.BLSPubkey} (member : key ∈ activeKeys x.state \ activeKeys y.state) :
    ∃ v ∈ y.state.validators.data.toList, v.pubkey = key ∧
      (getCurrentEpoch x.state).toNat < v.exitEpoch.toNat ∧
      v.exitEpoch.toNat ≤ (getCurrentEpoch y.state).toNat := by
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨active, absent⟩ := Finset.mem_sdiff.mp member
  obtain ⟨i, old, found, keyEq, active⟩ :=
    (mem_keysAt_epoch (Nat.lt_trans xEarly (by decide)) _ key).mp active
  obtain ⟨v, current, same⟩ := key_preserved tail i old found
  have kept := activeKept_of_chainSteps tail.chainSteps
    (getCurrentEpoch x.state) (getCurrentEpoch_le_activityFixedEpoch _) i
  have before : isActiveValidator v (getCurrentEpoch x.state) = true := by
    simpa [isActiveAt, current, found, active] using kept
  have after : ¬ isActiveValidator v (getCurrentEpoch y.state) = true := by
    intro active
    apply absent
    exact (mem_keysAt_epoch (Nat.lt_trans early (by decide)) _ key).mpr
      ⟨i, v, current, same.trans keyEq, active⟩
  have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at before after
  exact ⟨v, by simpa using Array.mem_of_getElem? current, same.trans keyEq, before.2, by omega⟩

theorem leaving_before_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (early : y.fork < .pectra) :
    Models.stake (effectiveWeight x.state) (activeKeys x.state \ activeKeys y.state) ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        max 1 (cohortCap config y.state.validators.data.size) *
          preset.MAX_EFFECTIVE_BALANCE.toNat := by
  classical
  let departing := y.state.validators.data.toList.filter fun v =>
    (getCurrentEpoch x.state).toNat < v.exitEpoch.toNat &&
      v.exitEpoch.toNat ≤ (getCurrentEpoch y.state).toNat
  have subset : activeKeys x.state \ activeKeys y.state ⊆
      (departing.map (·.pubkey)).toFinset := by
    intro key member
    obtain ⟨v, present, keyEq, lower, upper⟩ := leaving_key_exit tail early member
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨v, List.mem_filter.mpr ⟨present, by simp [lower, upper]⟩, keyEq⟩)
  have cohorts := (shared.append tail).exitCohortBound early genesis.exitCohortBound
  have count : departing.length ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        max 1 (cohortCap config y.state.validators.data.size) := by
    apply count_epoch_window
    intro n member
    have upper := (Finset.mem_Ioc.mp member).2
    have small : n < 2 ^ 64 := lt_of_le_of_lt upper (UInt64.toNat_lt _)
    have numeric : n.toUInt64.toNat = n := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
    have finite : n.toUInt64 ≠ FAR_FUTURE_EPOCH := by
      intro equal
      have far : n = 2 ^ 64 - 1 := by
        have h := congrArg UInt64.toNat equal
        rw [numeric] at h
        exact h
      have current := getCurrentEpoch_ne_farFuture twoSlots y.state
      have currentNat := UInt64.toNat_lt (getCurrentEpoch y.state)
      apply current
      apply UInt64.toNat_inj.mp
      change _ = 2 ^ 64 - 1
      omega
    have count := cohorts n.toUInt64 finite
    have predicates : (fun v : Validator => v.exitEpoch.toNat == n) =
        (fun v => v.exitEpoch == n.toUInt64) := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, ← UInt64.toNat_inj, numeric]
    simpa only [predicates, validatorCohort, registryChurnCap, cohortCap] using count
  have cards := (Finset.card_le_card subset).trans
    (List.toFinset_card_le (departing.map (·.pubkey)))
  simp only [List.length_map] at cards
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  unfold Models.stake
  calc
    _ ≤ ∑ _key ∈ activeKeys x.state \ activeKeys y.state,
        preset.MAX_EFFECTIVE_BALANCE.toNat :=
      Finset.sum_le_sum (fun key _ => effectiveWeight_le_cap shared genesis caps xEarly key)
    _ = (activeKeys x.state \ activeKeys y.state).card *
        preset.MAX_EFFECTIVE_BALANCE.toNat := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (cards.trans count)

/-- New recent keys use only activation cohorts, including when their count cap is zero. -/
private theorem new_recent_before_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (early : y.fork < .pectra) :
    Models.stake (effectiveWeight y.state) (recentKeys y.state \ recentKeys x.state) ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        cohortCap config y.state.validators.data.size * preset.MAX_EFFECTIVE_BALANCE.toNat := by
  classical
  let activated := y.state.validators.data.toList.filter fun v =>
    (getCurrentEpoch x.state).toNat < v.activationEpoch.toNat &&
      v.activationEpoch.toNat ≤ (getCurrentEpoch y.state).toNat
  have subset : recentKeys y.state \ recentKeys x.state ⊆
      (activated.map (·.pubkey)).toFinset := by
    intro key member
    obtain ⟨v, present, keyEq, lower, upper⟩ := new_recent_key_activation tail early member
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨v, List.mem_filter.mpr ⟨present, by simp [lower, upper]⟩, keyEq⟩)
  have cohorts := (shared.append tail).activationCohortBound early genesis.activationCohortBound
  have count : activated.length ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        cohortCap config y.state.validators.data.size := by
    apply count_epoch_window
    intro n member
    obtain ⟨lower, upper⟩ := Finset.mem_Ioc.mp member
    have small : n < 2 ^ 64 := lt_of_le_of_lt upper (UInt64.toNat_lt _)
    have numeric : n.toUInt64.toNat = n := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
    have finite : n.toUInt64 ≠ FAR_FUTURE_EPOCH := by
      intro equal
      have far : n = 2 ^ 64 - 1 := by
        have h := congrArg UInt64.toNat equal
        rw [numeric] at h
        exact h
      have current := getCurrentEpoch_ne_farFuture twoSlots y.state
      have currentNat := UInt64.toNat_lt (getCurrentEpoch y.state)
      apply current
      apply UInt64.toNat_inj.mp
      change _ = 2 ^ 64 - 1
      omega
    have nonzero : n.toUInt64 ≠ GENESIS_EPOCH := by
      intro equal
      have h := congrArg UInt64.toNat equal
      rw [numeric] at h
      change n = 0 at h
      omega
    have bound := cohorts.count n.toUInt64 finite nonzero
    have predicates : (fun v : Validator => v.activationEpoch.toNat == n) =
        (fun v => v.activationEpoch == n.toUInt64) := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, ← UInt64.toNat_inj, numeric]
    simpa only [predicates, validatorCohort, registryChurnCap, cohortCap] using bound
  have cards := (Finset.card_le_card subset).trans
    (List.toFinset_card_le (activated.map (·.pubkey)))
  simp only [List.length_map] at cards
  unfold Models.stake
  calc
    _ ≤ ∑ _key ∈ recentKeys y.state \ recentKeys x.state,
        preset.MAX_EFFECTIVE_BALANCE.toNat :=
      Finset.sum_le_sum (fun key _ =>
        effectiveWeight_le_cap (shared.append tail) genesis caps early key)
    _ = (recentKeys y.state \ recentKeys x.state).card *
        preset.MAX_EFFECTIVE_BALANCE.toNat := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (cards.trans count)

/-- Separate new activation cohorts from reference previous-only stake without a positive cap. -/
theorem joining_before_electra_split {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (early : y.fork < .pectra) :
    Models.stake (effectiveWeight y.state) (recentKeys y.state \ recentKeys x.state) ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        cohortCap config y.state.validators.data.size * preset.MAX_EFFECTIVE_BALANCE.toNat ∧
    Models.stake (effectiveWeight y.state)
      ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) ≤ boundaryStake x := by
  classical
  refine ⟨new_recent_before_electra shared tail genesis twoSlots caps early, ?_⟩
  have uniqueX := run_unique shared genesis
  have uniqueY := run_unique (shared.append tail) genesis
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have pointwise (key : Cryptography.Bls.BLSPubkey)
      (member : key ∈ (recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) :
      effectiveWeight y.state key ≤ effectiveWeight x.state key := by
    have same := carry_key_same_epoch shared tail genesis twoSlots early member
    obtain ⟨both, absent⟩ := Finset.mem_sdiff.mp member
    obtain ⟨⟨i, old, found, keyEq, _⟩, _⟩ :=
      (mem_boundary_iff x.state (Nat.lt_trans xEarly (by decide)) uniqueX key).mp
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp both).2, absent⟩)
    obtain ⟨v, current, vKey⟩ := key_preserved tail i old found
    have bound := tail.effectiveAt_le_of_same_epoch early same i
      (Array.getElem?_eq_some_iff.mp found).1
    have oldWeight := effectiveWeight_of_member uniqueX
      (by simpa using Array.mem_of_getElem? found)
    have newWeight := effectiveWeight_of_member uniqueY
      (by simpa using Array.mem_of_getElem? current)
    rw [keyEq] at oldWeight
    rw [vKey, keyEq] at newWeight
    rw [oldWeight, newWeight]
    simpa [effectiveAt, found, current] using bound
  unfold boundaryStake Models.stake
  exact (Finset.sum_le_sum pointwise).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro key member
        exact Finset.mem_sdiff.mpr
          ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp member).1).2,
            (Finset.mem_sdiff.mp member).2⟩)
      (by intros; exact Nat.zero_le _))

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

/-- A queue charge can spend earlier epochs; an arbitrary window needs its carry-in. -/
theorem exit_queue_charge {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (amount : Gwei) (epoch : Epoch)
    (ok : computeExitEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ first churn,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      exitChurnLimit config s = .ok churn ∧
      amount.toNat + (t.exitBalanceToConsume electra).toNat =
        (if (s.earliestExitEpoch electra) < max (s.earliestExitEpoch electra) first
          then churn.toNat else (s.exitBalanceToConsume electra).toNat) +
        (epoch.toNat - (max (s.earliestExitEpoch electra) first).toNat) * churn.toNat := by
  simp only [computeExitEpochAndUpdateChurn, Base.bind_ok_iff, liftArith,
    Base.mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨first, firstOk, churn, churnOk, ⟨placed, left⟩, queued, result⟩ := ok
  cases result
  refine ⟨first, churn, firstOk, churnOk, ?_⟩
  have spent := (churnQueue_spend queued).2.1
  split at spent <;> rename_i branch
  all_goals simp only [branch, ↓reduceIte]; omega

theorem consolidation_queue_charge {fork : Fork} (s t : BeaconState preset fork)
    (electra : .pectra ≤ fork) (amount : Gwei) (epoch : Epoch)
    (ok : computeConsolidationEpochAndUpdateChurn config s electra amount = .ok (t, epoch)) :
    ∃ first churn,
      computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      getConsolidationChurnLimit config s = .ok churn ∧
      amount.toNat + (t.consolidationBalanceToConsume electra).toNat =
        (if (s.earliestConsolidationEpoch electra) <
            max (s.earliestConsolidationEpoch electra) first then churn.toNat
          else (s.consolidationBalanceToConsume electra).toNat) +
        (epoch.toNat - (max (s.earliestConsolidationEpoch electra) first).toNat) * churn.toNat := by
  simp only [computeConsolidationEpochAndUpdateChurn, Base.bind_ok_iff, liftArith,
    Base.mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨first, firstOk, churn, churnOk, ⟨placed, left⟩, queued, result⟩ := ok
  cases result
  refine ⟨first, churn, firstOk, churnOk, ?_⟩
  have spent := (churnQueue_spend queued).2.1
  split at spent <;> rename_i branch
  all_goals simp only [branch, ↓reduceIte]; omega

end EthLib.Consensus.DirectSafety
