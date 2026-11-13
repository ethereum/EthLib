module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
public import EthLib.Consensus.Proofs.Churn
public import EthLib.Consensus.Proofs.DirectSafety.Drift
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# Departure charges and the Electra crossing

A departure charge is a validator's effective balance.

It is counted when the validator's unset exit epoch becomes assigned.

Electra exits spend balance churn, and consolidations spend their own queue's churn.

The Electra upgrade starts both queues with the churn of the upgraded state.

Before Electra, the validator-count churn bounds the stake that joins a window.

The boundary support is the unslashed cohort that exits at the current epoch.

The balance queues are specified by [EIP-7251].

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The pre-Electra churn limit, in validators, for `size` active validators. -/
def cohortCap (config : Config) (size : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT.toNat (size / config.CHURN_LIMIT_QUOTIENT.toNat)

/-- A departure: a validator, its new exit epoch and its effective balance before the step. -/
structure DepartureCharge where
  /-- The position of the validator in the registry. -/
  index : Nat
  /-- The exit epoch that the step assigns. -/
  epoch : Nat
  /-- The effective balance before the step, in Gwei. -/
  amount : Nat

/-- The departure charges of one step, one per validator of its input whose exit it assigns.

A charge reads the effective balance before the step, not after the effective-balance updates. -/
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

/-- The departure charges of two runs in turn are those of the first, then the second. -/
theorem _root_.EthLib.Consensus.Run.departureCharges_append {a b c : ForkedBeaconState preset}
    (one : Run config checks a b) (two : Run config checks b c) :
    (one.append two).departureCharges = one.departureCharges ++ two.departureCharges := by
  induction two with
  | nil => simp [Run.append, Run.departureCharges]
  | snoc two step ih => simp only [Run.append, Run.departureCharges, ih, List.append_assoc]

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

/-- A key slashed at the start of a run is slashed at its end: slashing persists forward. -/
theorem slashedAt_forward {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {key : Cryptography.Bls.BLSPubkey}
    (slashed : SlashedAt x.state key) : SlashedAt y.state key := by
  obtain ⟨v, member, keyEq, flag⟩ := slashed
  obtain ⟨i, found⟩ := Array.getElem?_of_mem (by simpa using member)
  obtain ⟨w, wFound, wFlag⟩ := tail.slashedPersistence i v found flag
  obtain ⟨u, uFound, uKey⟩ := validators_getElem?_of_validatorKeys_prefix
      (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 found
  have same : u = w := Option.some.inj (uFound.symm.trans wFound)
  exact ⟨w, by simpa using Array.mem_of_getElem? wFound, same ▸ uKey.trans keyEq, wFlag⟩

/-- A key of an epoch is the key of a validator active at that epoch. -/
theorem mem_keysAt_epoch {fork : Fork} {state : BeaconState preset fork}
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

/-- Distinct registry keys identify the boundary support with this epoch's exiting cohort.

The boundary support is unslashed, so the exiting validator is unslashed too. -/
theorem mem_boundary_iff {fork : Fork} (state : BeaconState preset fork)
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

/-- The Electra upgrade keeps the epoch and opens the exit queue after every exit already scheduled.

Both queues start with the churn limits of the upgraded state. -/
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

/-- A run from before Electra that reaches it splits at one step from a fork before Electra. -/
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
