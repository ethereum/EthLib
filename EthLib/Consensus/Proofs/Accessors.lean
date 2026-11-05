module

public import EthLib.Consensus.Accessors

/-!
# Proofs: state accessors

The active indices are exactly the indices of the active validators, in increasing order.

A total balance reads its indices as a set: their order and their repeats do not matter.

A total balance is at least one effective balance increment.

The total active balance never fails on an index, only on a sum of 2^64 or more.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- A position of the validator registry, as a validator index, keeps its value. -/
theorem toNat_toUInt64_of_lt {state : BeaconState preset fork} {i : Nat}
    (lt : i < state.validators.data.size) : i.toUInt64.toNat = i := by
  have bound := state.validators.bound
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- An index is active exactly when it names a validator that is active in the epoch. -/
theorem mem_getActiveValidatorIndices {state : BeaconState preset fork} {epoch : Epoch}
    {index : ValidatorIndex} :
    index ∈ getActiveValidatorIndices state epoch ↔
      ∃ validator, state.validators.data[index.toNat]? = some validator ∧
        isActiveValidator validator epoch = true := by
  simp only [getActiveValidatorIndices, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, List.mem_zipIdx_iff_getElem?, Prod.exists]
  constructor
  · rintro ⟨validator, i, found, active, rfl⟩
    have lt : i < state.validators.data.size := by
      have := (List.getElem?_eq_some_iff.mp found).1
      simpa using this
    rw [toNat_toUInt64_of_lt lt]
    exact ⟨validator, by simpa using found, active⟩
  · rintro ⟨validator, found, active⟩
    refine ⟨validator, index.toNat, by simpa using found, active, ?_⟩
    simp

/-- The active indices increase strictly. -/
theorem getActiveValidatorIndices_sorted (state : BeaconState preset fork) (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).Pairwise (· < ·) := by
  unfold getActiveValidatorIndices
  have base : state.validators.data.toList.zipIdx.Pairwise (fun a b => a.2 < b.2) := by
    have := List.pairwise_lt_range' (s := 0) (n := state.validators.data.toList.length)
    rw [← List.zipIdx_map_snd 0] at this
    exact List.pairwise_map.mp this
  refine List.Pairwise.filterMap _ ?_ (List.Pairwise.and_mem.mp base)
  rintro ⟨v, i⟩ ⟨w, j⟩ ⟨mi, mj, lt⟩ a ha b hb
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at ha hb
  obtain ⟨-, rfl⟩ := ha
  obtain ⟨-, rfl⟩ := hb
  have hi : i < state.validators.data.size := by simpa using (List.mem_zipIdx' mi).1
  have hj : j < state.validators.data.size := by simpa using (List.mem_zipIdx' mj).1
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64_of_lt hi, toNat_toUInt64_of_lt hj]
  exact lt

/-- Marking indices one after the other sets exactly the entries that some index names. -/
theorem getElem?_foldl_mark (indices : List ValidatorIndex) (init : Array Bool) (j : Nat) :
    (indices.foldl (fun marked index => marked.set! index.toNat true) init)[j]? =
      init[j]?.map (· || indices.any (·.toNat == j)) := by
  induction indices generalizing init with
  | nil =>
    simp only [List.foldl_nil, List.any_nil, Bool.or_false]
    cases init[j]? <;> rfl
  | cons index rest ih =>
    rw [List.foldl_cons, ih, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases same : index.toNat = j
    · subst same
      by_cases inside : index.toNat < init.size
      · simp [inside]
      · simp [inside]
    · have differ : (index.toNat == j) = false := by simpa using same
      cases init[j]? <;> simp [same, differ]

/-- The mark of a validator is set exactly when some index names it. -/
theorem getElem?_markIndices (size : Nat) (indices : List ValidatorIndex) (j : Nat) :
    (markIndices size indices)[j]? =
      if j < size then some (indices.any (·.toNat == j)) else none := by
  rw [markIndices, getElem?_foldl_mark]
  by_cases lt : j < size <;> simp [lt]

/-- Two lists with the same members mark the same validators. -/
theorem markIndices_congr {size : Nat} {first second : List ValidatorIndex}
    (same : ∀ index, index ∈ first ↔ index ∈ second) :
    markIndices size first = markIndices size second := by
  refine Array.ext_getElem? fun j => ?_
  rw [getElem?_markIndices, getElem?_markIndices]
  have : first.any (·.toNat == j) = second.any (·.toNat == j) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    exact ⟨fun ⟨x, m, e⟩ => ⟨x, (same x).mp m, e⟩, fun ⟨x, m, e⟩ => ⟨x, (same x).mpr m, e⟩⟩
  rw [this]

/-- A total balance exists exactly when every index names a validator and the sum of the marked
effective balances is below 2^64.

It is then that sum, or one increment if the sum is smaller. -/
theorem getTotalBalance_ok_iff {state : BeaconState preset fork}
    {indices : List ValidatorIndex} {total : Gwei} :
    getTotalBalance state indices = .ok total ↔
      (∀ index ∈ indices, index.toNat < state.validators.data.size) ∧
        sumMarked state.validators.data
          (markIndices state.validators.data.size indices) < 2 ^ 64 ∧
        total = max preset.EFFECTIVE_BALANCE_INCREMENT
          (sumMarked state.validators.data
            (markIndices state.validators.data.size indices)).toUInt64 := by
  unfold getTotalBalance
  cases found : indices.find? (state.validators.data.size ≤ ·.toNat) with
  | some index =>
    obtain ⟨outside, member⟩ := List.find?_eq_some_iff_append.mp found |>.imp_right
      fun ⟨as, bs, eq, _⟩ => eq ▸ List.mem_append_right as (List.mem_cons_self ..)
    have notAll : ¬ ∀ i ∈ indices, i.toNat < state.validators.data.size := fun inside => by
      have := inside index member
      simp at outside
      omega
    simp only [found]
    constructor
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · intro h
      exact absurd h.1 notAll
  | none =>
    have inside : ∀ index ∈ indices, index.toNat < state.validators.data.size := by
      intro index member
      have := List.find?_eq_none.mp found index member
      simp at this
      exact this
    simp only [found]
    by_cases big : 2 ^ 64 ≤ sumMarked state.validators.data
        (markIndices state.validators.data.size indices)
    · constructor
      · intro h
        simp [big, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · rintro ⟨-, lt, -⟩
        omega
    · have lt : sumMarked state.validators.data
          (markIndices state.validators.data.size indices) < 2 ^ 64 := by omega
      simp only [big, ite_false, pure, Except.pure, Except.ok.injEq]
      constructor
      · rintro rfl
        exact ⟨inside, lt, rfl⟩
      · rintro ⟨-, -, rfl⟩
        rfl

/-- A total balance is at least one effective balance increment. -/
theorem le_getTotalBalance {state : BeaconState preset fork} {indices : List ValidatorIndex}
    {total : Gwei} (ok : getTotalBalance state indices = .ok total) :
    preset.EFFECTIVE_BALANCE_INCREMENT ≤ total := by
  obtain ⟨-, -, rfl⟩ := getTotalBalance_ok_iff.mp ok
  rw [UInt64.max_def]
  split
  · assumption
  · exact UInt64.le_refl _

/-- A total balance depends on its indices only as a set: their order and repeats do not matter. -/
theorem getTotalBalance_congr {state : BeaconState preset fork}
    {first second : List ValidatorIndex} (same : ∀ index, index ∈ first ↔ index ∈ second)
    {total : Gwei} :
    getTotalBalance state first = .ok total ↔ getTotalBalance state second = .ok total := by
  rw [getTotalBalance_ok_iff, getTotalBalance_ok_iff, markIndices_congr same]
  exact ⟨fun ⟨inside, rest⟩ => ⟨fun i m => inside i ((same i).mpr m), rest⟩,
    fun ⟨inside, rest⟩ => ⟨fun i m => inside i ((same i).mp m), rest⟩⟩

/-- The total active balance never fails on an index: every active index names a validator. -/
theorem getTotalActiveBalance_ne_indexOutOfRange (state : BeaconState preset fork)
    (index : ValidatorIndex) :
    getTotalActiveBalance state ≠ .error (.indexOutOfRange index) := by
  have inside : ∀ i ∈ getActiveValidatorIndices state (getCurrentEpoch state),
      i.toNat < state.validators.data.size := by
    intro i member
    obtain ⟨_, found, -⟩ := mem_getActiveValidatorIndices.mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have none : (getActiveValidatorIndices state (getCurrentEpoch state)).find?
      (state.validators.data.size ≤ ·.toNat) = none := by
    rw [List.find?_eq_none]
    intro i member
    have := inside i member
    simp
    omega
  unfold getTotalActiveBalance getTotalBalance
  simp only [none]
  by_cases big : 2 ^ 64 ≤ sumMarked state.validators.data (markIndices state.validators.data.size
      (getActiveValidatorIndices state (getCurrentEpoch state)))
  · simp [big, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp [big, pure, Except.pure]

end EthLib.Consensus
