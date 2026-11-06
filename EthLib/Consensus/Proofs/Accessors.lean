module

public import EthLib.Consensus.Accessors
public import EthLib.Consensus.Proofs.ShufflePermutation
public import EthLib.Consensus.Proofs.Signing

/-!
# Proofs: state accessors

The active indices are exactly the indices of the active validators, in increasing order.

That needs the registry to stay within the limit of the preset, which its type says before Gloas.

From Gloas the registry is a progressive list, so these theorems take the bound as a hypothesis.

A total balance reads its indices as a set: their order and their repeats do not matter.

A total balance is at least one effective balance increment.

The total active balance never fails on an index, only on a sum of 2^64 or more.

The previous epoch is the current one minus one, or the genesis epoch at genesis.

Each slot has from one committee up to the most committees of the preset.

Each member of a committee, and each validator that an attestation shows, is active in its epoch.

The indices of an attestation increase strictly, as the check of an indexed attestation asks.

An attestation has at most as many signers as bits, so its indexed form never exceeds its limit.

Before Fulu, the proposer is active in the epoch of the state.

A signature domain always has a value.

A write to a circular buffer is read back at its position, and leaves every other entry unchanged.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- A position of the validator registry, as a validator index, keeps its value.

The registry must stay within the limit of the preset, which its type says before Gloas. -/
theorem toNat_toUInt64_of_lt {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) {i : Nat} (lt : i < state.validators.data.size) :
    i.toUInt64.toNat = i := by
  have bound : state.validators.data.size ≤ _ := within
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- An index is active exactly when it names a validator that is active in the epoch. -/
theorem mem_getActiveValidatorIndices {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) {epoch : Epoch} {index : ValidatorIndex} :
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
    rw [toNat_toUInt64_of_lt within lt]
    exact ⟨validator, by simpa using found, active⟩
  · rintro ⟨validator, found, active⟩
    refine ⟨validator, index.toNat, by simpa using found, active, ?_⟩
    simp

/-- The active indices increase strictly. -/
theorem getActiveValidatorIndices_sorted {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
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
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64_of_lt within hi, toNat_toUInt64_of_lt within hj]
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
theorem getTotalActiveBalance_ne_indexOutOfRange {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (index : ValidatorIndex) :
    getTotalActiveBalance state ≠ .error (.indexOutOfRange index) := by
  have inside : ∀ i ∈ getActiveValidatorIndices state (getCurrentEpoch state),
      i.toNat < state.validators.data.size := by
    intro i member
    obtain ⟨_, found, -⟩ := (mem_getActiveValidatorIndices within).mp member
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


/-- The previous epoch is at most the current epoch. -/
theorem getPreviousEpoch_le (state : BeaconState preset fork) :
    getPreviousEpoch state ≤ getCurrentEpoch state := by
  unfold getPreviousEpoch saturatingSub
  split
  · rename_i lt
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    omega
  · exact UInt64.zero_le

/-- After genesis, the previous epoch is the epoch just before the current one. -/
theorem getPreviousEpoch_add_one {state : BeaconState preset fork}
    (positive : getCurrentEpoch state ≠ 0) : getPreviousEpoch state + 1 = getCurrentEpoch state := by
  unfold getPreviousEpoch saturatingSub
  have nonzero : (getCurrentEpoch state).toNat ≠ 0 :=
    fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  split
  · rename_i lt
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    have := (getCurrentEpoch state).toNat_lt
    simp
    omega
  · rename_i notLt
    rw [UInt64.lt_iff_toNat_lt] at notLt
    have one : (getCurrentEpoch state).toNat = 1 := by simp at notLt; omega
    apply UInt64.toNat_inj.mp
    simp [one]

/-- The number of active validators fits in 64 bits, when the registry stays within its limit. -/
theorem length_getActiveValidatorIndices_lt {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).length < 2 ^ 64 := by
  unfold getActiveValidatorIndices
  refine Nat.lt_of_le_of_lt (List.length_filterMap_le _ _) ?_
  have bound : state.validators.data.size ≤ _ := within
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  simp only [List.length_zipIdx, Array.length_toList]
  omega

/-- The number of active validators, as a 64-bit integer, keeps its value. -/
theorem toNat_length_getActiveValidatorIndices {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).length.toUInt64.toNat =
      (getActiveValidatorIndices state epoch).length := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (length_getActiveValidatorIndices_lt within epoch)]

/-- Each slot has at least one committee. -/
theorem one_le_getCommitteeCountPerSlot (state : BeaconState preset fork) (epoch : Epoch) :
    1 ≤ getCommitteeCountPerSlot state epoch := by
  simp only [getCommitteeCountPerSlot, max, min]
  repeat' split
  all_goals simp_all [UInt64.le_iff_toNat_le]
  all_goals omega

/-- A slot has at most the most committees of the preset, or one if that is zero. -/
theorem getCommitteeCountPerSlot_le (state : BeaconState preset fork) (epoch : Epoch) :
    getCommitteeCountPerSlot state epoch ≤ max 1 preset.MAX_COMMITTEES_PER_SLOT := by
  simp only [getCommitteeCountPerSlot, max, min]
  repeat' split
  all_goals simp_all [UInt64.le_iff_toNat_le]
  all_goals omega

/-- Each member of a committee is active in the epoch of its slot. -/
theorem mem_getActiveValidatorIndices_of_getBeaconCommittee {state : BeaconState preset fork}
    {slot : Slot} {index : CommitteeIndex} {committee : Array ValidatorIndex}
    (computed : getBeaconCommittee state slot index = .ok committee)
    {member : ValidatorIndex} (mem : member ∈ committee) :
    member ∈ getActiveValidatorIndices state (computeEpochAtSlot preset slot) := by
  simp only [getBeaconCommittee, bind, Except.bind] at computed
  split at computed
  · cases computed
  split at computed
  · cases computed
  split at computed
  · cases computed
  simpa using mem_of_computeCommittee (mapError_ok_iff.mp computed) mem

/-- One step of the pass that drops repeats keeps its list decreasing, below the rest. -/
theorem keepNew_step {kept rest : List ValidatorIndex} {first : ValidatorIndex}
    (decreasing : kept.Pairwise (· > ·)) (keptLe : ∀ last ∈ kept, last ≤ first)
    (firstLe : ∀ index ∈ rest, first ≤ index) :
    (keepNew kept first).Pairwise (· > ·) ∧
      (∀ last ∈ keepNew kept first, ∀ index ∈ rest, last ≤ index) ∧
      ∀ index, index ∈ keepNew kept first ↔ index ∈ kept ∨ index = first := by
  have trans : ∀ a b c : UInt64, a ≤ b → b ≤ c → a ≤ c := fun a b c ab bc => by
    rw [UInt64.le_iff_toNat_le] at *; omega
  match kept with
  | [] => simpa [keepNew] using firstLe
  | last :: older =>
    by_cases same : last = first
    · subst same
      refine ⟨by simpa [keepNew] using decreasing, ?_, ?_⟩
      · intro other mem index inRest
        simp only [keepNew, ite_true] at mem
        exact trans _ _ _ (keptLe other mem) (firstLe index inRest)
      · intro index
        simp only [keepNew, ite_true, List.mem_cons]
        constructor
        · exact Or.inl
        · rintro (inKept | rfl)
          · exact inKept
          · exact Or.inl rfl
    · simp only [keepNew, same, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · refine List.pairwise_cons.mpr ⟨fun other mem => ?_, decreasing⟩
        have otherLe := keptLe other mem
        have lastLe := keptLe last (by simp)
        rw [List.mem_cons] at mem
        rcases mem with rfl | inOlder
        · rw [UInt64.le_iff_toNat_le] at otherLe
          have : other.toNat ≠ first.toNat := fun eq => same (UInt64.toNat_inj.mp eq)
          show other < first
          rw [UInt64.lt_iff_toNat_lt]
          omega
        · have below := (List.pairwise_cons.mp decreasing).1 other inOlder
          show other < first
          rw [UInt64.lt_iff_toNat_lt]
          rw [UInt64.le_iff_toNat_le] at lastLe
          rw [gt_iff_lt, UInt64.lt_iff_toNat_lt] at below
          omega
      · intro other mem index inRest
        rw [List.mem_cons] at mem
        rcases mem with rfl | inKept
        · exact firstLe index inRest
        · exact trans _ _ _ (keptLe other inKept) (firstLe index inRest)
      · intro index
        simp only [List.mem_cons]
        constructor
        · rintro (rfl | inKept)
          · exact Or.inr rfl
          · exact Or.inl inKept
        · rintro (inKept | rfl)
          · exact Or.inr inKept
          · exact Or.inl rfl

/-- The pass that drops repeats, on a sorted list, onto a list kept in decreasing order. -/
theorem foldl_keepNew {indices kept : List ValidatorIndex}
    (sorted : indices.Pairwise (· ≤ ·)) (decreasing : kept.Pairwise (· > ·))
    (below : ∀ last ∈ kept, ∀ index ∈ indices, last ≤ index) :
    (indices.foldl keepNew kept).Pairwise (· > ·) ∧
      ∀ index, index ∈ indices.foldl keepNew kept ↔ index ∈ kept ∨ index ∈ indices := by
  induction indices generalizing kept with
  | nil => simpa using decreasing
  | cons first rest ih =>
    rw [List.pairwise_cons] at sorted
    obtain ⟨stepDecreasing, stepBelow, stepMem⟩ := keepNew_step (rest := rest) decreasing
      (fun last mem => below last mem first (by simp)) sorted.1
    obtain ⟨resultDecreasing, resultMem⟩ := ih sorted.2 stepDecreasing stepBelow
    refine ⟨resultDecreasing, fun index => ?_⟩
    rw [List.foldl_cons, resultMem, stepMem, List.mem_cons, or_assoc]

/-- The sort of a list of indices is in increasing order. -/
theorem mergeSort_sorted (indices : List ValidatorIndex) :
    (indices.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
    (fun a b c ab bc => by simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le]; omega)
    indices
  simpa using sorted

/-- The pass over the sorted list gives a decreasing list with the same members. -/
theorem sortedSet_spec (indices : List ValidatorIndex) :
    ((indices.mergeSort (· ≤ ·)).foldl keepNew []).Pairwise (· > ·) ∧
      ∀ index, index ∈ (indices.mergeSort (· ≤ ·)).foldl keepNew [] ↔
        index ∈ [] ∨ index ∈ indices.mergeSort (· ≤ ·) :=
  foldl_keepNew (mergeSort_sorted indices) List.Pairwise.nil (by simp)

/-- The set of a list has the same members as the list. -/
theorem mem_sortedSet {indices : List ValidatorIndex} {index : ValidatorIndex} :
    index ∈ sortedSet indices ↔ index ∈ indices := by
  rw [sortedSet, List.mem_reverse, (sortedSet_spec indices).2, List.mem_mergeSort]
  simp

/-- The set of a list increases strictly, so it holds each index once. -/
theorem sortedSet_sorted (indices : List ValidatorIndex) :
    (sortedSet indices).Pairwise (· < ·) := by
  rw [sortedSet, List.pairwise_reverse]
  exact (sortedSet_spec indices).1

/-- Each attester of a committee is a member of it. -/
theorem mem_of_committeeAttesters {bits : Array Bool} {offset : Nat}
    {committee : Array ValidatorIndex} {attesters : List ValidatorIndex}
    (computed : committeeAttesters bits offset committee = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) : attester ∈ committee := by
  unfold committeeAttesters at computed
  split at computed
  · cases computed
  cases computed
  simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    List.mem_zipIdx_iff_getElem?, Prod.exists] at mem
  obtain ⟨member, position, found, -, rfl⟩ := mem
  exact Array.mem_toList_iff.mp (List.mem_of_getElem? found)

/-- From Electra: each attester of a list of committees is active in the epoch of the slot. -/
theorem mem_of_committeesAttesters {state : BeaconState preset fork} {slot : Slot}
    {bits : Array Bool} {committees : List CommitteeIndex} {offset : Nat}
    {attesters : List ValidatorIndex}
    (computed : committeesAttesters state slot bits committees offset = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) :
    attester ∈ getActiveValidatorIndices state (computeEpochAtSlot preset slot) := by
  induction committees generalizing offset attesters with
  | nil =>
    cases computed
    simp at mem
  | cons index rest ih =>
    simp only [committeesAttesters, bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i committee committeeOk
    split at computed
    · cases computed
    rename_i here hereOk
    split at computed
    · cases computed
    rename_i later laterOk
    cases computed
    rcases List.mem_append.mp mem with inHere | inLater
    · exact mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
        (mem_of_committeeAttesters hereOk inHere)
    · exact ih laterOk inLater

/-- Each validator that an attestation shows as a signer is active in the epoch of its slot. -/
theorem mem_getActiveValidatorIndices_of_getAttestingIndices {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters)
    {attester : ValidatorIndex} (mem : attester ∈ attesters) :
    attester ∈ getActiveValidatorIndices state (computeEpochAtSlot preset attestation.data.slot) := by
  unfold getAttestingIndices at computed
  split at computed
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i listed listedOk
    cases computed
    exact mem_of_committeesAttesters listedOk (mem_sortedSet.mp mem)
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i committee committeeOk
    split at computed
    · cases computed
    rename_i listed listedOk
    cases computed
    exact mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
      (mem_of_committeeAttesters listedOk (mem_sortedSet.mp mem))

/-- The validators that an attestation shows as signers increase strictly. -/
theorem getAttestingIndices_sorted {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    attesters.Pairwise (· < ·) := by
  unfold getAttestingIndices at computed
  split at computed <;>
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    repeat' (split at computed; · cases computed)
    cases computed
    exact sortedSet_sorted _

/-- The indices of an indexed attestation increase strictly, as its validity check asks. -/
theorem getIndexedAttestation_sorted {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {indexed : IndexedAttestation preset fork}
    (computed : getIndexedAttestation state attestation = .ok indexed) :
    indexed.attestingIndices.data.toList.Pairwise (· < ·) := by
  simp only [getIndexedAttestation, bind, Except.bind] at computed
  split at computed
  · cases computed
  rename_i attesters attestersOk
  split at computed
  · cases computed
    simpa using getAttestingIndices_sorted attestersOk
  · cases computed

/-- The pass that drops repeats adds at most one index for each index it reads. -/
theorem length_foldl_keepNew_le (indices kept : List ValidatorIndex) :
    (indices.foldl keepNew kept).length ≤ kept.length + indices.length := by
  induction indices generalizing kept with
  | nil => simp
  | cons first rest ih =>
    have step : (keepNew kept first).length ≤ kept.length + 1 := by
      unfold keepNew
      split
      · split <;> simp
      · simp
    have := ih (keepNew kept first)
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- The set of a list has at most as many indices as the list. -/
theorem length_sortedSet_le (indices : List ValidatorIndex) :
    (sortedSet indices).length ≤ indices.length := by
  have := length_foldl_keepNew_le (indices.mergeSort (· ≤ ·)) []
  simpa [sortedSet, List.length_mergeSort] using this

/-- The attesters of a committee read one bit each, from an offset.

So they end before the last bit, and an empty committee has none, wherever its bits start. -/
theorem length_committeeAttesters {bits : Array Bool} {offset : Nat}
    {committee : Array ValidatorIndex} {attesters : List ValidatorIndex}
    (computed : committeeAttesters bits offset committee = .ok attesters) :
    attesters.length ≤ committee.size ∧
      (0 < committee.size → offset + committee.size ≤ bits.size) := by
  unfold committeeAttesters at computed
  split at computed
  · cases computed
  rename_i inRange
  cases computed
  refine ⟨Nat.le_trans (List.length_filterMap_le _ _) (by simp), fun nonempty => ?_⟩
  omega

/-- From Electra: the attesters of a list of committees end before the last bit. -/
theorem length_committeesAttesters {state : BeaconState preset fork} {slot : Slot}
    {bits : Array Bool} {committees : List CommitteeIndex} {offset : Nat}
    {attesters : List ValidatorIndex}
    (computed : committeesAttesters state slot bits committees offset = .ok attesters) :
    offset + attesters.length ≤ max offset bits.size := by
  induction committees generalizing offset attesters with
  | nil =>
    cases computed
    simp only [List.length_nil, Nat.add_zero]
    omega
  | cons index rest ih =>
    simp only [committeesAttesters, bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i committee _
    split at computed
    · cases computed
    rename_i here hereOk
    split at computed
    · cases computed
    rename_i later laterOk
    cases computed
    obtain ⟨hereLe, reach⟩ := length_committeeAttesters hereOk
    have second := ih laterOk
    simp only [List.length_append]
    -- An empty committee moves no offset; a nonempty one ends before the last bit.
    by_cases empty : committee.size = 0
    · simp only [empty, Nat.add_zero] at second
      omega
    · have := reach (Nat.pos_of_ne_zero empty)
      omega

/-- The validators that an attestation shows as signers are at most its bits. -/
theorem length_getAttestingIndices_le {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    attesters.length ≤ attestation.aggregationBits.bits.size := by
  unfold getAttestingIndices at computed
  split at computed
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i listed listedOk
    cases computed
    have := length_committeesAttesters listedOk
    have := length_sortedSet_le listed
    omega
  · simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    split at computed
    · cases computed
    rename_i committee _ _ listed listedOk
    cases computed
    obtain ⟨short, reach⟩ := length_committeeAttesters listedOk
    have := length_sortedSet_le listed
    by_cases empty : committee.size = 0
    · omega
    · have := reach (Nat.pos_of_ne_zero empty)
      omega

/-- The check of the limit on an indexed attestation never fails.

Before Gloas the signers are at most the bits, and the bits are at most the limit.

From Gloas the list has no limit.

So the indexed form fails exactly when the signers do, with the same error. -/
theorem getIndexedAttestation_eq_error_iff {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {error : AccessorError} :
    getIndexedAttestation state attestation = .error error ↔
      getAttestingIndices state attestation = .error error := by
  simp only [getIndexedAttestation, bind, Except.bind]
  split
  · rename_i failure
    simp [failure]
  · rename_i attesters attestersOk
    simp only [attestersOk, reduceCtorEq, iff_false]
    split
    · simp [pure, Except.pure]
    · rename_i over
      exact absurd (fun before => Nat.le_trans (length_getAttestingIndices_le attestersOk)
        (attestation.aggregationBits.bound before)) over

/-- When the signers of an attestation have a value, its indexed form lists them in order. -/
theorem getIndexedAttestation_of_getAttestingIndices {state : BeaconState preset fork}
    {attestation : Attestation preset fork} {attesters : List ValidatorIndex}
    (computed : getAttestingIndices state attestation = .ok attesters) :
    ∃ indexed, getIndexedAttestation state attestation = .ok indexed ∧
      indexed.attestingIndices.data = attesters.toArray ∧ indexed.data = attestation.data ∧
      indexed.signature = attestation.signature := by
  simp only [getIndexedAttestation, bind, Except.bind, computed]
  split
  · exact ⟨_, rfl, rfl, rfl, rfl⟩
  · rename_i over
    exact absurd (fun before => Nat.le_trans (length_getAttestingIndices_le computed)
      (attestation.aggregationBits.bound before)) over

/-- The proposer search returns one of the indices, when each shuffled position is in range. -/
theorem mem_of_proposerSearch {preset : Preset} {fork : Base.Fork}
    {validators : Array Validator} {indices : Array ValidatorIndex} {shuffled : Array UInt64}
    {seed : Bytes32} (nonempty : 0 < indices.size)
    (positions : ∀ place < indices.size, (shuffled.getD place 0).toNat < indices.size)
    {i : Nat} {proposer : ValidatorIndex}
    (found : proposerSearch preset fork validators indices shuffled seed i = .ok proposer) :
    proposer ∈ indices := by
  -- The candidate of every step is one of the indices.
  have candidateMem : ∀ j, indices.getD (shuffled.getD (j % indices.size) 0).toNat 0 ∈ indices := by
    intro j
    have lt := positions _ (Nat.mod_lt j nonempty)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem lt, Option.getD_some]
    exact Array.getElem_mem lt
  -- Each step either returns its candidate or moves closer to the end of the counter.
  obtain ⟨left, leftEq⟩ : ∃ left, left = 2 ^ 64 - i := ⟨_, rfl⟩
  induction left using Nat.strongRecOn generalizing i with
  | _ left ih =>
    unfold proposerSearch at found
    simp only [bind, Except.bind, pure, Except.pure] at found
    split at found
    · split at found
      · cases found
      split at found
      · cases found
        exact candidateMem i
      split at found
      · exact ih (2 ^ 64 - (i + 1)) (by omega) found rfl
      · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at found
    · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at found

/-- A proposer is one of the indices it is drawn from. -/
theorem mem_of_computeProposerIndex {state : BeaconState preset fork}
    {indices : Array ValidatorIndex} {seed : Bytes32} {proposer : ValidatorIndex}
    (computed : computeProposerIndex state indices seed = .ok proposer) :
    proposer ∈ indices := by
  unfold computeProposerIndex at computed
  by_cases empty : indices.size = 0
  · simp [empty, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed
  by_cases fits : indices.size < 2 ^ 64
  · simp only [empty, fits, ↓reduceIte] at computed
    have sizeEq : indices.size.toUInt64.toNat = indices.size := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
    refine mem_of_proposerSearch (Nat.pos_of_ne_zero empty) (fun place lt => ?_) computed
    have entry := computeShuffledPermutation_getD_lt (preset := preset) (seed := seed)
      (count := indices.size.toUInt64) (place := place) (by rw [sizeEq]; exact lt)
    rwa [sizeEq] at entry
  · simp [empty, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed

/-- Before Fulu, the proposer of a slot is active in the epoch of the state. -/
theorem mem_getActiveValidatorIndices_of_getBeaconProposerIndex
    {state : BeaconState preset fork} (beforeFulu : ¬.fusaka ≤ fork)
    {proposer : ValidatorIndex} (computed : getBeaconProposerIndex state = .ok proposer) :
    proposer ∈ getActiveValidatorIndices state (getCurrentEpoch state) := by
  simp only [getBeaconProposerIndex, beforeFulu, ↓reduceDIte, bind, Except.bind] at computed
  split at computed
  · cases computed
  simpa using mem_of_computeProposerIndex computed

/-- A domain always has a value. -/
theorem getDomain_total (config : Config) (state : BeaconState preset fork)
    (domainType : DomainType) (epoch : Option Epoch) :
    ∃ domain, getDomain config state domainType epoch = .ok domain := by
  unfold getDomain
  obtain ⟨domain, computed⟩ := computeDomain_total config domainType
    (if epoch.getD (getCurrentEpoch state) < state.forkVersions.epoch then
      state.forkVersions.previousVersion else state.forkVersions.currentVersion)
    state.genesisValidatorsRoot
  exact ⟨domain, by simp only [computed]; rfl⟩

/-- A write to a circular buffer of nonzero length replaces the entry at position `i mod n`. -/
theorem writeCircular_of_ne_zero {α : Type} {n : UInt64} (buffer : Vector α n.toNat)
    (i : UInt64) (value : α) (nonzero : n ≠ 0) :
    writeCircular buffer i value =
      .ok (buffer.set (i % n).toNat value (toNat_mod_lt nonzero)) := by
  simp [writeCircular, nonzero]

/-- A write to a circular buffer of length zero is a division-by-zero error. -/
theorem writeCircular_zero {α : Type} (buffer : Vector α (0 : UInt64).toNat) (i : UInt64)
    (value : α) : writeCircular buffer i value = .error (.arith .divisionByZero) := by
  simp [writeCircular]

/-- A write to a circular buffer is read back at the position it wrote. -/
theorem readCircular_writeCircular {α : Type} {n : UInt64} {buffer written : Vector α n.toNat}
    {i : UInt64} {value : α} (computed : writeCircular buffer i value = .ok written) :
    readCircular written i = .ok value := by
  unfold writeCircular at computed
  split at computed
  · cases computed
  · next nonzero =>
    cases computed
    simp [readCircular, nonzero]

/-- A write to a circular buffer leaves the entry at every other position unchanged. -/
theorem readCircular_writeCircular_of_ne {α : Type} {n : UInt64}
    {buffer written : Vector α n.toNat} {i j : UInt64} {value : α}
    (computed : writeCircular buffer i value = .ok written) (other : i % n ≠ j % n) :
    readCircular written j = readCircular buffer j := by
  unfold writeCircular at computed
  split at computed
  · cases computed
  · next nonzero =>
    cases computed
    have differ : i.toNat % n.toNat ≠ j.toNat % n.toNat := by
      rw [← UInt64.toNat_mod, ← UInt64.toNat_mod]
      exact fun same => other (UInt64.toNat_inj.mp same)
    simp [readCircular, nonzero, differ]

end EthLib.Consensus
