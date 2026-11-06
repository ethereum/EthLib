module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.Shuffle

/-!
# Proofs: the shuffle is a permutation

Each round of swap-or-not undoes itself on the indices below the count.

So running the rounds again in reverse order gives each index back.

Hence the shuffled list holds each index below the count exactly once.

The committees cut from a list of indices then hold each of its entries exactly once.

So each entry of the list is in one of the committees.

When the list has no repeat, no entry is in two committees.

Each member of any committee that has a value is one of the indices.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

namespace Shuffle

/-- The reflection of the reflection of an index about a pivot is the index. -/
theorem reflect_reflect {count pivot index : Nat} (pivotLt : pivot < count)
    (indexLt : index < count) :
    (pivot + count - (pivot + count - index) % count) % count = index := by
  by_cases le : index ≤ pivot
  · -- The reflection is `pivot - index`, below the count.
    have first : (pivot + count - index) % count = pivot - index := by
      rw [show pivot + count - index = (pivot - index) + count by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [first, show pivot + count - (pivot - index) = index + count by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt indexLt]
  · -- The reflection is `pivot + count - index`, below the count.
    have first : (pivot + count - index) % count = pivot + count - index :=
      Nat.mod_eq_of_lt (by omega)
    rw [first, show pivot + count - (pivot + count - index) = index by omega,
      Nat.mod_eq_of_lt indexLt]

/-- Swap-or-not undoes itself on an index below the count, when the pivot is below it. -/
theorem swapOrNot_swapOrNot {count pivot index : Nat} {bit : Nat → Bool}
    (pivotLt : pivot < count) (indexLt : index < count) :
    swapOrNot count pivot bit (swapOrNot count pivot bit index) = index := by
  have back := reflect_reflect pivotLt indexLt
  unfold swapOrNot
  dsimp only
  by_cases swaps : bit (max index ((pivot + count - index) % count)) = true
  · -- The pair reads the same bit from its other member, since the maximum is symmetric.
    simp only [swaps, ↓reduceIte]
    rw [back, Nat.max_comm]
    simp [swaps]
  · simp [swaps]

/-- The pivot of a round is below the count, when the count is positive. -/
theorem pivot_lt {seed : Bytes32} {roundNumber count : Nat} (positive : 0 < count) :
    pivot seed roundNumber count < count :=
  Nat.mod_lt _ positive

/-- One round of swap-or-not undoes itself on an index below the count. -/
theorem indexRound_indexRound {seed : Bytes32} {count roundNumber index : Nat}
    (lt : index < count) :
    indexRound seed count roundNumber (indexRound seed count roundNumber index) = index :=
  swapOrNot_swapOrNot (pivot_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) lt)) lt

/-- The rounds in reverse order, which undo the shuffle. -/
def unshuffledIndex (rounds : Nat) (seed : Bytes32) (count index : Nat) : Nat :=
  (List.range rounds).reverse.foldl
    (fun index roundNumber => indexRound seed count roundNumber index) index

/-- Rounds keep an index below the count. -/
theorem foldl_indexRound_lt {seed : Bytes32} {count : Nat} (rounds : List Nat) {index : Nat}
    (lt : index < count) :
    rounds.foldl (fun index roundNumber => indexRound seed count roundNumber index) index <
      count := by
  induction rounds generalizing index with
  | nil => exact lt
  | cons first rest ih => exact ih (indexRound_lt lt)

/-- Rounds, then the same rounds in reverse order, give an index below the count back. -/
theorem foldl_reverse_foldl {seed : Bytes32} {count : Nat} (rounds : List Nat) {index : Nat}
    (lt : index < count) :
    rounds.reverse.foldl (fun index roundNumber => indexRound seed count roundNumber index)
        (rounds.foldl (fun index roundNumber => indexRound seed count roundNumber index) index) =
      index := by
  induction rounds generalizing index with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.foldl_append, List.foldl_nil]
    rw [ih (indexRound_lt lt), indexRound_indexRound lt]

/-- The reverse rounds undo the shuffle of an index below the count. -/
theorem unshuffledIndex_shuffledIndex {rounds : Nat} {seed : Bytes32} {count index : Nat}
    (lt : index < count) :
    unshuffledIndex rounds seed count (shuffledIndex rounds seed count index) = index :=
  foldl_reverse_foldl _ lt

/-- The shuffle undoes the reverse rounds on an index below the count. -/
theorem shuffledIndex_unshuffledIndex {rounds : Nat} {seed : Bytes32} {count index : Nat}
    (lt : index < count) :
    shuffledIndex rounds seed count (unshuffledIndex rounds seed count index) = index := by
  have := foldl_reverse_foldl (seed := seed) (count := count) (List.range rounds).reverse lt
  rwa [List.reverse_reverse] at this

/-- The shuffle keeps an index below the count. -/
theorem shuffledIndex_lt {rounds : Nat} {seed : Bytes32} {count index : Nat}
    (lt : index < count) : shuffledIndex rounds seed count index < count :=
  foldl_indexRound_lt _ lt

/-- The reverse rounds keep an index below the count. -/
theorem unshuffledIndex_lt {rounds : Nat} {seed : Bytes32} {count index : Nat}
    (lt : index < count) : unshuffledIndex rounds seed count index < count :=
  foldl_indexRound_lt _ lt

/-- Two indices below the count with one shuffled position are equal. -/
theorem shuffledIndex_injective {rounds : Nat} {seed : Bytes32} {count first second : Nat}
    (firstLt : first < count) (secondLt : second < count)
    (same : shuffledIndex rounds seed count first = shuffledIndex rounds seed count second) :
    first = second := by
  rw [← unshuffledIndex_shuffledIndex (rounds := rounds) (seed := seed) firstLt, same,
    unshuffledIndex_shuffledIndex secondLt]

end Shuffle

/-- The shuffled list is a permutation of the indices below the count. -/
theorem computeShuffledPermutation_perm (preset : Preset) (count : UInt64) (seed : Bytes32) :
    List.Perm ((computeShuffledPermutation preset count seed).toList.map UInt64.toNat)
      (List.range count.toNat) := by
  let shuffle := Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed count.toNat
  -- The list is the shuffle of each index below the count.
  have listed : (computeShuffledPermutation preset count seed).toList.map UInt64.toNat =
      (List.range count.toNat).map shuffle := by
    apply List.ext_getElem?
    intro index
    by_cases lt : index < count.toNat
    · have fits : shuffle index < 2 ^ 64 :=
        Nat.lt_trans (Shuffle.shuffledIndex_lt lt) count.toNat_lt
      simp [List.getElem?_map, computeShuffledPermutation_getElem lt, lt, shuffle,
        Nat.mod_eq_of_lt fits]
    · have size := computeShuffledPermutation_size preset count seed
      simp [List.getElem?_map, lt]
      omega
  rw [listed]
  apply (List.perm_ext_iff_of_nodup _ List.nodup_range).mpr
  · intro index
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨original, lt, rfl⟩
      exact Shuffle.shuffledIndex_lt lt
    · intro lt
      exact ⟨_, Shuffle.unshuffledIndex_lt lt, Shuffle.shuffledIndex_unshuffledIndex lt⟩
  · rw [List.Nodup, List.pairwise_map]
    exact List.nodup_range.imp_of_mem fun firstMem secondMem differ same =>
      differ (Shuffle.shuffledIndex_injective (List.mem_range.mp firstMem)
        (List.mem_range.mp secondMem) same)

namespace Shuffle

/-- The indices in shuffled order: at each place, the index at the shuffled position. -/
def shuffledIndices (preset : Preset) (indices : Array ValidatorIndex) (seed : Bytes32) :
    List ValidatorIndex :=
  let shuffled := computeShuffledPermutation preset (UInt64.ofNat indices.size) seed
  (List.range indices.size).map fun place => indices.getD (shuffled.getD place 0).toNat 0

/-- The indices in shuffled order are a permutation of the indices. -/
theorem shuffledIndices_perm (preset : Preset) {indices : Array ValidatorIndex} (seed : Bytes32)
    (fits : indices.size < 2 ^ 64) :
    List.Perm (shuffledIndices preset indices seed) indices.toList := by
  have perm := computeShuffledPermutation_perm preset (UInt64.ofNat indices.size) seed
  have size : (UInt64.ofNat indices.size).toNat = indices.size := by
    simp [Nat.mod_eq_of_lt fits]
  rw [size] at perm
  have size' := computeShuffledPermutation_size preset (UInt64.ofNat indices.size) seed
  rw [size] at size'
  -- Reading the indices at a permutation of their positions permutes them.
  have read := perm.map fun position => indices.getD position 0
  rw [List.map_map] at read
  have whole : (List.range indices.size).map (fun position => indices.getD position 0) =
      indices.toList := by
    apply List.ext_getElem (by simp)
    intro place lt _
    simp only [List.getElem_map, List.getElem_range, Array.getD_eq_getD_getElem?,
      Array.getElem_toList]
    simp at lt
    simp [lt]
  rw [whole] at read
  refine List.Perm.trans ?_ read
  apply List.Perm.of_eq
  apply List.ext_getElem (by simp [shuffledIndices, size'])
  intro place lt _
  simp only [shuffledIndices, List.length_map, List.length_range] at lt
  simp [shuffledIndices, Function.comp_def, Array.getD_eq_getD_getElem?, size', lt]

/-- Slices between the bounds of consecutive parts, from bound zero, tile the list. -/
theorem flatMap_slices {α : Type} (list : List α) (bound : Nat → Nat) (zero : bound 0 = 0)
    (mono : ∀ part, bound part ≤ bound (part + 1)) (parts : Nat) :
    (List.range parts).flatMap (fun part =>
        (list.drop (bound part)).take (bound (part + 1) - bound part)) =
      list.take (bound parts) := by
  induction parts with
  | zero => simp [zero]
  | succ parts ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, ← List.take_add,
      Nat.add_sub_cancel' (mono parts)]

end Shuffle

/-- Committee `index` of `count` is the slice of the shuffled indices between its bounds. -/
theorem computeCommittee_eq {preset : Preset} {indices : Array ValidatorIndex} {seed : Bytes32}
    {index count : UInt64} (lt : index < count)
    (fits : indices.size * count.toNat < 2 ^ 64) :
    computeCommittee preset indices seed index count =
      .ok (((Shuffle.shuffledIndices preset indices seed).drop
          (indices.size * index.toNat / count.toNat)).take
        (indices.size * (index.toNat + 1) / count.toNat -
          indices.size * index.toNat / count.toNat)).toArray := by
  have natLt : index.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp lt
  have positive : count ≠ 0 := by
    intro zero
    simp [zero] at natLt
  have bound : indices.size * (index.toNat + 1) ≤ indices.size * count.toNat :=
    Nat.mul_le_mul_left _ natLt
  have stopLe : indices.size * (index.toNat + 1) / count.toNat ≤ indices.size := by
    exact Nat.div_le_of_le_mul (Nat.le_trans bound (Nat.le_of_eq (Nat.mul_comm _ _)))
  have below : index.toNat + 1 < 2 ^ 64 := Nat.lt_of_le_of_lt natLt count.toNat_lt
  simp only [computeCommittee, positive, below, Nat.lt_of_le_of_lt bound fits, and_self,
    Nat.not_lt.mpr stopLe, and_false, ↓reduceIte]
  congr 2
  apply List.ext_getElem (by simp [Shuffle.shuffledIndices]; omega)
  intro place lt _
  simp [Shuffle.shuffledIndices]

/-- A committee with a position past the length of the indices fails.

The error names the first such position, as the spec's bound check on the shuffle does. -/
theorem computeCommittee_past_end {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {index count : UInt64} (positive : count ≠ 0)
    (below : index.toNat + 1 < 2 ^ 64) (fits : indices.size * (index.toNat + 1) < 2 ^ 64)
    (nonempty : indices.size * index.toNat / count.toNat <
      indices.size * (index.toNat + 1) / count.toNat)
    (past : indices.size < indices.size * (index.toNat + 1) / count.toNat) :
    computeCommittee preset indices seed index count =
      .error (.indexOutOfRange
        (UInt64.ofNat (max (indices.size * index.toNat / count.toNat) indices.size))
        (UInt64.ofNat indices.size)) := by
  simp only [computeCommittee, positive, below, fits, and_self, nonempty, past, ↓reduceIte]
  rfl

/-- A committee with an empty range of positions is empty, wherever the range lies. -/
theorem computeCommittee_empty {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {index count : UInt64} (positive : count ≠ 0)
    (below : index.toNat + 1 < 2 ^ 64) (fits : indices.size * (index.toNat + 1) < 2 ^ 64)
    (empty : indices.size * (index.toNat + 1) / count.toNat ≤
      indices.size * index.toNat / count.toNat) :
    computeCommittee preset indices seed index count = .ok #[] := by
  simp only [computeCommittee, positive, below, fits, and_self, Nat.not_lt.mpr empty,
    false_and, ↓reduceIte, Nat.sub_eq_zero_of_le empty]
  rfl

namespace Shuffle

/-- Committee `index` of `count`, as a slice of the shuffled indices. -/
def committeeSlice (preset : Preset) (indices : Array ValidatorIndex) (seed : Bytes32)
    (count index : Nat) : List ValidatorIndex :=
  ((shuffledIndices preset indices seed).drop (indices.size * index / count)).take
    (indices.size * (index + 1) / count - indices.size * index / count)

end Shuffle

/-- Each committee index below the count gives its slice, when the bounds fit in 64 bits. -/
theorem computeCommittee_of_mem {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {count : UInt64} (fits : indices.size * count.toNat < 2 ^ 64) :
    ∀ index ∈ List.range count.toNat,
      computeCommittee preset indices seed (UInt64.ofNat index) count =
        .ok (Shuffle.committeeSlice preset indices seed count.toNat index).toArray := by
  intro index mem
  have lt := List.mem_range.mp mem
  have natEq : (UInt64.ofNat index).toNat = index :=
    Nat.mod_eq_of_lt (Nat.lt_trans lt count.toNat_lt)
  have ult : UInt64.ofNat index < count := by
    rw [UInt64.lt_iff_toNat_lt, natEq]
    exact lt
  rw [computeCommittee_eq ult fits, natEq]
  rfl

/-- All committees exist, when the bounds fit in 64 bits. -/
theorem computeCommittee_mapM {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {count : UInt64} (fits : indices.size * count.toNat < 2 ^ 64) :
    (List.range count.toNat).mapM
        (fun index => computeCommittee preset indices seed (UInt64.ofNat index) count) =
      .ok ((List.range count.toNat).map fun index =>
        (Shuffle.committeeSlice preset indices seed count.toNat index).toArray) :=
  Base.mapM_eq_ok_map (computeCommittee_of_mem fits)

/-- The `count` committees cut from a list of indices partition it.

Their concatenation, in order, is a permutation of the list. -/
theorem computeCommittee_partition {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {count : UInt64} {committees : List (Array ValidatorIndex)}
    (fits : indices.size * count.toNat < 2 ^ 64) (positive : 0 < count)
    (computed : (List.range count.toNat).mapM
      (fun index => computeCommittee preset indices seed (UInt64.ofNat index) count) =
        .ok committees) :
    List.Perm (committees.flatMap Array.toList) indices.toList := by
  have sizeFits : indices.size < 2 ^ 64 := by
    have : 1 ≤ count.toNat := UInt64.lt_iff_toNat_lt.mp positive
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ this) fits
  let bound := fun part => indices.size * part / count.toNat
  have listed := computeCommittee_mapM (preset := preset) (seed := seed) fits
  rw [computed, Except.ok.injEq] at listed
  subst listed
  rw [List.flatMap_map]
  simp only [Shuffle.committeeSlice]
  rw [Shuffle.flatMap_slices _ bound (by simp [bound])
    (fun part => Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_succ part)))]
  have whole : bound count.toNat = indices.size :=
    Nat.mul_div_cancel _ (UInt64.lt_iff_toNat_lt.mp positive)
  have length : (Shuffle.shuffledIndices preset indices seed).length = indices.size := by
    simp [Shuffle.shuffledIndices]
  rw [whole, ← length, List.take_length]
  exact Shuffle.shuffledIndices_perm preset seed sizeFits

/-- The shuffled position read at a place below the count is below the count. -/
theorem computeShuffledPermutation_getD_lt {preset : Preset} {count : UInt64} {seed : Bytes32}
    {place : Nat} (lt : place < count.toNat) :
    ((computeShuffledPermutation preset count seed).getD place 0).toNat < count.toNat := by
  have below := Shuffle.shuffledIndex_lt (rounds := preset.SHUFFLE_ROUND_COUNT.toNat)
    (seed := seed) lt
  rw [Array.getD_eq_getD_getElem?, computeShuffledPermutation_getElem lt, Option.getD_some,
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans below count.toNat_lt)]
  exact below

/-- Each member of a committee is one of the indices it is cut from. -/
theorem mem_of_computeCommittee {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {index count : UInt64} {committee : Array ValidatorIndex}
    (computed : computeCommittee preset indices seed index count = .ok committee)
    {member : ValidatorIndex} (mem : member ∈ committee) : member ∈ indices := by
  unfold computeCommittee at computed
  by_cases zero : count = 0
  · simp [zero, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed
  by_cases fits : index.toNat + 1 < 2 ^ 64 ∧ indices.size * (index.toNat + 1) < 2 ^ 64
  · by_cases past : indices.size * index.toNat / count.toNat <
        indices.size * (index.toNat + 1) / count.toNat ∧
        indices.size < indices.size * (index.toNat + 1) / count.toNat
    · simp [zero, fits, past, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed
    · simp [zero, fits, past, pure, Except.pure] at computed
      subst computed
      simp only [List.mem_toArray, List.mem_map, List.mem_range] at mem
      obtain ⟨i, lt, rfl⟩ := mem
      have sizeFits : indices.size < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) fits.2
      have sizeEq : (UInt64.ofNat indices.size).toNat = indices.size := by
        rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt sizeFits]
      have entry := computeShuffledPermutation_getD_lt (preset := preset) (seed := seed)
        (count := UInt64.ofNat indices.size)
        (place := indices.size * index.toNat / count.toNat + i) (by rw [sizeEq]; omega)
      rw [sizeEq, Array.getD_eq_getD_getElem?] at entry
      rw [Array.getElem?_eq_getElem entry, Option.getD_some]
      exact Array.getElem_mem entry
  · simp [zero, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at computed

/-- Each entry of a list of indices is in one of the `count` committees cut from it.

The bounds must fit in 64 bits, and the count must be positive. -/
theorem exists_mem_computeCommittee {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {count : UInt64} (fits : indices.size * count.toNat < 2 ^ 64)
    (positive : 0 < count) {member : ValidatorIndex} (mem : member ∈ indices) :
    ∃ index < count.toNat, ∃ committee,
      computeCommittee preset indices seed (UInt64.ofNat index) count = .ok committee ∧
        member ∈ committee := by
  have perm := computeCommittee_partition fits positive
    (computeCommittee_mapM (preset := preset) (seed := seed) fits)
  have inFlat := perm.symm.mem_iff.mp (Array.mem_toList_iff.mpr mem)
  obtain ⟨committee, listed, inCommittee⟩ := List.mem_flatMap.mp inFlat
  obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp listed
  exact ⟨index, List.mem_range.mp inRange, _,
    computeCommittee_of_mem fits index inRange, Array.mem_toList_iff.mp inCommittee⟩

/-- No entry of a list of indices without repeats is in two of the committees cut from it.

Two committees below the count that both hold one entry are the same committee.

The bounds must fit in 64 bits. -/
theorem eq_of_mem_computeCommittee {preset : Preset} {indices : Array ValidatorIndex}
    {seed : Bytes32} {count : UInt64} (nodup : indices.toList.Nodup)
    (fits : indices.size * count.toNat < 2 ^ 64) {first second : Nat}
    (firstLt : first < count.toNat) (secondLt : second < count.toNat)
    {firstCommittee secondCommittee : Array ValidatorIndex}
    (firstComputed :
      computeCommittee preset indices seed (UInt64.ofNat first) count = .ok firstCommittee)
    (secondComputed :
      computeCommittee preset indices seed (UInt64.ofNat second) count = .ok secondCommittee)
    {member : ValidatorIndex} (firstMem : member ∈ firstCommittee)
    (secondMem : member ∈ secondCommittee) : first = second := by
  have positive : 0 < count := UInt64.lt_iff_toNat_lt.mpr (Nat.zero_lt_of_lt firstLt)
  let slice := fun index =>
    (Shuffle.committeeSlice preset indices seed count.toNat index).toArray.toList
  -- The concatenated committees are a permutation of the list, so they have no repeat either.
  have perm := computeCommittee_partition fits positive
    (computeCommittee_mapM (preset := preset) (seed := seed) fits)
  rw [List.flatMap_map] at perm
  have apart := (List.pairwise_flatMap.mp (perm.nodup_iff.mpr nodup)).2
  have firstEq := computeCommittee_of_mem (preset := preset) (seed := seed) fits first
    (List.mem_range.mpr firstLt)
  have secondEq := computeCommittee_of_mem (preset := preset) (seed := seed) fits second
    (List.mem_range.mpr secondLt)
  rw [firstComputed, Except.ok.injEq] at firstEq
  rw [secondComputed, Except.ok.injEq] at secondEq
  subst firstEq secondEq
  -- Committees at two different places of the range share no entry.
  have split : ∀ i j, i < count.toNat → j < count.toNat → i < j →
      ∀ x ∈ slice i, ∀ y ∈ slice j, x ≠ y := by
    intro i j iLt jLt lt
    have := List.pairwise_iff_getElem.mp apart i j (by simpa using iLt) (by simpa using jLt) lt
    simpa using this
  have firstIn : member ∈ slice first := Array.mem_toList_iff.mpr firstMem
  have secondIn : member ∈ slice second := Array.mem_toList_iff.mpr secondMem
  rcases Nat.lt_trichotomy first second with lt | same | gt
  · exact absurd rfl (split first second firstLt secondLt lt member firstIn member secondIn)
  · exact same
  · exact absurd rfl (split second first secondLt firstLt gt member secondIn member firstIn)

end EthLib.Consensus
