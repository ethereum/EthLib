module

public import EthLib.Consensus.Shuffle

/-!
# Proofs: the shuffle moves each index on its own

A round hashes each bucket of positions once, for all indices.

It gives each index the value that one round of swap-or-not gives it alone.

So the shuffled list holds, at each index, the result of every round on that index.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- Two errors with one code come from one constructor. -/
theorem ShuffleError.code_injective (e₁ e₂ : ShuffleError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ShuffleError.code] at h; exact absurd h (by decide))

namespace Shuffle

/-- One round of swap-or-not on one index, hashing the bucket of its position directly. -/
def indexRound (seed : Bytes32) (count roundNumber index : Nat) : Nat :=
  swapOrNot count (pivot seed roundNumber count)
    (fun position => bitAt (bucketBits seed roundNumber (position / 256)) position) index

/-- Every round of a preset on one index, in order. -/
def shuffledIndex (rounds : Nat) (seed : Bytes32) (count index : Nat) : Nat :=
  (List.range rounds).foldl (fun index roundNumber => indexRound seed count roundNumber index) index

/-- Swap-or-not keeps an index below the count. -/
theorem swapOrNot_lt {count pivot index : Nat} {bit : Nat → Bool} (lt : index < count) :
    swapOrNot count pivot bit index < count := by
  unfold swapOrNot
  dsimp only
  split
  · exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) lt)
  · exact lt

/-- One round of an index below the count keeps it below the count. -/
theorem indexRound_lt {seed : Bytes32} {count roundNumber index : Nat} (lt : index < count) :
    indexRound seed count roundNumber index < count :=
  swapOrNot_lt lt

/-- A round on indices below the count is the round of each index on its own. -/
theorem round_eq_map {seed : Bytes32} {count roundNumber : Nat} {indices : Array Nat}
    (bounded : ∀ index ∈ indices, index < count) :
    round seed count roundNumber indices = indices.map (indexRound seed count roundNumber) := by
  unfold round indexRound
  apply Array.map_congr_left
  intro index mem
  have lt := bounded index mem
  unfold swapOrNot
  dsimp only
  -- The position read is below the count, so its bucket is one of the hashed buckets.
  have flipLt : (pivot seed roundNumber count + count - index) % count < count :=
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) lt)
  have bucketLt : max index ((pivot seed roundNumber count + count - index) % count) / 256 <
      count / 256 + 1 := by
    have : max index ((pivot seed roundNumber count + count - index) % count) < count :=
      Nat.max_lt.mpr ⟨lt, flipLt⟩
    have := Nat.div_le_div_right (c := 256) (Nat.le_of_lt this)
    omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, bucketLt, dite_true,
    Option.getD_some]

/-- A round keeps every index below the count. -/
theorem round_bounded {seed : Bytes32} {count roundNumber : Nat} {indices : Array Nat}
    (bounded : ∀ index ∈ indices, index < count) :
    ∀ index ∈ round seed count roundNumber indices, index < count := by
  rw [round_eq_map bounded]
  intro index mem
  obtain ⟨original, member, rfl⟩ := Array.mem_map.mp mem
  exact indexRound_lt (bounded original member)

/-- Rounds on indices below the count are the rounds of each index on its own. -/
theorem foldl_round_eq_map {seed : Bytes32} {count : Nat} (rounds : List Nat)
    {indices : Array Nat} (bounded : ∀ index ∈ indices, index < count) :
    rounds.foldl (fun indices roundNumber => round seed count roundNumber indices) indices =
      indices.map fun index =>
        rounds.foldl (fun index roundNumber => indexRound seed count roundNumber index) index := by
  induction rounds generalizing indices with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldl_cons]
    rw [ih (round_bounded bounded), round_eq_map bounded, Array.map_map]
    rfl

end Shuffle

/-- The shuffled list holds, at each index below the count, every round applied to that index. -/
theorem computeShuffledPermutation_getElem {preset : Preset} {count : UInt64} {seed : Bytes32}
    {index : Nat} (lt : index < count.toNat) :
    (computeShuffledPermutation preset count seed)[index]? =
      some (UInt64.ofNat
        (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed count.toNat index)) := by
  unfold computeShuffledPermutation
  rw [Shuffle.foldl_round_eq_map _ (fun i mem => Array.mem_range.mp mem)]
  simp [lt, Shuffle.shuffledIndex]

/-- The shuffled list has one entry for each index below the count. -/
theorem computeShuffledPermutation_size (preset : Preset) (count : UInt64) (seed : Bytes32) :
    (computeShuffledPermutation preset count seed).size = count.toNat := by
  unfold computeShuffledPermutation
  rw [Shuffle.foldl_round_eq_map _ (fun i mem => Array.mem_range.mp mem)]
  simp

/-- The shuffled position of an index below the count is every round applied to it. -/
theorem computeShuffledIndex_eq {preset : Preset} {index count : UInt64} {seed : Bytes32}
    (lt : index < count) :
    computeShuffledIndex preset index count seed =
      .ok (UInt64.ofNat
        (Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed count.toNat index.toNat)) := by
  have natLt : index.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp lt
  simp [computeShuffledIndex, lt, Array.getD_eq_getD_getElem?,
    computeShuffledPermutation_getElem natLt]

/-- An index at or above the count has no shuffled position. -/
theorem computeShuffledIndex_of_le {preset : Preset} {index count : UInt64} {seed : Bytes32}
    (le : count ≤ index) :
    computeShuffledIndex preset index count seed = .error (.indexOutOfRange index count) := by
  simp [computeShuffledIndex, UInt64.not_lt.mpr le]

end EthLib.Consensus
