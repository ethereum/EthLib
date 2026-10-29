import EthLib.Consensus.Ssz.Merkle.Tree
import EthLib.Consensus.Ssz.Type.Paths
import EthLib.Consensus.Proofs.Ssz.Merkle.Merkleize

/-! What a bounded root costs in hashes, and why a large capacity barely adds to it. -/

namespace EthLib.Consensus.Ssz

/--
Hashes a bounded root costs, counted along the recursion that produces it.

A subtree beginning past the data is answered from the precomputed table, so it costs nothing.

A leaf is read rather than hashed.

Every other node pays one hash to fold its two halves together.
-/
def subtreeCost (chunks : Array Bytes) (depth start : Nat) : Nat :=
  if start ≥ chunks.size then 0
  else
    match depth with
    | 0 => 0
    | d + 1 => 1 + subtreeCost chunks d start + subtreeCost chunks d (start + 2 ^ d)

/-- A leaf costs nothing, whether it holds a chunk or reads as padding. -/
private theorem subtreeCost_leaf (chunks : Array Bytes) (start : Nat) :
    subtreeCost chunks 0 start = 0 := by
  rw [subtreeCost.eq_def]
  split <;> rfl

/-- A subtree wholly past the data is a lookup, at any depth. -/
private theorem subtreeCost_past (chunks : Array Bytes) (depth start : Nat)
    (past : chunks.size ≤ start) : subtreeCost chunks depth start = 0 := by
  rw [subtreeCost.eq_def]
  simp [past]

/-- A node that reaches the data pays one hash and charges both halves. -/
private theorem subtreeCost_node (chunks : Array Bytes) (depth start : Nat)
    (inside : start < chunks.size) :
    subtreeCost chunks (depth + 1) start
      = 1 + subtreeCost chunks depth start + subtreeCost chunks depth (start + 2 ^ depth) := by
  rw [subtreeCost.eq_def]
  simp [Nat.not_le.mpr inside]

/-- No subtree costs more than materializing all of its leaves would. -/
theorem subtreeCost_le_width (chunks : Array Bytes) (depth start : Nat) :
    subtreeCost chunks depth start + 1 ≤ 2 ^ depth := by
  induction depth generalizing start with
  | zero => simp [subtreeCost_leaf]
  | succ depth ih =>
    by_cases past : chunks.size ≤ start
    · rw [subtreeCost_past chunks (depth + 1) start past]
      simpa using Nat.one_le_two_pow
    · have left := ih start
      have right := ih (start + 2 ^ depth)
      rw [subtreeCost_node chunks depth start (Nat.not_le.mp past), Nat.pow_succ]
      omega

/--
A subtree that lies inside the data reaches every one of its leaves.

Its cost is then one hash short of its width, which is the price of the naive walk.
-/
theorem subtreeCost_saturated (chunks : Array Bytes) (depth start : Nat)
    (filled : start + 2 ^ depth ≤ chunks.size) :
    subtreeCost chunks depth start + 1 = 2 ^ depth := by
  induction depth generalizing start with
  | zero => simp [subtreeCost_leaf]
  | succ depth ih =>
    have half : 0 < 2 ^ depth := Nat.two_pow_pos depth
    rw [Nat.pow_succ] at filled
    have left := ih start (by omega)
    have right := ih (start + 2 ^ depth) (by omega)
    rw [subtreeCost_node chunks depth start (by omega), Nat.pow_succ]
    omega

/--
Above the point where the data already fits, each level costs exactly one hash.

The sibling on every such level is an all-zero subtree, which the table answers.
-/
private theorem subtreeCost_climb (chunks : Array Bytes) (start below : Nat)
    (inside : start < chunks.size) (covered : chunks.size ≤ start + 2 ^ below) (extra : Nat) :
    subtreeCost chunks (below + extra) start = extra + subtreeCost chunks below start := by
  induction extra with
  | zero => simp
  | succ extra ih =>
    have wider : 2 ^ below ≤ 2 ^ (below + extra) := Nat.pow_le_pow_right (by omega) (by omega)
    have sibling : subtreeCost chunks (below + extra) (start + 2 ^ (below + extra)) = 0 :=
      subtreeCost_past chunks _ _ (by omega)
    rw [show below + (extra + 1) = below + extra + 1 from rfl,
      subtreeCost_node chunks (below + extra) start inside, sibling, ih]
    omega

/-- The width chosen for a nonempty count is under twice that count. -/
private theorem two_pow_depthFor_lt (count : Nat) (nonempty : 0 < count) :
    2 ^ depthFor count < 2 * count := by
  cases height : depthFor count with
  | zero =>
    simp only [Nat.pow_zero]
    omega
  | succ shallower =>
    have tight : 2 ^ shallower < count := Nat.lt_of_not_le fun above => by
      have := depthFor_le_of_le_two_pow above
      omega
    rw [Nat.pow_succ]
    omega

/-- A larger capacity never asks for a shallower tree. -/
private theorem depthFor_le_depthFor {count capacity : Nat} (room : count ≤ capacity) :
    depthFor count ≤ depthFor capacity :=
  depthFor_le_of_le_two_pow (Nat.le_trans room (le_two_pow_depthFor capacity))

/--
Merkleizing nonempty data costs under twice the chunk count plus the logarithm of the width.

The capacity enters only through that logarithm, however far it exceeds the data.

Each term pays for one regime: the fold over the data, and the climb above it.
-/
theorem subtreeCost_lt (chunks : Array Bytes) (capacity : Nat) (nonempty : 0 < chunks.size)
    (room : chunks.size ≤ capacity) :
    subtreeCost chunks (depthFor capacity) 0
      < 2 * chunks.size + Nat.log2 (nextPow2 capacity) := by
  have height : Nat.log2 (nextPow2 capacity) = depthFor capacity := by
    simp only [nextPow2, Nat.log2_two_pow]
  have data : depthFor chunks.size ≤ depthFor capacity := depthFor_le_depthFor room
  have covered : chunks.size ≤ 0 + 2 ^ depthFor chunks.size := by
    have := le_two_pow_depthFor chunks.size
    omega
  have levels : depthFor chunks.size + (depthFor capacity - depthFor chunks.size)
      = depthFor capacity := by omega
  have climbed := subtreeCost_climb chunks 0 (depthFor chunks.size) nonempty covered
    (depthFor capacity - depthFor chunks.size)
  rw [levels] at climbed
  have fold := subtreeCost_le_width chunks (depthFor chunks.size) 0
  have narrow := two_pow_depthFor_lt chunks.size nonempty
  rw [height, climbed]
  omega

/--
A walk that materializes every leaf of the capacity's tree costs one hash short of the width.

That is what the precomputed table saves, and it grows with the capacity rather than the data.
-/
theorem subtreeCost_all_leaves (chunks : Array Bytes) (capacity : Nat)
    (filled : nextPow2 capacity ≤ chunks.size) :
    subtreeCost chunks (Nat.log2 (nextPow2 capacity)) 0 + 1 = nextPow2 capacity := by
  have height : Nat.log2 (nextPow2 capacity) = depthFor capacity := by
    simp only [nextPow2, Nat.log2_two_pow]
  rw [height]
  simp only [nextPow2] at filled ⊢
  exact subtreeCost_saturated chunks (depthFor capacity) 0 (by omega)

/--
Root of a bounded subtree paired with the number of folds computing it performs.

The recursion is the one `subtreeAt` runs, carrying the running count alongside the root.
-/
def subtreeAtCounted (chunks : Array Bytes) (depth start : Nat) : Bytes × Nat :=
  if start ≥ chunks.size then (zeroSubtree depth, 0)
  else
    match depth with
    | 0 => (padded zeroChunk chunks start, 0)
    | d + 1 =>
      (combine (subtreeAtCounted chunks d start).1 (subtreeAtCounted chunks d (start + 2 ^ d)).1,
        1 + (subtreeAtCounted chunks d start).2 + (subtreeAtCounted chunks d (start + 2 ^ d)).2)

/-- Counting the folds leaves the root the implementation produces untouched. -/
theorem subtreeAtCounted_fst (chunks : Array Bytes) :
    ∀ depth start, (subtreeAtCounted chunks depth start).1 = subtreeAt chunks depth start := by
  intro depth start
  -- Both recursions branch on the same tests, so unfolding the implementation closes every case.
  fun_induction subtreeAtCounted chunks depth start <;> rw [subtreeAt.eq_def] <;> grind

/-- The folds counted along that recursion are exactly the modelled cost. -/
theorem subtreeAtCounted_snd (chunks : Array Bytes) :
    ∀ depth start, (subtreeAtCounted chunks depth start).2 = subtreeCost chunks depth start := by
  intro depth start
  -- Both recursions branch on the same tests, so unfolding the cost closes every case.
  fun_induction subtreeAtCounted chunks depth start <;> rw [subtreeCost.eq_def] <;> grind

end EthLib.Consensus.Ssz
