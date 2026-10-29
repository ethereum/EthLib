import EthLib.Consensus.Ssz.Merkle.Tree
import EthLib.Consensus.Proofs.Ssz.Merkle.Merkleize

/-! Laws of the concrete SHA-256 trees: node widths, zero subtrees, and windowed roots. -/

namespace EthLib.Consensus.Ssz

/-- The table holds one entry per depth up to the one it was built for. -/
theorem zeroRootsUpTo_size (built : Nat) : (zeroRootsUpTo built).size = built + 1 := by
  induction built with
  -- The table opens with the zero node alone.
  | zero => rfl
  -- Every level after that pushes exactly one entry on the end.
  | succ built ih => simp [zeroRootsUpTo, ih]

/--
Every entry of the table is the zero subtree of its own depth.

This is what lets an empty subtree be answered by lookup.
The answer still means what the specification says it means.
-/
theorem zeroRootsUpTo_get (built : Nat) :
    ∀ depth, depth ≤ built →
      (zeroRootsUpTo built)[depth]?.getD zeroChunk = zeroRoot combine zeroChunk depth := by
  induction built with
  | zero =>
    -- Only depth zero fits, and the table opens with the zero node itself.
    intro depth holds
    obtain rfl : depth = 0 := by omega
    rfl
  | succ built ih =>
    intro depth holds
    -- Either the entry was already there before this level, or it is the one just added.
    by_cases below : depth < built + 1
    · -- A shallower entry was already in the table, and pushing on the end left it alone.
      simp only [zeroRootsUpTo, Array.getElem?_push, zeroRootsUpTo_size, ite_eq_right (Nat.ne_of_lt below)]
      exact ih depth (by omega)
    · -- The new entry folds the previous one against itself, which is the level above.
      obtain rfl : depth = built + 1 := by omega
      simp only [zeroRootsUpTo, Array.getElem?_push, zeroRootsUpTo_size, ite_eq_left, Option.getD_some, zeroRoot]
      -- The entry below it is already known to be the subtree one level down.
      rw [ih built (Nat.le_refl built)]

/-- Reading the table at any depth it covers gives the zero subtree of that depth. -/
theorem zeroRoots_get {depth : Nat} (covered : depth ≤ maxZeroDepth) :
    zeroRoots[depth]?.getD zeroChunk = zeroRoot combine zeroChunk depth :=
  -- The table was built through the requested depth, so its entry has the proved recursive meaning.
  zeroRootsUpTo_get maxZeroDepth depth covered

/-- Cached and uncached zero roots both describe the same perfect tree. -/
theorem zeroSubtree_eq (depth : Nat) :
    zeroSubtree depth = zeroRoot combine zeroChunk depth := by
  -- Inside the cache, the table theorem identifies the entry.
  by_cases covered : depth ≤ maxZeroDepth
  · have present : depth < zeroRoots.size := by
      simpa [zeroRoots, zeroRootsUpTo_size] using Nat.lt_succ_of_le covered
    simpa [zeroSubtree, Array.getElem?_eq_getElem present] using zeroRoots_get covered
  · -- Beyond the cache, the recursive definition supplies the root directly.
    have absent : zeroRoots[depth]? = none :=
      Array.getElem?_eq_none (by simp only [zeroRoots, zeroRootsUpTo_size]; omega)
    simp [zeroSubtree, absent]

/-- Packing uses the smallest number of whole nodes that can hold the bytes. -/
@[simp] theorem packBytes_size (data : Bytes) :
    (packBytes data).size = (data.size + bytesPerChunk - 1) / bytesPerChunk := by
  -- One array position is allocated for each window, including a final partial window.
  simp only [packBytes, Array.size_ofFn]

/-- Every packed node has exactly the width of a hash operand. -/
theorem packBytes_chunk_size (data : Bytes) (i : Nat) (within : i < (packBytes data).size) :
    ((packBytes data)[i]).size = bytesPerChunk := by
  -- An extracted window is at most one node wide, and zeros fill exactly its missing bytes.
  simp only [packBytes, Array.getElem_ofFn, Array.size_append, Array.size_replicate,
    Array.size_extract]
  omega

/-- Packing pads even the final partial node to one complete hash operand. -/
theorem packBytes_mem_size (data : Bytes) :
    ∀ chunk ∈ packBytes data, chunk.size = bytesPerChunk := by
  -- A member of the array sits at some position, and every position is one node wide.
  intro chunk member
  obtain ⟨i, within, rfl⟩ := Array.mem_iff_getElem.mp member
  exact packBytes_chunk_size data i within

/-- Bytes inside the payload retain their positions when divided into nodes. -/
theorem packBytes_get (data : Bytes) (i j : Nat) (node : i < (packBytes data).size)
    (position : j < bytesPerChunk) (payload : i * bytesPerChunk + j < data.size) :
    ((packBytes data)[i])[j]'(by rw [packBytes_chunk_size]; exact position) =
      data[i * bytesPerChunk + j] := by
  -- A position inside the original message lies in the extracted window, before its zero padding.
  simp only [packBytes, Array.getElem_ofFn]
  rw [Array.getElem_append_left (by simp only [Array.size_extract]; omega)]
  simp only [Array.getElem_extract]

/-- Positions beyond the original message are zero-filled in the final node. -/
theorem packBytes_padding (data : Bytes) (i j : Nat) (node : i < (packBytes data).size)
    (position : j < bytesPerChunk) (padding : data.size ≤ i * bytesPerChunk + j) :
    ((packBytes data)[i])[j]'(by rw [packBytes_chunk_size]; exact position) = 0 := by
  -- After the extracted bytes, the remaining positions belong to the explicit zero suffix.
  simp only [packBytes, Array.getElem_ofFn]
  rw [Array.getElem_append_right (by simp only [Array.size_extract]; omega)]
  exact Array.getElem_replicate _

/--
Cached subtree evaluation agrees with the full recursive tree.

An empty subtree may therefore use a table lookup without changing its mathematical root.
-/
theorem subtreeAt_eq_subtreeRoot (chunks : Array Bytes) :
    ∀ depth, ∀ start,
      subtreeAt chunks depth start
        = subtreeRoot combine depth (fun i => padded zeroChunk chunks (start + i)) := by
  intro depth
  -- The walk descends a level at a time, so the starting position stays quantified over.
  induction depth with
  | zero =>
    intro start
    unfold subtreeAt
    -- Either the leaf lies past the data, or it is read from it.
    split
    · -- Past the data, the lookup answers with the zero node the leaf would have read.
      rw [zeroSubtree_eq]
      simp [subtreeRoot, zeroRoot, padded, Array.getElem?_eq_none (show chunks.size ≤ start by omega)]
    · simp [subtreeRoot, padded]
  | succ depth ih =>
    intro start
    unfold subtreeAt
    -- Either the whole subtree lies past the data, or part of it does not.
    split
    · -- A subtree wholly past the data is the empty tree of its depth, by the lemma above.
      rw [zeroSubtree_eq]
      exact (subtreeRoot_padded_past_data combine zeroChunk (depth + 1) chunks (by omega)).symm
    · -- Otherwise both sides fold the same two halves, and the shift lines up.
      show combine (subtreeAt chunks depth start) (subtreeAt chunks depth (start + 2 ^ depth)) = _
      -- Each half is the same claim one level down, which the hypothesis gives twice.
      rw [subtreeRoot, ih start, ih (start + 2 ^ depth)]
      -- The right half starts a half-width along, which is the shift the fold applies.
      simp only [Nat.add_assoc, Nat.add_comm (2 ^ depth)]

/--
A subtree is its two halves combined, whatever sits under it.

This is the law a branch rests on: knowing one child and its sibling gives the parent.
-/
theorem subtreeAt_split (chunks : Array Bytes) {depth : Nat}
    (start : Nat) :
    subtreeAt chunks (depth + 1) start
      = combine (subtreeAt chunks depth start) (subtreeAt chunks depth (start + 2 ^ depth)) := by
  -- Either part of the subtree reaches the data, or none of it does.
  rw [subtreeAt]
  split
  · -- Wholly past the data, so both halves read the zero subtree one level down.
    rename_i past
    rw [subtreeAt.eq_def chunks depth start, ite_eq_left past, subtreeAt.eq_def chunks depth (start + 2 ^ depth),
      ite_eq_left (Nat.le_add_right_of_le past), zeroSubtree_eq, zeroSubtree_eq]
    rfl
  · rfl

/-- The bounded tree over a whole node array, read as the specification states it. -/
theorem subtreeAt_zero_eq (chunks : Array Bytes) {depth : Nat} :
    subtreeAt chunks depth 0 = subtreeRoot combine depth (padded zeroChunk chunks) := by
  -- Starting at position zero, the shift the walk applies is no shift at all.
  simp only [subtreeAt_eq_subtreeRoot chunks depth 0, Nat.zero_add]

/-- A subtree of height zero is the node at its position, or the zero node past the data. -/
theorem subtreeAt_leaf (chunks : Array Bytes) (start : Nat) :
    subtreeAt chunks 0 start = chunks[start]?.getD zeroChunk := by
  unfold subtreeAt
  split
  · -- Past the data, the cached zero tree of height zero is the zero node.
    rw [zeroSubtree_eq, Array.getElem?_eq_none (by omega)]
    rfl
  · rfl

/-- A subtree wholly past the data is the zero tree of its height. -/
theorem subtreeAt_past (chunks : Array Bytes) (depth start : Nat) (past : chunks.size ≤ start) :
    subtreeAt chunks depth start = zeroSubtree depth := by
  -- The walk checks for this case first and answers from the zero tree.
  unfold subtreeAt
  rw [ite_eq_left past]

/-- A subtree reads only the leaves under it. -/
theorem subtreeAt_congr (left right : Array Bytes) (depth leftStart rightStart : Nat)
    (same : ∀ i < 2 ^ depth, left[leftStart + i]? = right[rightStart + i]?) :
    subtreeAt left depth leftStart = subtreeAt right depth rightStart := by
  induction depth generalizing leftStart rightStart with
  | zero =>
    rw [subtreeAt_leaf, subtreeAt_leaf]
    have := same 0 (by simp)
    simp only [Nat.add_zero] at this
    rw [this]
  | succ depth ih =>
    -- Each half of the tree reads its own half of the leaves.
    rw [subtreeAt_split, subtreeAt_split]
    congr 1
    · exact ih leftStart rightStart fun i lt => same i (by rw [Nat.pow_succ]; omega)
    · exact ih _ _ fun i lt => by
        have := same (2 ^ depth + i) (by rw [Nat.pow_succ]; omega)
        rwa [← Nat.add_assoc, ← Nat.add_assoc] at this

/--
Merkleizing one window of the leaves gives the subtree standing over that window.

A proof reads a run of leaves rather than the whole tree, and this is why doing so is sound.
-/
theorem merkleizeBoundedUnchecked_window (chunks : Array Bytes) {depth : Nat}
    (start : Nat) :
    merkleizeBoundedUnchecked (chunks.extract start (start + 2 ^ depth)) (some (2 ^ depth))
      = .ok (subtreeAt chunks depth start) := by
  -- A window is no wider than it was asked to be, so the capacity check passes.
  have span : (chunks.extract start (start + 2 ^ depth)).size ≤ 2 ^ depth := by
    rw [Array.size_extract]
    generalize 2 ^ depth = width
    omega
  simp only [merkleizeBoundedUnchecked, ite_eq_right (Nat.not_lt.mpr span), depthFor_pow, pure, Except.pure,
    Except.ok.injEq]
  -- Both sides are the specification's tree, over leaf supplies that have yet to be compared.
  rw [subtreeAt_zero_eq _, subtreeAt_eq_subtreeRoot chunks depth start]
  refine subtreeRoot_congr combine depth ?_
  intro position below
  simp only [padded, Array.getElem?_extract]
  split
  · rfl
  · -- A position the window does not reach is one the whole tree reads as zero too.
    generalize 2 ^ depth = width at *
    simp [Array.getElem?_eq_none (show chunks.size ≤ start + position by omega)]

/--
Merkleizing a short buffer gives the root of one filled out with zeros.

This is the shortcut every implementation takes, stated about the code that takes it.
-/
theorem merkleizeBoundedUnchecked_append_zeros (chunks : Array Bytes)
    {count capacity : Nat}
    (room : chunks.size + count ≤ capacity) :
    merkleizeBoundedUnchecked (chunks ++ Array.replicate count zeroChunk) (some capacity)
      = merkleizeBoundedUnchecked chunks (some capacity) := by
  -- The padded buffer is longer, but still inside the capacity, so neither side refuses.
  simp only [merkleizeBoundedUnchecked, Array.size_append, Array.size_replicate, ite_eq_right (by omega : ¬ capacity < chunks.size + count),
    ite_eq_right (by omega : ¬ capacity < chunks.size)]
  -- Both roots are then the specification's, over leaf supplies already known equal.
  rw [subtreeAt_zero_eq _, subtreeAt_zero_eq _, padded_append_zeros]

/-- An empty buffer merkleizes to the zero subtree of the width it was given. -/
theorem merkleizeBoundedUnchecked_empty {capacity : Nat} :
    merkleizeBoundedUnchecked #[] (some capacity)
      = .ok (zeroRoot combine zeroChunk (depthFor capacity)) := by
  -- An empty buffer is under any capacity, so the merkleizer answers rather than refusing.
  simp only [merkleizeBoundedUnchecked, Array.size_empty, ite_eq_right (by omega : ¬ capacity < 0)]
  -- Every leaf then reads as zero, which is the constant supply the table entry stands for.
  rw [subtreeAt_zero_eq _, ← subtreeRoot_const_zero combine zeroChunk]
  rfl

/-- The executable progressive tree agrees with the hash-independent definition. -/
theorem merkleizeProgressiveUnchecked_eq (chunks : List Bytes) (level : Nat) :
    merkleizeProgressiveUnchecked chunks level = progressiveRoot combine zeroChunk chunks level := by
  -- Both definitions consume one level's leaves before continuing down the spine.
  induction chunks, level using merkleizeProgressiveUnchecked.induct with
  | case1 chunks level empty =>
    simp [merkleizeProgressiveUnchecked, progressiveRoot, empty]
  | case2 chunks level nonempty width ih =>
    rw [merkleizeProgressiveUnchecked, progressiveRoot, ite_eq_right nonempty, ite_eq_right nonempty]
    -- The bounded subtree equivalence is valid at every depth.
    dsimp only
    rw [subtreeAt_zero_eq, ih]

end EthLib.Consensus.Ssz
