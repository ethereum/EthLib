module

public import EthLib.Serialization.Ssz.Typed.ForkKind
public import EthLib.Serialization.Ssz.Typed.Rooted

/-!
# Typed SSZ values: fork-chosen lists that keep their Merkle tree

A rooted fork-chosen list holds its elements together with every level of their Merkle tree.

Before the switch fork the list has a limit.

Its levels reach only as high as its leaves need, so a write costs a hash per level of that tree.

Writing or appending one element then rehashes only the path above its leaf.

An append that fills the tree first adds one level on top.

The root lifts the top of the levels to the depth that the limit sets, with zero subtrees.

Then it mixes in the length.

From the switch on, the list is progressive.

Its leaves then fill a spine of trees of one, four, sixteen leaves and so on.

The list keeps the levels of each of these trees.

A write rehashes the path in the one tree that holds its leaf.

An append past the last tree opens a new one.

The root folds the tops of the trees along the spine, then mixes in the length.

A list of basic elements packs them into shared leaves, several to a leaf.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType

/--
The levels a fork-chosen list keeps over its leaves.

Before the switch, they are the levels of the least deep tree that holds the leaves.

From the switch on, there are none.
-/
def forkListLevels (switch fork : Fork) (leaves : Array Bytes) : List (Array Bytes) :=
  if fork < switch then buildLevels 0 leaves (depthFor leaves.size) else []

/--
The levels of the trees on a progressive spine, from the tree that starts at a given leaf.

That tree holds `4 ^ level` leaves, so `2 * level` levels lie above them.

Each next tree holds four times as many leaves, and the trees go on while leaves remain.
-/
def spineLevels (leaves : Array Bytes) (start level : Nat) : List (List (Array Bytes)) :=
  if start < leaves.size then
    buildLevels 0 (leaves.extract start (start + 4 ^ level)) (2 * level)
      :: spineLevels leaves (start + 4 ^ level) (level + 1)
  else []
termination_by leaves.size - start
decreasing_by
  have : 0 < 4 ^ level := Nat.pos_of_neZero _
  omega

/--
The levels of the spine trees after one leaf is written, replaced or appended.

The position counts from the start of the first tree given.

Only the tree that holds the position changes, along one path.

A position just past the last tree opens a new tree that holds the one leaf.
-/
def spineWrite (level position : Nat) (node : Bytes) :
    List (List (Array Bytes)) → List (List (Array Bytes))
  | [] => [buildLevels 0 #[node] (2 * level)]
  | levels :: rest =>
    if position < 4 ^ level then updateLevels 0 position node levels :: rest
    else levels :: spineWrite (level + 1) (position - 4 ^ level) node rest

/-- The root of a progressive spine from the levels of its trees, closed by a zero node. -/
def spineRoot (level : Nat) : List (List (Array Bytes)) → Bytes
  | [] => zeroChunk
  | levels :: rest => combine (topOfLevels (2 * level) levels) (spineRoot (level + 1) rest)

/-- The levels of the spine trees of a fork-chosen list: none before the switch. -/
def forkListSpine (switch fork : Fork) (leaves : Array Bytes) : List (List (Array Bytes)) :=
  if fork < switch then [] else spineLevels leaves 0 0

/-- An entry of a slice is the entry at the same offset from its start, inside the slice. -/
theorem getElem?_extract_of {xs : Array Bytes} {start stop : Nat} (index : Nat) :
    (xs.extract start stop)[index]?
      = if index < stop - start then xs[start + index]? else none := by
  rw [Array.getElem?_extract]
  by_cases inside : index < stop - start
  · rw [ite_eq_left inside]
    split
    · rfl
    · exact (Array.getElem?_eq_none (by omega)).symm
  · rw [ite_eq_right inside, ite_eq_right (by omega)]

/-- The spine trees from a leaf on read only the leaves from there on. -/
theorem spineLevels_congr {leaves other : Array Bytes} :
    ∀ {start : Nat} (level : Nat), (∀ index, start ≤ index → leaves[index]? = other[index]?) →
      spineLevels leaves start level = spineLevels other start level := by
  intro start level same
  induction start, level using spineLevels.induct leaves with
  | case1 start level inside ih =>
    -- The first leaf of the tree is present in both, so both have the tree.
    have there : start < other.size := by
      have here := same start (Nat.le_refl _)
      rw [Array.getElem?_eq_getElem inside] at here
      exact (Array.getElem?_eq_some_iff.mp here.symm).1
    have slice :
        leaves.extract start (start + 4 ^ level) = other.extract start (start + 4 ^ level) := by
      apply Array.ext_getElem?
      intro index
      rw [getElem?_extract_of, getElem?_extract_of, same (start + index) (Nat.le_add_right _ _)]
    rw [spineLevels.eq_1 leaves, spineLevels.eq_1 other, ite_eq_left inside, ite_eq_left there,
      slice, ih fun index past => same index (Nat.le_trans (Nat.le_add_right _ _) past)]
  | case2 start level outside =>
    have gone : ¬start < other.size := by
      intro there
      have here := same start (Nat.le_refl _)
      rw [Array.getElem?_eq_none (Nat.not_lt.mp outside), Array.getElem?_eq_getElem there] at here
      cases here
    rw [spineLevels.eq_1 leaves, spineLevels.eq_1 other, ite_eq_right outside, ite_eq_right gone]

/-- Writing a leaf inside a slice, or just past the leaves, writes the slice at its offset. -/
theorem extract_writeEntry {leaves : Array Bytes} {start stop position : Nat} (node : Bytes)
    (after : start ≤ position) (to : position < stop) (within : position ≤ leaves.size) :
    (writeEntry leaves position node).extract start stop
      = writeEntry (leaves.extract start stop) (position - start) node := by
  have room : position - start ≤ (leaves.extract start stop).size := by
    rw [Array.size_extract]
    omega
  apply Array.ext_getElem?
  intro index
  rw [getElem?_writeEntry room, getElem?_extract_of, getElem?_extract_of,
    getElem?_writeEntry within]
  by_cases same : position - start = index
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left same]
  · rw [ite_eq_right same]
    split
    · rw [ite_eq_right (by omega)]
    · rfl

/--
Writing the spine trees at a leaf gives the spine trees over the written leaves.

The leaf lies inside the leaves or just past them, and not before the first tree given.
-/
theorem spineWrite_spineLevels (leaves : Array Bytes) (node : Bytes) :
    ∀ {start : Nat} (level : Nat) {position : Nat}, start ≤ position → position ≤ leaves.size →
      spineWrite level (position - start) node (spineLevels leaves start level)
        = spineLevels (writeEntry leaves position node) start level := by
  intro start level position after within
  have written : ∀ index, (writeEntry leaves position node)[index]?
      = if position = index then some node else leaves[index]? := getElem?_writeEntry within node
  induction start, level using spineLevels.induct leaves with
  | case1 start level inside ih =>
    have grown : start < (writeEntry leaves position node).size := by
      unfold writeEntry
      split <;> simp <;> omega
    rw [spineLevels.eq_1 leaves, ite_eq_left inside, spineLevels.eq_1 (writeEntry _ _ _),
      ite_eq_left grown, spineWrite]
    by_cases here : position - start < 4 ^ level
    · -- The tree that holds the leaf takes the write, and the trees after it read none of it.
      rw [ite_eq_left here, extract_writeEntry node after (by omega) within,
        updateLevels_buildLevels _ 0 _ (by simp; omega)]
      congr 1
      apply spineLevels_congr
      intro index past
      rw [written, ite_eq_right (by omega)]
    · -- The leaf lies in a later tree, so this one reads none of it.
      rw [ite_eq_right here, show position - start - 4 ^ level = position - (start + 4 ^ level)
        by omega, ih (by omega)]
      congr 2
      apply Array.ext_getElem?
      intro index
      rw [getElem?_extract_of, getElem?_extract_of]
      split
      · rw [written, ite_eq_right (by omega)]
      · rfl
  | case2 start level outside =>
    -- The leaf is the first past the leaves, and it opens a tree of its own.
    have first : position = start := by omega
    subst first
    have last : position = leaves.size := by omega
    have pushed : writeEntry leaves position node = leaves.push node := by
      simp [writeEntry, last]
    have wide : 0 < 4 ^ level := Nat.pos_of_neZero _
    have slice : (leaves.push node).extract position (position + 4 ^ level) = #[node] := by
      apply Array.ext_getElem?
      intro index
      rw [getElem?_extract_of, Nat.add_sub_cancel_left]
      rcases Nat.eq_zero_or_pos index with zero | positive
      · subst zero
        simp [last, wide]
      · rw [Array.getElem?_eq_none (show (leaves.push node).size ≤ position + index by
            simp; omega),
          Array.getElem?_eq_none (show (#[node] : Array Bytes).size ≤ index by simp; omega)]
        split <;> rfl
    rw [spineLevels.eq_1 leaves, ite_eq_right outside, Nat.sub_self, spineWrite, pushed,
      spineLevels.eq_1 (leaves.push node), ite_eq_left (by simp; omega), slice,
      spineLevels.eq_1 (leaves.push node), ite_eq_right (by simp; omega)]

/-- A list with a limit before the switch fork and a progressive list from it on, with its tree. -/
structure RootedForkList (switch fork : Fork) (α : Type) [SszType α] (limit : Nat) where
  /-- The elements, in order. -/
  data : Array α
  /-- Before the switch, the count stays within the limit. -/
  bound : fork < switch → data.size ≤ limit
  /-- Before the switch, the levels of the tree, from the leaves up to the top node. -/
  levels : List (Array Bytes)
  /-- The levels are those of the tree over the leaves of the elements. -/
  built : levels = forkListLevels switch fork (sequenceLeaves data)
  /-- From the switch on, the levels of each tree on the spine, in spine order. -/
  spine : List (List (Array Bytes))
  /-- The spine trees are those over the leaves of the elements. -/
  spineBuilt : spine = forkListSpine switch fork (sequenceLeaves data)

namespace RootedForkList

variable {switch fork : Fork} {α : Type} [SszType α] {limit : Nat}

/-- A list with the levels of its trees, built from the leaves up. -/
def ofData (data : Array α) (bound : fork < switch → data.size ≤ limit) :
    RootedForkList switch fork α limit :=
  let leaves := sequenceLeaves data
  ⟨data, bound, forkListLevels switch fork leaves, rfl, forkListSpine switch fork leaves, rfl⟩

/-- The fork-chosen list with the same elements, without its tree. -/
def toForkList (l : RootedForkList switch fork α limit) : ForkList switch fork α limit :=
  ⟨l.data, l.bound⟩

/-- A fork-chosen list with the levels of its trees. -/
def ofForkList (l : ForkList switch fork α limit) : RootedForkList switch fork α limit :=
  ofData l.data l.bound

/-- The list with the element at an index replaced, its tree rehashed along one path. -/
def set (l : RootedForkList switch fork α limit) (index : Nat) (a : α)
    (inside : index < l.data.size := by get_elem_tactic) : RootedForkList switch fork α limit :=
  -- Read the trees before the write, so that the write finds the elements unshared.
  let levels := l.levels
  let spine := l.spine
  let data := l.data.set index a inside
  let node := leafNode data index a
  -- Only one of the two holds trees: the levels before the switch, the spine from it on.
  let before := fork < switch
  have leaves : sequenceLeaves data
      = writeEntry (sequenceLeaves l.data) (leafIndex α index) node := by
    apply sequenceLeaves_write (by simp [data, inside]) (.inl (by simp [data]))
    intro other differ
    simp [data, Ne.symm differ]
  ⟨data, by simpa [data] using l.bound,
    if before then updateLevels 0 (leafIndex α index) node levels else levels, by
    simp only [levels, before]
    rw [l.built, forkListLevels, forkListLevels]
    split
    · rw [size_sequenceLeaves, size_sequenceLeaves, Array.size_set,
        updateLevels_buildLevels _ 0 _ (leafIndex_le (by omega)), leaves]
    · rfl,
    if before then spine else spineWrite 0 (leafIndex α index) node spine, by
    simp only [spine, before]
    rw [l.spineBuilt, forkListSpine, forkListSpine]
    split
    · rfl
    · rw [leaves, ← spineWrite_spineLevels _ _ 0 (Nat.zero_le _) (leafIndex_le (by omega)),
        Nat.sub_zero]⟩

/--
The list with one more element at its end, its tree rehashed along one path.

Before the switch, a new leaf that the tree cannot hold first grows the tree by one level.

From the switch on, a leaf past the last spine tree opens a new tree.
-/
def push (l : RootedForkList switch fork α limit) (a : α)
    (room : fork < switch → l.data.size < limit) : RootedForkList switch fork α limit :=
  let size := l.data.size
  let depth := depthFor (leafCount α size)
  let levels := l.levels
  let spine := l.spine
  -- Every read of the old list comes first, so that the append finds the elements unshared.
  let data := l.data.push a
  let node := leafNode data size a
  -- Only one of the two holds trees: the levels before the switch, the spine from it on.
  let before := fork < switch
  have leaves : sequenceLeaves data
      = writeEntry (sequenceLeaves l.data) (leafIndex α size) node := by
    apply sequenceLeaves_write (by simp [data]) (.inr ⟨by simp [data], rfl⟩)
    intro other differ
    simp only [data, Array.getElem?_push, ite_eq_right differ]
  ⟨data, fun early => by simpa [data] using Nat.succ_le_of_lt (room early),
    if before then updateLevels 0 (leafIndex α size) node
      (raiseLevels depth levels (depthFor (leafCount α (size + 1)) - depth))
    else levels, by
    have grows := depthFor_le_depthFor (leafCount_le_succ α l.data.size)
    simp only [levels, depth, size, before]
    rw [l.built, forkListLevels, forkListLevels]
    split
    · rw [size_sequenceLeaves, size_sequenceLeaves, Array.size_push,
        raiseLevels_buildLevels_leaves, Nat.add_sub_cancel' grows,
        updateLevels_buildLevels _ 0 _ (leafIndex_le (Nat.le_refl _)), leaves]
    · rfl,
    if before then spine else spineWrite 0 (leafIndex α size) node spine, by
    simp only [spine, before]
    rw [l.spineBuilt, forkListSpine, forkListSpine]
    split
    · rfl
    · rw [leaves, ← spineWrite_spineLevels _ _ 0 (Nat.zero_le _) (leafIndex_le (Nat.le_refl _)),
        Nat.sub_zero]⟩

/-- Two rooted lists with the same elements are the same, since the elements fix the trees. -/
theorem ext {l m : RootedForkList switch fork α limit} (same : l.data = m.data) : l = m := by
  cases l
  cases m
  subst same
  simp_all

instance [DecidableEq α] : DecidableEq (RootedForkList switch fork α limit) := fun l m =>
  if same : l.data = m.data then isTrue (ext same)
  else isFalse fun equal => same (equal ▸ rfl)

end RootedForkList

open RootedForkList

/--
The fork-chosen list, which reads its root from the top of its levels before the switch.

The top is first raised to the depth that the limit sets.

From the switch on, it folds the tops of the spine trees.

Either way, the length is mixed in last.
-/
instance {switch fork : Fork} {α : Type} [SszType α] {limit : Nat} :
    SszType (RootedForkList switch fork α limit) where
  desc := desc (ForkList switch fork α limit)
  toValue l := toValue l.toForkList
  ofValue value := ofForkList <$> ofValue value
  root l :=
    if fork < switch then
      let depth := depthFor (leafCount α l.data.size)
      let full := depthFor (leafCapacity α limit)
      .ok (mixIn (topOfLevels full (raiseLevels depth l.levels (full - depth)))
        (lengthWord l.data.size))
    else .ok (mixIn (spineRoot 0 l.spine) (lengthWord l.data.size))

end EthLib.Serialization.Ssz
