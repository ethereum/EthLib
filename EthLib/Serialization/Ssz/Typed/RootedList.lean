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

From the switch on, the list is progressive and keeps no levels yet, so its root is hashed in full.

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

/-- A list with a limit before the switch fork and a progressive list from it on, with its tree. -/
structure RootedForkList (switch fork : Fork) (α : Type) [SszType α] (limit : Nat) where
  /-- The elements, in order. -/
  data : Array α
  /-- Before the switch, the count stays within the limit. -/
  bound : fork < switch → data.size ≤ limit
  /-- The levels of the tree, from the leaves up to the top node. -/
  levels : List (Array Bytes)
  /-- The levels are those of the tree over the leaves of the elements. -/
  built : levels = forkListLevels switch fork (sequenceLeaves data)

namespace RootedForkList

variable {switch fork : Fork} {α : Type} [SszType α] {limit : Nat}

/-- A list with the levels of its tree, built from the leaves up. -/
def ofData (data : Array α) (bound : fork < switch → data.size ≤ limit) :
    RootedForkList switch fork α limit :=
  ⟨data, bound, forkListLevels switch fork (sequenceLeaves data), rfl⟩

/-- The fork-chosen list with the same elements, without its tree. -/
def toForkList (l : RootedForkList switch fork α limit) : ForkList switch fork α limit :=
  ⟨l.data, l.bound⟩

/-- A fork-chosen list with the levels of its tree. -/
def ofForkList (l : ForkList switch fork α limit) : RootedForkList switch fork α limit :=
  ofData l.data l.bound

/-- The list with the element at an index replaced, its tree rehashed along one path. -/
def set (l : RootedForkList switch fork α limit) (index : Nat) (a : α)
    (inside : index < l.data.size := by get_elem_tactic) : RootedForkList switch fork α limit :=
  -- Read the levels before the write, so that the write finds the elements unshared.
  let levels := l.levels
  let data := l.data.set index a inside
  ⟨data, by simpa [data] using l.bound,
    updateLevels 0 (leafIndex α index) (leafNode data index a) levels, by
    simp only [data, levels]
    rw [l.built, forkListLevels, forkListLevels]
    split
    · rw [size_sequenceLeaves, size_sequenceLeaves, Array.size_set,
        updateLevels_buildLevels _ 0 _ (leafIndex_le (by omega))]
      congr 1
      symm
      apply sequenceLeaves_write (by simp [inside]) (.inl (by simp))
      intro other differ
      simp [Ne.symm differ]
    · rfl⟩

/--
The list with one more element at its end, its tree rehashed along one path.

If the new element needs a new leaf that the tree cannot hold, the tree first grows one level.
-/
def push (l : RootedForkList switch fork α limit) (a : α)
    (room : fork < switch → l.data.size < limit) : RootedForkList switch fork α limit :=
  let size := l.data.size
  let depth := depthFor (leafCount α size)
  -- From the switch on there are no levels to raise.
  let raised := if fork < switch then
    raiseLevels depth l.levels (depthFor (leafCount α (size + 1)) - depth) else l.levels
  -- Every read of the old list comes first, so that the append finds the elements unshared.
  let data := l.data.push a
  ⟨data, fun before => by simpa [data] using Nat.succ_le_of_lt (room before),
    updateLevels 0 (leafIndex α size) (leafNode data size a) raised, by
    have grows := depthFor_le_depthFor (leafCount_le_succ α l.data.size)
    simp only [raised, depth, data, size]
    rw [l.built, forkListLevels, forkListLevels]
    by_cases before : fork < switch
    · simp only [before, ↓reduceIte]
      rw [size_sequenceLeaves, size_sequenceLeaves, Array.size_push,
        raiseLevels_buildLevels_leaves, Nat.add_sub_cancel' grows,
        updateLevels_buildLevels _ 0 _ (leafIndex_le (Nat.le_refl _))]
      congr 1
      symm
      apply sequenceLeaves_write (by simp) (.inr ⟨by simp, rfl⟩)
      intro other differ
      simp only [Array.getElem?_push, ite_eq_right differ]
    · simp only [before, ↓reduceIte, updateLevels]⟩

/-- Two rooted lists with the same elements are the same, since the elements fix the levels. -/
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

From the switch on, it is hashed as the fork-chosen list is.
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
    else Ssz.hashTreeRoot (desc (ForkList switch fork α limit)) (toValue l.toForkList)

end EthLib.Serialization.Ssz
