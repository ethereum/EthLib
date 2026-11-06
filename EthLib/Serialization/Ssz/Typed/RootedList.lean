module

public import EthLib.Serialization.Ssz.Typed.ForkKind
public import EthLib.Serialization.Ssz.Typed.Rooted

/-!
# Typed SSZ values: fork-chosen lists that keep their Merkle tree

A rooted fork-chosen list holds its elements together with every level of their Merkle tree.

Before the switch fork the list has a limit, and its tree has the depth that the limit sets.

Writing or appending one element then rehashes only the path above its leaf.

The root is the top of the levels with the length mixed in.

From the switch on, the list is progressive and keeps no levels yet, so its root is hashed in full.

A list of basic elements packs them into shared leaves, several to a leaf.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType

/--
The levels a fork-chosen list keeps over its leaves.

Before the switch, they are the levels of the tree whose depth the capacity in leaves sets.

From the switch on, there are none.
-/
def forkListLevels (switch fork : Fork) (capacity : Nat) (leaves : Array Bytes) :
    List (Array Bytes) :=
  if fork < switch then buildLevels 0 leaves (depthFor capacity) else []

/-- A list with a limit before the switch fork and a progressive list from it on, with its tree. -/
structure RootedForkList (switch fork : Fork) (α : Type) [SszType α] (limit : Nat) where
  /-- The elements, in order. -/
  data : Array α
  /-- Before the switch, the count stays within the limit. -/
  bound : fork < switch → data.size ≤ limit
  /-- The levels of the tree, from the leaves up to the top node. -/
  levels : List (Array Bytes)
  /-- The levels are those of the tree over the leaves of the elements. -/
  built : levels = forkListLevels switch fork (leafCapacity α limit) (sequenceLeaves data)

namespace RootedForkList

variable {switch fork : Fork} {α : Type} [SszType α] {limit : Nat}

/-- A list with the levels of its tree, built from the leaves up. -/
def ofData (data : Array α) (bound : fork < switch → data.size ≤ limit) :
    RootedForkList switch fork α limit :=
  ⟨data, bound, forkListLevels switch fork (leafCapacity α limit) (sequenceLeaves data), rfl⟩

/-- The fork-chosen list with the same elements, without its tree. -/
def toForkList (l : RootedForkList switch fork α limit) : ForkList switch fork α limit :=
  ⟨l.data, l.bound⟩

/-- A fork-chosen list with the levels of its tree. -/
def ofForkList (l : ForkList switch fork α limit) : RootedForkList switch fork α limit :=
  ofData l.data l.bound

/-- The list with the element at an index replaced, its tree rehashed along one path. -/
def set (l : RootedForkList switch fork α limit) (index : Nat) (a : α)
    (inside : index < l.data.size := by get_elem_tactic) : RootedForkList switch fork α limit :=
  ⟨l.data.set index a inside, by simpa using l.bound,
    updateLevels 0 (leafIndex α index) (leafNode (l.data.set index a inside) index a) l.levels, by
    rw [l.built, forkListLevels, forkListLevels]
    split
    · rw [updateLevels_buildLevels _ 0 _ (leafIndex_le (by omega))]
      congr 1
      symm
      apply sequenceLeaves_write (by simp [inside]) (.inl (by simp))
      intro other differ
      simp [Ne.symm differ]
    · rfl⟩

/-- The list with one more element at its end, its tree rehashed along one path. -/
def push (l : RootedForkList switch fork α limit) (a : α)
    (room : fork < switch → l.data.size < limit) : RootedForkList switch fork α limit :=
  ⟨l.data.push a, fun before => by simpa using Nat.succ_le_of_lt (room before),
    updateLevels 0 (leafIndex α l.data.size) (leafNode (l.data.push a) l.data.size a) l.levels, by
    rw [l.built, forkListLevels, forkListLevels]
    split
    · rw [updateLevels_buildLevels _ 0 _ (leafIndex_le (Nat.le_refl _))]
      congr 1
      symm
      apply sequenceLeaves_write (by simp) (.inr ⟨by simp, rfl⟩)
      intro other differ
      simp only [Array.getElem?_push, ite_eq_right differ]
    · rfl⟩

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

From the switch on, it is hashed as the fork-chosen list is.
-/
instance {switch fork : Fork} {α : Type} [SszType α] {limit : Nat} :
    SszType (RootedForkList switch fork α limit) where
  desc := desc (ForkList switch fork α limit)
  toValue l := toValue l.toForkList
  ofValue value := ofForkList <$> ofValue value
  root l :=
    if fork < switch then
      .ok (mixIn (topOfLevels (depthFor (leafCapacity α limit)) l.levels) (lengthWord l.data.size))
    else Ssz.hashTreeRoot (desc (ForkList switch fork α limit)) (toValue l.toForkList)

end EthLib.Serialization.Ssz
