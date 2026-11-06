module

public import EthLib.Serialization.Ssz.Typed.Collections

/-!
# Typed SSZ values: vectors that keep their Merkle tree

A rooted vector holds its elements together with every level of their Merkle tree.

Writing one element then rehashes only the path above its leaf, one node per level.

The root is read from the top level, and the proofs show that it is the root of the vector.

Each leaf is the root of one element, as in the tree of a vector of composite elements.

A vector of basic elements packs them into shared leaves, so its root does not use the levels.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
The parent of entries `2 * index` and `2 * index + 1` of a level whose subtrees have a height.

An entry past the level is the zero subtree of that height.
-/
def parentAt (height : Nat) (level : Array Bytes) (index : Nat) : Bytes :=
  combine (level[2 * index]?.getD (zeroSubtree height))
    (level[2 * index + 1]?.getD (zeroSubtree height))

/-- The level above a level whose subtrees have a height: each pair of entries hashed together. -/
def pairUp (height : Nat) (level : Array Bytes) : Array Bytes :=
  -- An odd last entry is paired with the zero subtree.
  Array.ofFn (n := (level.size + 1) / 2) fun index => parentAt height level index

/--
The given level, whose subtrees have a height, then the given count of levels above it.

The first level is the one given, and each next one pairs up the entries of the one below.
-/
def buildLevels (height : Nat) (level : Array Bytes) : Nat → List (Array Bytes)
  | 0 => [level]
  | above + 1 => level :: buildLevels (height + 1) (pairUp height level) above

/--
The levels after one entry of the first level is replaced by a node.

Each level above changes in one entry, the parent of the entry changed below it.
-/
def updateLevels (height position : Nat) (node : Bytes) : List (Array Bytes) → List (Array Bytes)
  | [] => []
  | level :: rest =>
    let level := level.setIfInBounds position node
    match rest with
    -- The top level has no parent to rehash.
    | [] => [level]
    | rest =>
      level :: updateLevels (height + 1) (position / 2) (parentAt height level (position / 2)) rest

/-- Pairing up a level after one entry changed changes the one entry above it. -/
theorem pairUp_set (height : Nat) (level : Array Bytes) {position : Nat}
    (inside : position < level.size) (node : Bytes) :
    pairUp height (level.set position node inside)
      = (pairUp height level).setIfInBounds (position / 2)
          (parentAt height (level.set position node inside) (position / 2)) := by
  apply Array.ext
  · simp [pairUp]
  · intro index left right
    simp only [pairUp, Array.size_ofFn, Array.size_set] at left
    rw [Array.getElem_setIfInBounds (by simp only [pairUp, Array.size_ofFn]; omega)]
    split
    · next same =>
      subst same
      simp [pairUp]
    · -- The two entries under another parent are not the one that changed.
      next other =>
      simp only [pairUp, Array.getElem_ofFn, parentAt, Array.getElem?_set]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Updating the levels of a tree gives the levels of the tree over the updated first level. -/
theorem updateLevels_buildLevels :
    ∀ (above height : Nat) (level : Array Bytes) {position : Nat}
      (inside : position < level.size) (node : Bytes),
      updateLevels height position node (buildLevels height level above)
        = buildLevels height (level.set position node inside) above
  | 0, height, level, position, inside, node => by
    simp [buildLevels, updateLevels, Array.setIfInBounds, inside]
  | above + 1, height, level, position, inside, node => by
    have higher : position / 2 < (pairUp height level).size := by
      simp only [pairUp, Array.size_ofFn]
      omega
    rw [buildLevels, buildLevels, pairUp_set height level inside, Array.setIfInBounds,
      dite_eq_left higher, ← updateLevels_buildLevels above (height + 1) _ higher]
    -- The levels above the first are never empty, so the update goes on up.
    obtain ⟨first, rest, nonempty⟩ :
        ∃ first rest, buildLevels (height + 1) (pairUp height level) above = first :: rest := by
      cases above <;> exact ⟨_, _, rfl⟩
    rw [nonempty]
    simp only [updateLevels, Array.setIfInBounds, dite_eq_left inside]

/-- The top node of a tree from its levels, or the zero subtree of its depth if it has no leaf. -/
def topOfLevels (depth : Nat) (levels : List (Array Bytes)) : Bytes :=
  ((levels.getLast?.bind fun top => top[0]?)).getD (zeroSubtree depth)

open SszType

/-- The leaf of an element in a rooted vector: its root, or the zero node if it has none. -/
def leafRoot {α : Type} [SszType α] (a : α) : Bytes :=
  -- A lawful element always has a root, so the zero node never stands in.
  match root a with
  | .ok node => node
  | .error _ => zeroChunk

/-- The leaves of a rooted vector: the roots of its elements. -/
def leafRoots {α : Type} [SszType α] {length : Nat} (elements : Vector α length) : Array Bytes :=
  -- A loop over the indices: a map over a generic element type keeps one stack frame per element.
  Array.ofFn fun index : Fin length => leafRoot elements[index]

/-- `Vector[α, length]`, with every level of its Merkle tree. -/
structure RootedVector (α : Type) [SszType α] (length : Nat) where
  /-- The elements, in order. -/
  elements : Vector α length
  /-- The levels of the tree, from the leaves up to the top node. -/
  levels : List (Array Bytes)
  /-- The levels are those of the tree over the roots of the elements. -/
  built : levels = buildLevels 0 (leafRoots elements) (depthFor length)

namespace RootedVector

variable {α : Type} [SszType α] {length : Nat}

/-- A vector with the levels of its tree, built from the leaves up. -/
def ofVector (elements : Vector α length) : RootedVector α length :=
  ⟨elements, buildLevels 0 (leafRoots elements) (depthFor length), rfl⟩

/-- The element at an index. -/
def get (v : RootedVector α length) (index : Nat) (inside : index < length := by get_elem_tactic) :
    α :=
  v.elements[index]

instance : GetElem (RootedVector α length) Nat α fun _ index => index < length where
  getElem v index inside := v.get index inside

/-- The vector with the element at an index replaced, its tree rehashed along one path. -/
def set (v : RootedVector α length) (index : Nat) (a : α)
    (inside : index < length := by get_elem_tactic) : RootedVector α length :=
  ⟨v.elements.set index a inside, updateLevels 0 index (leafRoot a) v.levels, by
    have leaf : index < (leafRoots v.elements).size := by simp [leafRoots, inside]
    rw [v.built, updateLevels_buildLevels _ 0 _ leaf]
    congr 1
    apply Array.ext
    · simp [leafRoots]
    · intro other _ _
      simp only [leafRoots, Array.getElem_ofFn, Array.getElem_set]
      split <;> simp_all⟩

/-- The vector with the element at an index replaced, or the same vector past its end. -/
def set! (v : RootedVector α length) (index : Nat) (a : α) : RootedVector α length :=
  if inside : index < length then v.set index a inside else v

/-- Two rooted vectors with the same elements are the same, since the elements fix the levels. -/
theorem ext {v w : RootedVector α length} (same : v.elements = w.elements) : v = w := by
  cases v
  cases w
  subst same
  simp_all

instance [Repr α] : Repr (RootedVector α length) where
  reprPrec v := reprPrec v.elements

instance [DecidableEq α] : DecidableEq (RootedVector α length) := fun v w =>
  if same : v.elements = w.elements then isTrue (ext same)
  else isFalse fun equal => same (equal ▸ rfl)

end RootedVector

open RootedVector

/--
`Vector[α, length]`, which reads its root from the top of its levels.

A vector of basic elements packs them into shared leaves, so it hashes them as a vector does.
-/
instance {α : Type} [SszType α] {length : Nat} : SszType (RootedVector α length) where
  desc := desc (Vector α length)
  toValue v := toValue v.elements
  ofValue value := ofVector <$> ofValue value
  root v :=
    if (desc α).isBasic then Ssz.hashTreeRoot (desc (Vector α length)) (toValue v.elements)
    else .ok (topOfLevels (depthFor length) v.levels)

end EthLib.Serialization.Ssz
