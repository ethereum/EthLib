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
A level with the entry at a position replaced by a node.

At the end of the level, the node is appended instead.
-/
def writeEntry (level : Array Bytes) (position : Nat) (node : Bytes) : Array Bytes :=
  if inside : position < level.size then level.set position node inside else level.push node

/--
The levels after one entry of the first level is written, replaced or appended.

Each level above changes in one entry, the parent of the entry written below it.
-/
def updateLevels (height position : Nat) (node : Bytes) : List (Array Bytes) → List (Array Bytes)
  | [] => []
  | level :: rest =>
    let level := writeEntry level position node
    match rest with
    -- The top level has no parent to rehash.
    | [] => [level]
    | rest =>
      level :: updateLevels (height + 1) (position / 2) (parentAt height level (position / 2)) rest

/-- Writing at most one past the end changes the entry at the position and no other. -/
theorem getElem?_writeEntry {level : Array Bytes} {position : Nat} (within : position ≤ level.size)
    (node : Bytes) (index : Nat) :
    (writeEntry level position node)[index]?
      = if position = index then some node else level[index]? := by
  unfold writeEntry
  split
  · simp [Array.getElem?_set]
  · simp only [Array.getElem?_push]
    split <;> split <;> first | rfl | omega

/-- An entry of a paired-up level is the parent of two entries below, inside the level. -/
theorem getElem?_pairUp (height : Nat) (level : Array Bytes) (index : Nat) :
    (pairUp height level)[index]?
      = if index < (level.size + 1) / 2 then some (parentAt height level index) else none := by
  simp only [pairUp, Array.getElem?_ofFn]
  split <;> rfl

/-- Pairing up a level after one entry is written writes the one entry above it. -/
theorem pairUp_writeEntry (height : Nat) (level : Array Bytes) {position : Nat}
    (within : position ≤ level.size) (node : Bytes) :
    pairUp height (writeEntry level position node)
      = writeEntry (pairUp height level) (position / 2)
          (parentAt height (writeEntry level position node) (position / 2)) := by
  have higher : position / 2 ≤ (pairUp height level).size := by
    simp only [pairUp, Array.size_ofFn]
    omega
  have size : (writeEntry level position node).size = max level.size (position + 1) := by
    unfold writeEntry
    split <;> simp <;> omega
  apply Array.ext_getElem?
  intro index
  rw [getElem?_writeEntry higher, getElem?_pairUp, getElem?_pairUp, size]
  by_cases same : position / 2 = index
  · subst same
    rw [ite_eq_left (by omega), ite_eq_left rfl]
  · -- The two entries under another parent are not the one written.
    have unchanged : parentAt height (writeEntry level position node) index
        = parentAt height level index := by
      simp only [parentAt, getElem?_writeEntry within]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [unchanged, ite_eq_right same]
    by_cases inside : index < (level.size + 1) / 2
    · rw [ite_eq_left inside, ite_eq_left (by omega)]
    · rw [ite_eq_right inside, ite_eq_right (by omega)]

/--
Updating the levels of a tree gives the levels of the tree over the written first level.

The position is inside the first level or just past it.
-/
theorem updateLevels_buildLevels :
    ∀ (above height : Nat) (level : Array Bytes) {position : Nat}
      (_ : position ≤ level.size) (node : Bytes),
      updateLevels height position node (buildLevels height level above)
        = buildLevels height (writeEntry level position node) above
  | 0, height, level, position, _, node => by
    simp [buildLevels, updateLevels]
  | above + 1, height, level, position, within, node => by
    have higher : position / 2 ≤ (pairUp height level).size := by
      simp only [pairUp, Array.size_ofFn]
      omega
    rw [buildLevels, buildLevels, pairUp_writeEntry height level within,
      ← updateLevels_buildLevels above (height + 1) _ higher]
    -- The levels above the first are never empty, so the update goes on up.
    obtain ⟨first, rest, nonempty⟩ :
        ∃ first rest, buildLevels (height + 1) (pairUp height level) above = first :: rest := by
      cases above <;> exact ⟨_, _, rfl⟩
    rw [nonempty]
    simp only [updateLevels]

/-- The top node of a tree from its levels, or the zero subtree of its depth if it has no leaf. -/
def topOfLevels (depth : Nat) (levels : List (Array Bytes)) : Bytes :=
  ((levels.getLast?.bind fun top => top[0]?)).getD (zeroSubtree depth)

open SszType

/-- The leaf of an element in a rooted sequence: its root, or the zero node if it has none. -/
def leafRoot {α : Type} [SszType α] (a : α) : Bytes :=
  -- A lawful element always has a root, so the zero node never stands in.
  match root a with
  | .ok node => node
  | .error _ => zeroChunk

/-- The leaves of a rooted sequence: the roots of its elements. -/
def leafRoots {α : Type} [SszType α] (elements : Array α) : Array Bytes :=
  -- A loop over the indices: a map over a generic element type keeps one stack frame per element.
  Array.ofFn fun index : Fin elements.size => leafRoot elements[index]

/-- Each leaf is the root of the element at its index. -/
theorem getElem?_leafRoots {α : Type} [SszType α] (elements : Array α) (index : Nat) :
    (leafRoots elements)[index]? = elements[index]?.map leafRoot := by
  simp only [leafRoots, Array.getElem?_ofFn]
  split <;> simp_all

/-- `Vector[α, length]`, with every level of its Merkle tree. -/
structure RootedVector (α : Type) [SszType α] (length : Nat) where
  /-- The elements, in order. -/
  elements : Vector α length
  /-- The levels of the tree, from the leaves up to the top node. -/
  levels : List (Array Bytes)
  /-- The levels are those of the tree over the roots of the elements. -/
  built : levels = buildLevels 0 (leafRoots elements.toArray) (depthFor length)

namespace RootedVector

variable {α : Type} [SszType α] {length : Nat}

/-- A vector with the levels of its tree, built from the leaves up. -/
def ofVector (elements : Vector α length) : RootedVector α length :=
  ⟨elements, buildLevels 0 (leafRoots elements.toArray) (depthFor length), rfl⟩

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
    rw [v.built, updateLevels_buildLevels _ 0 _ (by simp [leafRoots]; omega)]
    congr 1
    apply Array.ext_getElem?
    intro other
    rw [getElem?_writeEntry (by simp [leafRoots]; omega), getElem?_leafRoots,
      getElem?_leafRoots, Vector.toArray_set, Array.getElem?_set]
    split <;> simp_all⟩

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
