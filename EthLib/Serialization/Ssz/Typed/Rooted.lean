module

public import EthLib.Serialization.Ssz.Typed.Collections

/-!
# Typed SSZ values: vectors that keep their Merkle tree

A rooted vector holds its elements together with every level of their Merkle tree.

Writing one element then rehashes only the path above its leaf, one node per level.

The root is read from the top level, and the proofs show that it is the root of the vector.

Each leaf is the root of one element when the elements are composite.

Basic elements are packed, several to a leaf, and a write rehashes the leaf that holds the element.
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

/--
The levels with a count of levels added on top, each pairing up the one below it.

The height is that of the subtrees in the top level given.
-/
def raiseLevels (height : Nat) (levels : List (Array Bytes)) : Nat → List (Array Bytes)
  | 0 => levels
  | count + 1 =>
    raiseLevels (height + 1) (levels ++ [pairUp height (levels.getLast?.getD #[])]) count

/-- One more level on top of a tree pairs up its top level. -/
theorem buildLevels_succ :
    ∀ (above height : Nat) (level : Array Bytes),
      buildLevels height level (above + 1) = buildLevels height level above
        ++ [pairUp (height + above) ((buildLevels height level above).getLast?.getD #[])]
  | 0, height, level => by simp [buildLevels]
  | above + 1, height, level => by
    rw [buildLevels, buildLevels_succ above (height + 1), buildLevels]
    -- The levels above the first are never empty, so the top is theirs.
    obtain ⟨first, rest, nonempty⟩ :
        ∃ first rest, buildLevels (height + 1) (pairUp height level) above = first :: rest := by
      cases above <;> exact ⟨_, _, rfl⟩
    rw [nonempty, show height + 1 + above = height + (above + 1) by omega]
    simp

/-- Raising the levels of a tree gives the levels of the same leaves up to a greater height. -/
theorem raiseLevels_buildLevels (height : Nat) (level : Array Bytes) :
    ∀ (count above : Nat), raiseLevels (height + above) (buildLevels height level above) count
      = buildLevels height level (above + count)
  | 0, above => rfl
  | count + 1, above => by
    rw [raiseLevels, ← buildLevels_succ, show height + above + 1 = height + (above + 1) by omega,
      raiseLevels_buildLevels height level count (above + 1),
      show above + 1 + count = above + (count + 1) by omega]

/-- Raising the levels over the leaves gives their levels up to a greater height. -/
theorem raiseLevels_buildLevels_leaves (level : Array Bytes) (above count : Nat) :
    raiseLevels above (buildLevels 0 level above) count = buildLevels 0 level (above + count) := by
  simpa using raiseLevels_buildLevels 0 level count above

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

/-- The encoding of an element, or no bytes if it has none. -/
def elementBytes {α : Type} [SszType α] (a : α) : Bytes :=
  -- A lawful element always has an encoding, so the empty one never stands in.
  match Ssz.serialize (desc α) (toValue a) with
  | .ok bytes => bytes
  | .error _ => #[]

/-- How many elements of a basic type share one leaf: those that fit in a node, at least one. -/
def perChunk (α : Type) [SszType α] : Nat :=
  max 1 (bytesPerChunk / (desc α).itemLength)

/-- The leaf at an index of basic elements: the encodings of its elements, padded to a node. -/
def packedChunk {α : Type} [SszType α] (elements : Array α) (index : Nat) : Bytes :=
  let start := index * perChunk α
  -- A loop over the few elements of the leaf, never over the whole sequence.
  let piece := (elements.extract start (start + perChunk α)).foldl
    (fun bytes a => bytes ++ elementBytes a) #[]
  piece ++ Array.replicate (bytesPerChunk - piece.size) 0

/-- The leaves of basic elements, each holding the elements that share it. -/
def packedChunks {α : Type} [SszType α] (elements : Array α) : Array Bytes :=
  Array.ofFn fun index : Fin ((elements.size + perChunk α - 1) / perChunk α) =>
    packedChunk elements index

/-- The leaves of a rooted sequence: packed elements if they are basic, else their roots. -/
def sequenceLeaves {α : Type} [SszType α] (elements : Array α) : Array Bytes :=
  if (desc α).isBasic then packedChunks elements else leafRoots elements

/-- The count of leaves a capacity of elements takes, as SSZ measures a tree's width. -/
def leafCapacity (α : Type) [SszType α] (count : Nat) : Nat :=
  if (desc α).isBasic then chunksForBytes (count * (desc α).itemLength) else count

/-- The position of the leaf that holds the element at an index. -/
def leafIndex (α : Type) [SszType α] (index : Nat) : Nat :=
  if (desc α).isBasic then index / perChunk α else index

/-- The count of leaves that a count of elements fills. -/
def leafCount (α : Type) [SszType α] (count : Nat) : Nat :=
  if (desc α).isBasic then (count + perChunk α - 1) / perChunk α else count

/-- The leaf that holds the element at an index, once that element is the one given. -/
def leafNode {α : Type} [SszType α] (elements : Array α) (index : Nat) (a : α) : Bytes :=
  if (desc α).isBasic then packedChunk elements (index / perChunk α) else leafRoot a

/-- A positive count of elements shares each leaf. -/
theorem perChunk_pos (α : Type) [SszType α] : 0 < perChunk α :=
  Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

/-- Leaf `index` lies within the leaves of `count` elements exactly when its first element does. -/
theorem lt_chunks_iff {per : Nat} (positive : 0 < per) (index count : Nat) :
    index < (count + per - 1) / per ↔ index * per < count := by
  rw [Nat.lt_div_iff_mul_lt positive]
  omega

/-- An element sits in leaf `chunk` exactly when it lies in that leaf's run of elements. -/
theorem div_eq_iff_between {per : Nat} (positive : 0 < per) (index chunk : Nat) :
    index / per = chunk ↔ chunk * per ≤ index ∧ index < chunk * per + per := by
  rw [Nat.div_eq_iff positive]
  omega

/-- A packed leaf reads only the elements of its own run. -/
theorem packedChunk_congr {α : Type} [SszType α] {elements other : Array α} {chunk : Nat}
    (same : ∀ offset, offset < perChunk α →
      elements[chunk * perChunk α + offset]? = other[chunk * perChunk α + offset]?) :
    packedChunk elements chunk = packedChunk other chunk := by
  have runs : elements.extract (chunk * perChunk α) (chunk * perChunk α + perChunk α)
      = other.extract (chunk * perChunk α) (chunk * perChunk α + perChunk α) := by
    apply Array.ext_getElem?
    intro offset
    rw [Array.getElem?_extract, Array.getElem?_extract]
    by_cases inside : offset < perChunk α
    · have here := same offset inside
      -- Both runs end where the leaf or the sequence ends, so they hold the same elements.
      by_cases left : offset < min (chunk * perChunk α + perChunk α) elements.size
          - chunk * perChunk α
      · rw [ite_eq_left left]
        by_cases right : offset < min (chunk * perChunk α + perChunk α) other.size
            - chunk * perChunk α
        · rw [ite_eq_left right, here]
        · rw [ite_eq_right right, here]
          exact Array.getElem?_eq_none (by omega)
      · rw [ite_eq_right left]
        by_cases right : offset < min (chunk * perChunk α + perChunk α) other.size
            - chunk * perChunk α
        · rw [ite_eq_left right, ← here]
          exact (Array.getElem?_eq_none (by omega)).symm
        · rw [ite_eq_right right]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [packedChunk, runs]

/-- The leaf of an element inside the sequence or just past it is inside the leaves or just past. -/
theorem leafIndex_le {α : Type} [SszType α] {elements : Array α} {index : Nat}
    (within : index ≤ elements.size) : leafIndex α index ≤ (sequenceLeaves elements).size := by
  unfold leafIndex sequenceLeaves
  split
  · simp only [packedChunks, Array.size_ofFn]
    apply Nat.le_of_lt_succ
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le (perChunk_pos α)]
    have := Nat.div_mul_le_self index (perChunk α)
    have := perChunk_pos α
    omega
  · simpa [leafRoots] using within

/-- The leaves of a sequence are as many as its count of elements fills. -/
theorem size_sequenceLeaves {α : Type} [SszType α] (elements : Array α) :
    (sequenceLeaves elements).size = leafCount α elements.size := by
  unfold sequenceLeaves leafCount
  split <;> simp [packedChunks, leafRoots]

/-- One more element fills at least as many leaves. -/
theorem leafCount_le_succ (α : Type) [SszType α] (count : Nat) :
    leafCount α count ≤ leafCount α (count + 1) := by
  unfold leafCount
  split
  · exact Nat.div_le_div_right (by omega)
  · omega

/--
Writing one element, inside or just past the end, writes the one leaf that holds it.

The other elements stay where they were.
-/
theorem sequenceLeaves_write {α : Type} [SszType α] {elements written : Array α} {index : Nat}
    {a : α} (put : written[index]? = some a)
    (grow : written.size = elements.size ∨ (written.size = elements.size + 1 ∧
      index = elements.size))
    (others : ∀ other, other ≠ index → written[other]? = elements[other]?) :
    sequenceLeaves written = writeEntry (sequenceLeaves elements) (leafIndex α index)
      (leafNode written index a) := by
  have inside : index < written.size := (Array.getElem?_eq_some_iff.mp put).1
  have positive := perChunk_pos α
  unfold sequenceLeaves leafIndex leafNode
  split
  · -- Basic elements: only the leaf of the written element reads it.
    have within : index / perChunk α ≤ (packedChunks elements).size := by
      simp only [packedChunks, Array.size_ofFn]
      apply Nat.le_of_lt_succ
      rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le positive]
      have := Nat.div_mul_le_self index (perChunk α)
      omega
    apply Array.ext_getElem?
    intro chunk
    rw [getElem?_writeEntry within]
    simp only [packedChunks, Array.getElem?_ofFn]
    by_cases same : index / perChunk α = chunk
    · subst same
      rw [dite_eq_left ((lt_chunks_iff positive _ _).mpr (by
        have := Nat.div_mul_le_self index (perChunk α)
        omega)), ite_eq_left rfl]
    · rw [ite_eq_right same]
      have away := mt (div_eq_iff_between positive index chunk).mpr same
      have unchanged : packedChunk written chunk = packedChunk elements chunk :=
        packedChunk_congr fun offset _ => others _ (by omega)
      rw [unchanged]
      by_cases before : chunk * perChunk α < elements.size
      · rw [dite_eq_left ((lt_chunks_iff positive _ _).mpr (by omega)),
          dite_eq_left ((lt_chunks_iff positive _ _).mpr before)]
      · rw [dite_eq_right (fun lt => before ((lt_chunks_iff positive _ _).mp lt)),
          dite_eq_right (fun lt => by have := (lt_chunks_iff positive _ _).mp lt; omega)]
  · -- Composite elements: each leaf is the root of its own element.
    apply Array.ext_getElem?
    intro other
    rw [getElem?_writeEntry (by simp [leafRoots]; omega), getElem?_leafRoots,
      getElem?_leafRoots]
    by_cases same : index = other
    · subst same
      simp [put]
    · rw [ite_eq_right same, others other (Ne.symm same)]

/-- `Vector[α, length]`, with every level of its Merkle tree. -/
structure RootedVector (α : Type) [SszType α] (length : Nat) where
  /-- The elements, in order. -/
  elements : Vector α length
  /-- The levels of the tree, from the leaves up to the top node. -/
  levels : List (Array Bytes)
  /-- The levels are those of the tree over the leaves of the elements. -/
  built :
    levels = buildLevels 0 (sequenceLeaves elements.toArray) (depthFor (leafCapacity α length))

namespace RootedVector

variable {α : Type} [SszType α] {length : Nat}

/-- A vector with the levels of its tree, built from the leaves up. -/
def ofVector (elements : Vector α length) : RootedVector α length :=
  ⟨elements, buildLevels 0 (sequenceLeaves elements.toArray) (depthFor (leafCapacity α length)),
    rfl⟩

/-- The element at an index. -/
def get (v : RootedVector α length) (index : Nat) (inside : index < length := by get_elem_tactic) :
    α :=
  v.elements[index]

instance : GetElem (RootedVector α length) Nat α fun _ index => index < length where
  getElem v index inside := v.get index inside

/-- The vector with the element at an index replaced, its tree rehashed along one path. -/
def set (v : RootedVector α length) (index : Nat) (a : α)
    (inside : index < length := by get_elem_tactic) : RootedVector α length :=
  ⟨v.elements.set index a inside,
    updateLevels 0 (leafIndex α index) (leafNode (v.elements.set index a inside).toArray index a)
      v.levels, by
    rw [v.built, updateLevels_buildLevels _ 0 _ (leafIndex_le (by simp; omega))]
    congr 1
    symm
    apply sequenceLeaves_write (by simp [inside]) (.inl (by simp))
    intro other differ
    simp [Vector.toArray_set, Ne.symm differ]⟩

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

/-- `Vector[α, length]`, which reads its root from the top of its levels. -/
instance {α : Type} [SszType α] {length : Nat} : SszType (RootedVector α length) where
  desc := desc (Vector α length)
  toValue v := toValue v.elements
  ofValue value := ofVector <$> ofValue value
  root v := .ok (topOfLevels (depthFor (leafCapacity α length)) v.levels)

end EthLib.Serialization.Ssz
