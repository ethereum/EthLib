module

public import EthLib.Serialization.Ssz.Typed.Rooted
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
public import EthLib.Serialization.Proofs.Ssz.Codec.RootUnfold
public import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain
public import EthLib.Serialization.Proofs.Ssz.Merkle.Tree
public import EthLib.Serialization.Proofs.Ssz.Codec.BindingPacking

/-!
# Proofs: rooted vectors are lawful

Each level of a rooted vector holds the subtrees of one height over the leaves.

So the top level holds the root of the whole tree, which is the root of the vector.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType RootedVector

/-- A zero subtree is the zero subtree one level down, hashed with itself. -/
theorem zeroSubtree_succ (height : Nat) :
    zeroSubtree (height + 1) = combine (zeroSubtree height) (zeroSubtree height) := by
  rw [zeroSubtree_eq, zeroSubtree_eq]
  rfl

/--
Entry `index` of the level at a height is the subtree of that height at leaf `index * 2 ^ height`.

An entry past the level reads as the zero subtree, as the subtree past the leaves does.
-/
def LevelOf (chunks : Array Bytes) (height : Nat) (level : Array Bytes) : Prop :=
  ∀ index, level[index]?.getD (zeroSubtree height) = subtreeAt chunks height (index * 2 ^ height)

/-- The leaves are the level of height zero. -/
theorem levelOf_leaves (chunks : Array Bytes) : LevelOf chunks 0 chunks := by
  intro index
  rw [subtreeAt_leaf, zeroSubtree_eq]
  simp [zeroRoot]

/-- Pairing up the level at a height gives the level one higher. -/
theorem LevelOf.pairUp {chunks level : Array Bytes} {height : Nat}
    (holds : LevelOf chunks height level) : LevelOf chunks (height + 1) (pairUp height level) := by
  intro index
  have left := holds (2 * index)
  have right := holds (2 * index + 1)
  -- Child `2 * index` starts where the parent does, and its sibling one subtree further on.
  rw [show 2 * index * 2 ^ height = index * 2 ^ (height + 1) by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ height) 2, ← Nat.mul_assoc, Nat.mul_comm index 2]] at left
  rw [show (2 * index + 1) * 2 ^ height = index * 2 ^ (height + 1) + 2 ^ height by
    rw [Nat.add_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (2 ^ height) 2, ← Nat.mul_assoc,
      Nat.mul_comm index 2]] at right
  rw [subtreeAt_split, ← left, ← right]
  by_cases inside : index < (level.size + 1) / 2
  · simp [Ssz.pairUp, inside, parentAt]
  · -- Past the level, both children are past it too, so both are zero subtrees.
    have parent : (Ssz.pairUp height level)[index]? = none :=
      Array.getElem?_eq_none (by simp only [Ssz.pairUp, Array.size_ofFn]; omega)
    have first : level[2 * index]? = none := Array.getElem?_eq_none (by omega)
    have second : level[2 * index + 1]? = none := Array.getElem?_eq_none (by omega)
    simp only [parent, first, second, Option.getD_none]
    exact zeroSubtree_succ height

/-- The top node of the levels over a level at a height is the subtree over the leaves. -/
theorem topOfLevels_buildLevels {chunks : Array Bytes} :
    ∀ (above height : Nat) {level : Array Bytes}, LevelOf chunks height level →
      topOfLevels (height + above) (buildLevels height level above)
        = subtreeAt chunks (height + above) 0
  | 0, height, level, holds => by
    simpa [topOfLevels, buildLevels] using holds 0
  | above + 1, height, level, holds => by
    have := topOfLevels_buildLevels above (height + 1) holds.pairUp
    rw [show height + (above + 1) = height + 1 + above by omega, ← this]
    -- The levels above the first are never empty, so the top is theirs.
    obtain ⟨first, rest, nonempty⟩ :
        ∃ first rest, buildLevels (height + 1) (Ssz.pairUp height level) above = first :: rest := by
      cases above <;> exact ⟨_, _, rfl⟩
    simp only [topOfLevels, buildLevels, nonempty, List.getLast?_cons_cons]

/-- The top node of a tree from its levels is the bounded root of its leaves. -/
theorem topOfLevels_eq (chunks : Array Bytes) (depth : Nat) :
    topOfLevels depth (buildLevels 0 chunks depth) = subtreeAt chunks depth 0 := by
  simpa using topOfLevels_buildLevels depth 0 (levelOf_leaves chunks)

namespace RootedVector

variable {α : Type} [SszType α] {length : Nat}

/-- The elements of the vector built from a vector are that vector. -/
@[simp] theorem elements_ofVector (elements : Vector α length) :
    (ofVector elements).elements = elements := rfl

/-- The elements after a write are the elements with that one replaced. -/
@[simp] theorem elements_set (v : RootedVector α length) (index : Nat) (a : α)
    (inside : index < length) : (v.set index a inside).elements = v.elements.set index a inside :=
  rfl

/-- An optional read of the vector is the optional read of its elements. -/
@[simp] theorem getElem?_eq (v : RootedVector α length) (index : Nat) :
    v[index]? = v.elements[index]? := by
  by_cases inside : index < length
  · rw [Vector.getElem?_eq_getElem inside]
    exact dite_eq_left inside
  · rw [Vector.getElem?_eq_none (Nat.le_of_not_lt inside)]
    exact dite_eq_right inside

/-- Reading the element just written gives it back. -/
@[simp] theorem getElem_set_self (v : RootedVector α length) (index : Nat) (a : α)
    (inside : index < length) : (v.set index a inside)[index] = a := by
  show (v.elements.set index a inside)[index] = a
  simp

/-- Reading another element after a write gives what was there. -/
theorem getElem_set_ne (v : RootedVector α length) {index other : Nat} (a : α)
    (inside : index < length) (within : other < length) (differ : index ≠ other) :
    (v.set index a inside)[other] = v[other] := by
  show (v.elements.set index a inside)[other] = v.elements[other]
  simp [differ]

end RootedVector

variable {α : Type} [SszType α] [LawfulSszType α]

/-- A lawful element has a root, which is its leaf. -/
theorem root_eq_leafRoot (a : α) : root a = .ok (leafRoot a) := by
  obtain ⟨node, rooted, -⟩ := Ssz.hashTreeRoot_total (desc α) (toValue a)
    LawfulSszType.wellFormed (LawfulSszType.fits a)
  rw [← LawfulSszType.root_eq] at rooted
  simp [leafRoot, rooted]

/-- Rooting the elements one by one gives their leaves. -/
theorem mapM_hashTreeRoot_toValue (items : List α) :
    items.mapM (fun a => Ssz.hashTreeRoot (desc α) (toValue a)) = .ok (items.map leafRoot) := by
  have same : (fun a : α => Ssz.hashTreeRoot (desc α) (toValue a)) = fun a => .ok (leafRoot a) := by
    funext a
    rw [← LawfulSszType.root_eq, root_eq_leafRoot]
  rw [same]
  induction items with
  | nil => rfl
  | cons a items ih => simp [List.mapM_cons, ih, bind, Except.bind, pure, Except.pure]

/-- A vector of composite elements has the bounded root of the roots of its elements. -/
theorem hashTreeRoot_vector_leafRoots {length : Nat} (composite : (desc α).isBasic = false)
    (elements : Vector α length) :
    Ssz.hashTreeRoot (.vector (desc α) length) (.seq (elements.toList.map toValue))
      = .ok (subtreeAt (leafRoots elements.toArray) (depthFor length) 0) := by
  have rooted := mapM_hashTreeRoot_toValue elements.toList
  rw [hashTreeRoot_unfold]
  simp [merkleLayout, sequenceLayout, composite, MerkleLayout.nesting, leafChunks,
    slotRoot, List.mapM_map, Function.comp_def, rooted, finishLayout, merkleizeBoundedUnchecked,
    bind, Except.bind, pure, Except.pure]
  congr 1
  apply Array.ext
  · simp [leafRoots]
  · intro index _ _
    simp [leafRoots]

/-- Taking whole parts out of parts of one width takes the same bytes out of their run. -/
theorem extract_concatParts_run {width : Nat} :
    ∀ (parts : List Bytes), (∀ part ∈ parts, part.size = width) → ∀ skip take : Nat,
      (concatParts parts).extract (skip * width) ((skip + take) * width)
        = concatParts ((parts.drop skip).take take)
  | [], _, skip, take => by simp [concatParts]
  | part :: rest, widths, skip, take => by
    have sized : part.size = width := widths part (by simp)
    have restWidths : ∀ other ∈ rest, other.size = width := fun other member =>
      widths other (by simp [member])
    simp only [concatParts, Array.extract_append, sized]
    cases skip with
    | succ skip =>
      -- The first part lies wholly before the run, so the run starts in the rest.
      rw [Array.extract_eq_empty_of_le (by rw [Nat.succ_mul]; omega), Array.empty_append,
        show (skip + 1) * width - width = skip * width by rw [Nat.succ_mul]; omega,
        show (skip + 1 + take) * width - width = (skip + take) * width by
          rw [show skip + 1 + take = (skip + take) + 1 by omega, Nat.succ_mul]; omega,
        extract_concatParts_run rest restWidths skip take]
      simp
    | zero =>
      cases take with
      | zero => simp [concatParts]
      | succ take =>
        -- The run starts with the first part, whole, then takes the rest from the next one.
        have ih := extract_concatParts_run rest restWidths 0 take
        simp only [Nat.zero_mul, Nat.zero_add, Nat.zero_sub, List.drop_zero] at ih ⊢
        rw [show (take + 1) * width - width = take * width by rw [Nat.succ_mul]; omega, ih,
          Array.extract_eq_self_of_le (by rw [sized, Nat.succ_mul]; omega)]
        simp [concatParts]

section Packed

/-- A basic element encodes to the bytes of its leaf, of the width of its type. -/
theorem serialize_elementBytes (basic : (desc α).isBasic = true) (a : α) :
    Ssz.serialize (desc α) (toValue a) = .ok (elementBytes a)
      ∧ (elementBytes a).size = (desc α).itemLength := by
  have fits := LawfulSszType.fits a
  unfold elementBytes
  generalize desc α = shape at fits basic ⊢
  generalize toValue a = value at fits ⊢
  cases fits <;> simp [Desc.isBasic] at basic
  case bool b => simp [Ssz.serialize, Desc.itemLength]
  case uint width n bound => simp [Ssz.serialize, bound, Desc.itemLength, uintBytes_size]

/-- Encoding basic elements one by one gives the bytes of their leaves. -/
theorem serializeEach_elementBytes (basic : (desc α).isBasic = true) :
    ∀ items : List α,
      serializeEach (desc α) (items.map toValue) = .ok (items.map elementBytes)
  | [] => by simp [serializeEach_nil]
  | a :: items => by
    simp [serializeEach_cons, (serialize_elementBytes basic a).1,
      serializeEach_elementBytes basic items, bind, Except.bind, pure, Except.pure]

/-- A basic type of a well-formed shape fills a node with a whole number of elements. -/
theorem itemLength_mul_perChunk (basic : (desc α).isBasic = true) :
    (desc α).itemLength * perChunk α = bytesPerChunk := by
  have sound := LawfulSszType.wellFormed (α := α)
  unfold perChunk
  generalize desc α = shape at sound basic ⊢
  cases shape <;> simp [Desc.isBasic] at basic
  · simp [Desc.itemLength, bytesPerChunk]
  · rename_i width
    simp only [Desc.wellFormed] at sound
    split at sound
    · rename_i listed
      have member : width ∈ [1, 2, 4, 8, 16, 32] := List.contains_iff_mem.mp listed
      simp only [Desc.itemLength, bytesPerChunk]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · cases sound

/-- Basic elements pack into the leaves that a rooted sequence keeps for them. -/
theorem packElements_elementBytes (basic : (desc α).isBasic = true) (elements : Array α) :
    packElements (elements.toList.map elementBytes) = packedChunks elements := by
  have filled := itemLength_mul_perChunk (α := α) basic
  have widths : ∀ part ∈ elements.toList.map elementBytes, part.size = (desc α).itemLength := by
    intro part member
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp member
    exact (serialize_elementBytes basic a).2
  have size := concatParts_size _ _ widths
  simp only [List.length_map, Array.length_toList] at size
  generalize hw : (desc α).itemLength = width at filled widths size
  have positive := perChunk_pos α
  generalize hk : perChunk α = per at filled positive
  rw [bytesPerChunk] at filled
  have wide : 0 < width := Nat.pos_of_ne_zero (by rintro rfl; simp at filled)
  rw [packElements, fold_parts_eq_concat, Array.empty_append]
  apply Array.ext
  · -- The bytes fill whole nodes of `per` elements each, the last one perhaps in part.
    simp only [packBytes_size, size, packedChunks, Array.size_ofFn, hk, bytesPerChunk]
    rw [← filled, ← Nat.div_div_eq_div_mul]
    congr 1
    have expand : elements.size * width + width * per - 1
        = width * (elements.size + per - 1) + (width - 1) := by
      rw [Nat.mul_sub, Nat.mul_add, Nat.mul_one, Nat.mul_comm elements.size width]
      have : width ≤ width * per := Nat.le_mul_of_pos_right width positive
      omega
    rw [expand, Nat.mul_add_div wide, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  · intro chunk _ _
    simp only [packBytes, packedChunks, packedChunk, Array.getElem_ofFn, hk, bytesPerChunk]
    -- Leaf `chunk` holds the bytes of elements `chunk * per` to `chunk * per + per`.
    have run : (concatParts (elements.toList.map elementBytes)).extract (chunk * 32)
          (chunk * 32 + 32)
        = (elements.extract (chunk * per) (chunk * per + per)).foldl
            (fun bytes a => bytes ++ elementBytes a) #[] := by
      rw [show chunk * 32 + 32 = (chunk * per + per) * width by
          rw [← filled, Nat.add_mul]; ac_rfl,
        show chunk * 32 = (chunk * per) * width by rw [← filled]; ac_rfl,
        extract_concatParts_run _ widths, ← Array.foldl_toList, Array.toList_extract,
        List.extract_eq_take_drop, ← List.foldl_map, fold_parts_eq_concat, Array.empty_append,
        List.map_take, List.map_drop]
      congr 2
      omega
    rw [run]

/-- A vector of basic elements has the bounded root of its packed leaves. -/
theorem hashTreeRoot_vector_packed {length : Nat} (basic : (desc α).isBasic = true)
    (elements : Vector α length) :
    Ssz.hashTreeRoot (.vector (desc α) length) (.seq (elements.toList.map toValue))
      = .ok (subtreeAt (packedChunks elements.toArray)
          (depthFor (chunksForBytes (length * (desc α).itemLength))) 0) := by
  rw [hashTreeRoot_unfold]
  have packed : packElements (elements.toList.map elementBytes) = packedChunks elements.toArray :=
    packElements_elementBytes basic elements.toArray
  have fit : ¬chunksForBytes (length * (desc α).itemLength) < (packedChunks elements.toArray).size
      := by
    rw [← packed, packElements, fold_parts_eq_concat, Array.empty_append, packBytes_size,
      concatParts_size _ _ (fun part member => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp member
        exact (serialize_elementBytes basic a).2)]
    simp [chunksForBytes]
  simp [merkleLayout, sequenceLayout, basic, MerkleLayout.packing, leafChunks,
    serializeEach_elementBytes basic, finishLayout, merkleizeBoundedUnchecked,
    bind, Except.bind, pure, Except.pure, packed, fit]

end Packed

namespace RootedVector

variable {length : Nat}

/-- The root of a rooted vector is the root of its elements as a vector. -/
theorem root_eq (v : RootedVector α length) :
    root v = Ssz.hashTreeRoot (desc (RootedVector α length)) (toValue v) := by
  simp only [root, desc, toValue]
  rw [v.built, topOfLevels_eq, sequenceLeaves, leafCapacity]
  by_cases basic : (desc α).isBasic
  · rw [ite_eq_left basic, ite_eq_left basic, hashTreeRoot_vector_packed basic]
  · rw [ite_eq_right basic, ite_eq_right basic,
      hashTreeRoot_vector_leafRoots (by simpa using basic)]

end RootedVector

/-- A rooted vector is lawful when its elements are and its length is positive. -/
instance {length : Nat} [NeZero length] : LawfulSszType (RootedVector α length) where
  wellFormed := LawfulSszType.wellFormed (α := Vector α length)
  fits v := LawfulSszType.fits (α := Vector α length) v.elements
  ofValue_toValue v := by
    change ofVector <$> (ofValue (toValue v.elements) : Except Err (Vector α length)) = .ok v
    rw [LawfulSszType.ofValue_toValue]
    exact congrArg Except.ok (ext rfl)
  toValue_of_ofValue {value v} made := by
    change ofVector <$> (ofValue value : Except Err (Vector α length)) = .ok v at made
    cases read : (ofValue value : Except Err (Vector α length)) with
    | error fault => simp [read, Functor.map, Except.map] at made
    | ok w =>
      simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
      subst made
      exact LawfulSszType.toValue_of_ofValue (α := Vector α length) read
  ofValue_ne_error {value fault} fits made := by
    change ofVector <$> (ofValue value : Except Err (Vector α length)) = .error fault at made
    cases read : (ofValue value : Except Err (Vector α length)) with
    | error fault => exact LawfulSszType.ofValue_ne_error (α := (Vector α length)) fits read
    | ok w => simp [read, Functor.map, Except.map] at made
  root_eq := RootedVector.root_eq
  encode_eq v := LawfulSszType.encode_eq (α := Vector α length) v.elements

end EthLib.Serialization.Ssz
