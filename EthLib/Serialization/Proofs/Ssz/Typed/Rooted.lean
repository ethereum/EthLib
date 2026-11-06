module

public import EthLib.Serialization.Ssz.Typed.Rooted
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
public import EthLib.Serialization.Proofs.Ssz.Codec.RootUnfold
public import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain
public import EthLib.Serialization.Proofs.Ssz.Merkle.Tree

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

namespace RootedVector

variable {length : Nat}

/-- The root of a rooted vector is the root of its elements as a vector. -/
theorem root_eq (v : RootedVector α length) :
    root v = Ssz.hashTreeRoot (desc (RootedVector α length)) (toValue v) := by
  by_cases basic : (desc α).isBasic
  · simp [root, basic, desc, toValue]
  · simp only [root, basic, desc, toValue, Bool.false_eq_true, ite_false]
    rw [hashTreeRoot_vector_leafRoots (by simpa using basic), v.built, topOfLevels_eq]

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
  root_eq := RootedVector.root_eq

end EthLib.Serialization.Ssz
