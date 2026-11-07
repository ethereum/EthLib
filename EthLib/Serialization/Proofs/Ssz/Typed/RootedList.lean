module

public import EthLib.Serialization.Ssz.Typed.RootedList
public import EthLib.Serialization.Proofs.Ssz.Typed.ForkKind
public import EthLib.Serialization.Proofs.Ssz.Typed.Rooted

/-!
# Proofs: rooted fork-chosen lists are lawful

Before the switch, the top of the levels is the bounded root of the leaves.

With the length mixed in, it is the root of the list.

A rooted list has the SSZ type and the values of the fork-chosen list with its elements.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType RootedForkList

namespace RootedForkList

variable {switch fork : Fork} {α : Type} [SszType α] {limit : Nat}

/-- The elements of the list built from an array are that array. -/
@[simp] theorem data_ofData (data : Array α) (bound : fork < switch → data.size ≤ limit) :
    (ofData (switch := switch) data bound).data = data := rfl

/-- The elements of the list built from a fork-chosen list are its elements. -/
@[simp] theorem data_ofForkList (l : ForkList switch fork α limit) :
    (ofForkList l).data = l.data := rfl

/-- The elements after a write are the elements with that one replaced. -/
@[simp] theorem data_set (l : RootedForkList switch fork α limit) (index : Nat) (a : α)
    (inside : index < l.data.size) : (l.set index a inside).data = l.data.set index a inside :=
  rfl

/-- The elements after an append are the elements with one more at the end. -/
@[simp] theorem data_push (l : RootedForkList switch fork α limit) (a : α)
    (room : fork < switch → l.data.size < limit) : (l.push a room).data = l.data.push a :=
  rfl

end RootedForkList

variable {α : Type} [SszType α] [LawfulSszType α]

/-- A list of composite elements within its limit has the root of the roots of its elements. -/
theorem hashTreeRoot_list_leafRoots {limit : Nat} (composite : (desc α).isBasic = false)
    (data : Array α) (bound : data.size ≤ limit) :
    Ssz.hashTreeRoot (.list (desc α) limit) (.seq (data.toList.map toValue))
      = .ok (mixIn (subtreeAt (leafRoots data) (depthFor limit) 0) (lengthWord data.size)) := by
  have rooted := mapM_hashTreeRoot_toValue data.toList
  have within : ¬limit < data.size := by omega
  have leaves : (data.toList.map leafRoot).toArray = leafRoots data := by
    apply Array.ext_getElem?
    intro index
    simp [getElem?_leafRoots]
  have size : (leafRoots data).size = data.size := by simp [leafRoots]
  rw [hashTreeRoot_unfold]
  simp [merkleLayout, sequenceLayout, composite, MerkleLayout.nesting, leafChunks,
    slotRoot, List.mapM_map, Function.comp_def, rooted, finishLayout, merkleizeBoundedUnchecked,
    bind, Except.bind, pure, Except.pure, within, leaves, size]

/-- A list of basic elements within its limit has the root of its packed leaves. -/
theorem hashTreeRoot_list_packed {limit : Nat} (basic : (desc α).isBasic = true)
    (data : Array α) (bound : data.size ≤ limit) :
    Ssz.hashTreeRoot (.list (desc α) limit) (.seq (data.toList.map toValue))
      = .ok (mixIn (subtreeAt (packedChunks data)
          (depthFor (chunksForBytes (limit * (desc α).itemLength))) 0) (lengthWord data.size)) := by
  have within : ¬limit < data.size := by omega
  have packed := packElements_elementBytes basic data
  have fit : ¬chunksForBytes (limit * (desc α).itemLength) < (packedChunks data).size := by
    rw [← packed, packElements, fold_parts_eq_concat, Array.empty_append, packBytes_size,
      concatParts_size _ _ (fun part member => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp member
        exact (serialize_elementBytes basic a).2)]
    simp only [List.length_map, Array.length_toList, chunksForBytes, Nat.not_lt]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ bound) _) _)
  rw [hashTreeRoot_unfold]
  simp [merkleLayout, sequenceLayout, basic, MerkleLayout.packing, leafChunks,
    serializeEach_elementBytes basic, finishLayout, merkleizeBoundedUnchecked,
    bind, Except.bind, pure, Except.pure, packed, fit, within]

namespace RootedForkList

variable {switch fork : Fork} {limit : Nat}

/-- The root of a rooted list is the root of its elements as a fork-chosen list. -/
theorem root_eq (l : RootedForkList switch fork α limit) :
    root l = Ssz.hashTreeRoot (desc (RootedForkList switch fork α limit)) (toValue l) := by
  by_cases before : fork < switch
  · simp only [root, before, ite_true, desc, toValue, toForkList, not_switch_of_lt before,
      ite_false]
    rw [l.built, forkListLevels, ite_eq_left before, topOfLevels_eq, sequenceLeaves,
      leafCapacity]
    by_cases basic : (desc α).isBasic
    · rw [ite_eq_left basic, ite_eq_left basic,
        hashTreeRoot_list_packed basic _ (l.bound before)]
    · rw [ite_eq_right basic, ite_eq_right basic,
        hashTreeRoot_list_leafRoots (by simpa using basic) _ (l.bound before)]
  · simp [root, before, desc, toValue]

end RootedForkList

variable {switch fork : Fork} {limit : Nat}

/-- A rooted list is lawful when its elements are. -/
instance : LawfulSszType (RootedForkList switch fork α limit) where
  wellFormed := LawfulSszType.wellFormed (α := ForkList switch fork α limit)
  fits l := LawfulSszType.fits (α := ForkList switch fork α limit) l.toForkList
  ofValue_toValue l := by
    change ofForkList <$>
      (ofValue (toValue l.toForkList) : Except Err (ForkList switch fork α limit)) = .ok l
    rw [LawfulSszType.ofValue_toValue]
    exact congrArg Except.ok (ext rfl)
  toValue_of_ofValue {value l} made := by
    change ofForkList <$> (ofValue value : Except Err (ForkList switch fork α limit)) = .ok l
      at made
    cases read : (ofValue value : Except Err (ForkList switch fork α limit)) with
    | error fault => simp [read, Functor.map, Except.map] at made
    | ok m =>
      simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
      subst made
      exact LawfulSszType.toValue_of_ofValue (α := ForkList switch fork α limit) read
  root_eq := RootedForkList.root_eq

end EthLib.Serialization.Ssz
