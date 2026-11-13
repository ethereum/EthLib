module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: two stores agree on the ancestry of the blocks they share

A safety argument for the fast confirmation rule works across honest nodes.

It learns an ancestry in the store of one node and uses it in the store of another.

The walk to an ancestor reads only the blocks of the store, by their roots.

So two stores that hold the same block at each root of the walk make the same walk.

In a reachable store each known block is keyed by its own hash tree root.

So two reachable stores hold different blocks at one root only when those blocks collide.

A search over the roots of the walk names such a collision, when there is one.

So the walk of the first store is also the walk of the second, or the search names a collision.

The second store must hold a block at each root of the walk.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Store

open Classical in
/-- The first root of a list where two stores hold different blocks, with those two blocks.

Blocks have no decidable equality, so the search compares them classically. -/
noncomputable def findBlockCollision (first second : Store preset fork) :
    List Root → Option (Root × BeaconBlock preset fork × BeaconBlock preset fork)
  | [] => none
  | root :: roots =>
    match first.blocks[root]?, second.blocks[root]? with
    | some block₁, some block₂ =>
      if block₁ = block₂ then findBlockCollision first second roots
      else some (root, block₁, block₂)
    | _, _ => findBlockCollision first second roots

variable {config : Config} {anchorState₁ anchorState₂ : BeaconState preset fork}
  {anchorBlock₁ anchorBlock₂ : BeaconBlock preset fork} {first second : Store preset fork}

/-- Without a collision over the roots, stores hold equal blocks wherever both hold one. -/
private theorem eq_of_findBlockCollision_none {roots : List Root} {root : Root}
    {b₁ b₂ : BeaconBlock preset fork} (none : findBlockCollision first second roots = none)
    (mem : root ∈ roots) (h₁ : first.blocks[root]? = some b₁)
    (h₂ : second.blocks[root]? = some b₂) : b₁ = b₂ := by
  induction roots with
  | nil => simp at mem
  | cons head tail ih =>
    simp only [findBlockCollision] at none
    rcases List.mem_cons.mp mem with rfl | mem
    · rw [h₁, h₂] at none
      simp only at none
      split at none
      · assumption
      · simp at none
    · split at none
      · rename_i c₁ c₂ _ _
        split at none
        · exact ih none mem
        · simp at none
      · exact ih none mem

/-- Without a collision, a store that holds a block at each root of a walk agrees on them. -/
private theorem agree_of_findBlockCollision_none {node : ForkChoiceNode} {slot : Slot}
    {roots : List Root} (none : findBlockCollision first second roots = none)
    (cover : ∀ later visited, slot ≤ later → first.getAncestor node later = .ok visited →
      visited.root ∈ roots)
    (known : ∀ later visited, slot ≤ later → first.getAncestor node later = .ok visited →
      second.blocks.contains visited.root) :
    ∀ later visited, slot ≤ later → first.getAncestor node later = .ok visited →
      second.blocks[visited.root]? = first.blocks[visited.root]? := by
  intro later visited hle hw
  obtain ⟨b₁, h₁, -⟩ := getAncestor_le hw
  have hc := known later visited hle hw
  obtain ⟨b₂, h₂⟩ : ∃ b₂, second.blocks[visited.root]? = some b₂ := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?] at hc
    exact Option.isSome_iff_exists.mp hc
  rw [h₂, h₁, eq_of_findBlockCollision_none none (cover later visited hle hw) h₁ h₂]

/-- A search on two reachable stores names two different blocks with one hash tree root. -/
theorem findBlockCollision_valid (reachable₁ : Reachable config anchorState₁ anchorBlock₁ first)
    (reachable₂ : Reachable config anchorState₂ anchorBlock₂ second) {roots : List Root}
    {root : Root} {block₁ block₂ : BeaconBlock preset fork}
    (found : findBlockCollision first second roots = some (root, block₁, block₂)) :
    block₁ ≠ block₂ ∧ SszType.hashTreeRoot block₁ = .ok root ∧
      SszType.hashTreeRoot block₂ = .ok root := by
  induction roots with
  | nil => simp [findBlockCollision] at found
  | cons head tail ih =>
    simp only [findBlockCollision] at found
    split at found
    · rename_i b₁ b₂ h₁ h₂
      split at found
      · exact ih found
      · rename_i ne
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl, rfl⟩ := found
        exact ⟨ne, reachable₁.root h₁, reachable₂.root h₂⟩
    · exact ih found

/-- A search finds no collision between a store and itself. -/
theorem findBlockCollision_self (store : Store preset fork) (roots : List Root) :
    findBlockCollision store store roots = none := by
  induction roots with
  | nil => simp [findBlockCollision]
  | cons head tail ih =>
    simp only [findBlockCollision]
    split
    · rename_i b₁ b₂ h₁ h₂
      rw [h₁] at h₂
      cases h₂
      simp [ih]
    · exact ih

/-- A walk to an ancestor gives the same result in a store that holds the same blocks on it.

The second store must hold, at each root that the walk of the first visits, the same block. -/
theorem getAncestor_of_agree {node ancestor : ForkChoiceNode} {slot : Slot}
    (agree : ∀ later visited, slot ≤ later → first.getAncestor node later = .ok visited →
      second.blocks[visited.root]? = first.blocks[visited.root]?)
    (walk : first.getAncestor node slot = .ok ancestor) :
    second.getAncestor node slot = .ok ancestor := by
  induction node using getAncestor.induct (store := first) (slot := slot) with
  | case1 node found =>
    rw [getAncestor] at walk
    split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block found le =>
    rw [getAncestor_of_le found le] at walk
    cases walk
    have h := agree slot _ (UInt64.le_refl _) (getAncestor_of_le found le)
    rw [found] at h
    exact getAncestor_of_le h le
  | case3 node block found above parentFound =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case4 node block found above parent parentFound lower ih =>
    rw [getAncestor_step found above parentFound lower] at walk
    have nodeAgree := agree _ node (UInt64.le_of_lt (UInt64.not_le.mp above))
      (getAncestor_of_le found (UInt64.le_refl _))
    have parentAgree : second.blocks[block.parentRoot]? = first.blocks[block.parentRoot]? := by
      by_cases le : slot ≤ parent.slot
      · exact agree _ _ le (getAncestor_parent_of_slot_lt found parentFound lower)
      · have h : first.getAncestor node slot =
            .ok ⟨block.parentRoot, parentPayloadStatus block parent⟩ := by
          rw [getAncestor_step found above parentFound lower]
          exact getAncestor_of_le parentFound (UInt64.le_of_lt (UInt64.not_le.mp le))
        exact agree _ _ (UInt64.le_refl _) h
    have parentAgree' := parentAgree
    rw [found] at nodeAgree
    rw [parentFound] at parentAgree'
    rw [getAncestor_step nodeAgree above parentAgree' lower]
    apply ih _ walk
    intro later visited hle hw
    by_cases hb : block.slot ≤ later
    · rw [getAncestor_of_le parentFound (UInt64.le_trans (UInt64.le_of_lt lower) hb)] at hw
      cases hw
      exact parentAgree
    · rw [← getAncestor_step found hb parentFound lower] at hw
      exact agree later visited hle hw
  | case5 node block found above parent parentFound notLower =>
    rw [getAncestor] at walk
    split at walk
    · simp_all
    · rename_i b same
      rw [found, Option.some.injEq] at same
      subst same
      simp only [above, ↓reduceIte] at walk
      split at walk
      · simp_all
      · rename_i p same
        rw [parentFound, Option.some.injEq] at same
        subst same
        simp [notLower, throw, throwThe, MonadExceptOf.throw] at walk

/-- A walk to an ancestor carries over to a store that holds a block at each root it visits.

It carries over, or the search over a list of roots that covers the walk names a collision.

For reachable stores, the root it names is the hash tree root of two different blocks. -/
theorem getAncestor_transport_or_collision {node ancestor : ForkChoiceNode} {slot : Slot}
    {roots : List Root}
    (cover : ∀ later visited, slot ≤ later → first.getAncestor node later = .ok visited →
      visited.root ∈ roots)
    (known : ∀ later visited, slot ≤ later → first.getAncestor node later = .ok visited →
      second.blocks.contains visited.root)
    (walk : first.getAncestor node slot = .ok ancestor) :
    second.getAncestor node slot = .ok ancestor ∨
      ∃ collision, findBlockCollision first second roots = some collision := by
  by_cases none : findBlockCollision first second roots = none
  · exact .inl (getAncestor_of_agree (agree_of_findBlockCollision_none none cover known) walk)
  · exact .inr (Option.ne_none_iff_exists'.mp none)

/-- Ancestry carries over to a store that holds the ancestor and each block of the walk to it.

It carries over, or the search over a list of roots names a collision.

The list must hold the root of the ancestor and each root of the walk. -/
theorem isAncestor_transport_or_collision {node ancestor : ForkChoiceNode}
    {ancestorBlock : BeaconBlock preset fork} {result : Bool} {roots : List Root}
    (found : first.blocks[ancestor.root]? = some ancestorBlock)
    (knownAncestor : second.blocks.contains ancestor.root) (coverAncestor : ancestor.root ∈ roots)
    (cover : ∀ later visited, ancestorBlock.slot ≤ later →
      first.getAncestor node later = .ok visited → visited.root ∈ roots)
    (known : ∀ later visited, ancestorBlock.slot ≤ later →
      first.getAncestor node later = .ok visited → second.blocks.contains visited.root)
    (ancestry : first.isAncestor node ancestor = .ok result) :
    second.isAncestor node ancestor = .ok result ∨
      ∃ collision, findBlockCollision first second roots = some collision := by
  by_cases none : findBlockCollision first second roots = none
  · refine .inl ?_
    obtain ⟨b₂, h₂⟩ : ∃ b₂, second.blocks[ancestor.root]? = some b₂ := by
      rw [Std.TreeMap.contains_eq_isSome_getElem?] at knownAncestor
      exact Option.isSome_iff_exists.mp knownAncestor
    have eq := eq_of_findBlockCollision_none none coverAncestor found h₂
    subst eq
    have agree := agree_of_findBlockCollision_none none cover known
    unfold isAncestor at ancestry ⊢
    simp only [block_ok_iff.mpr found, block_ok_iff.mpr h₂, bind, Except.bind] at ancestry ⊢
    split at ancestry
    · simp at ancestry
    · rename_i f walk
      rw [getAncestor_of_agree agree walk]
      exact ancestry
  · exact .inr (Option.ne_none_iff_exists'.mp none)

end Store

end EthLib.Consensus
