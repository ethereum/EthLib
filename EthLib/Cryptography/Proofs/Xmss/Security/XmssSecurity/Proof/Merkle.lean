module

public import EthLib.Cryptography.Proofs.Merkle.Binding
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.IdealStatement

/-!
# The model's climb on the shared Merkle tree

The model's node hash takes the held node first and orders the pair itself.

So its climb is the shared climb from index 0, where the held node is always the left input.
-/

@[expose] public section

namespace XmssSecurity.Merkle

open EthLib.Cryptography.Merkle (climb climb_append climb_binding findCollision_valid ordered)

variable {α : Type} (nodeHash : Nat → α → α → α)

/-- Climb `steps` levels from level `position`, with the sibling `path l` on level `l`. -/
def ascend (path : Nat → α) (position steps : Nat) (leaf : α) : α :=
  (climb (m := Id) (fun level _ current sibling => nodeHash (level - 1) current sibling)
    position 0 leaf ((List.range steps).map fun offset => path (position + offset))).run

@[simp] theorem ascend_zero (path : Nat → α) (position : Nat) (leaf : α) :
    ascend nodeHash path position 0 leaf = leaf := rfl

/-- One more level hashes the held node with the next sibling. -/
theorem ascend_succ (path : Nat → α) (position steps : Nat) (leaf : α) :
    ascend nodeHash path position (steps + 1) leaf =
      nodeHash (position + steps) (ascend nodeHash path position steps leaf)
        (path (position + steps)) := by
  simp [ascend, List.range_succ, climb_append, climb, ordered]
  rfl

def SamePathSegment (leftPath rightPath : Nat → α) (position steps : Nat) : Prop :=
  ∀ offset, offset < steps → leftPath (position + offset) = rightPath (position + offset)

def IsXmssPathCollisionAt (leftPath rightPath : Nat → α) (left right : α)
    (level : Fin treeHeight) : Prop :=
  (ascend nodeHash leftPath 0 level.val left, leftPath level.val) ≠
    (ascend nodeHash rightPath 0 level.val right, rightPath level.val) ∧
  nodeHash level.val (ascend nodeHash leftPath 0 level.val left) (leftPath level.val) =
    nodeHash level.val (ascend nodeHash rightPath 0 level.val right) (rightPath level.val)

def HasXmssPathCollision (leftPath rightPath : Nat → α) (left right : α) : Prop :=
  ∃ level, IsXmssPathCollisionAt nodeHash leftPath rightPath left right level

/-- Take an alternative XMSS authentication path that reaches the same root.

It has the same leaf and the same path, or it collides at one of its 16 levels.

A collision at level `l` hashes two different pairs of level-`l` nodes to one node of level `l + 1`.

The shared search finds the lowest such level, and records the parent's level `l + 1`. -/
theorem sameXmssPath_or_hasCollision (leftPath rightPath : Nat → α) (left right : α)
    (hroot : ascend nodeHash leftPath 0 treeHeight left =
      ascend nodeHash rightPath 0 treeHeight right) :
    (left = right ∧ SamePathSegment leftPath rightPath 0 treeHeight) ∨
      HasXmssPathCollision nodeHash leftPath rightPath left right := by
  classical
  rcases climb_binding _ _ _ 0 0 left right (by simp) hroot with ⟨hleaf, hpath⟩ | hfound
  · -- Equal lists of siblings agree at every level.
    refine .inl ⟨hleaf, fun offset hoffset => ?_⟩
    simpa [hoffset] using congrArg (·[offset]?) hpath
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hfound
    obtain ⟨⟨hne, heq⟩, k, s, t, hs, ht, hlevel, _, hx, hy⟩ :=
      findCollision_valid _ _ _ _ _ _ _ c hc
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hs
    obtain ⟨_, rfl⟩ := List.getElem?_eq_some_iff.mp ht
    have hk' : k < treeHeight := by simpa using hk
    -- The collision's pairs hold the nodes both climbs reach after `k` levels, and sibling `k`.
    rw [← List.map_take, List.take_range, Nat.min_eq_left hk'.le] at hx hy
    refine .inr ⟨⟨k, hk'⟩, ?_, ?_⟩
    · simpa [hx, hy, ordered, ascend] using hne
    · simp [hx, hy, hlevel, ordered, ascend] at heq ⊢
      exact heq

end XmssSecurity.Merkle
