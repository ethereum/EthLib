module

public import EthLib.Cryptography.Proofs.Merkle.Binding

/-!
# Proofs: the root binds the vector

Two trees of height `h` with one root agree on every leaf below `2^h`, or expose a collision.

It follows from position binding at each leaf, which the binding of two climbs proves.

Catalano and Fiore define position binding in [their paper][cf], section 3, definition 4.

[cf]: https://eprint.iacr.org/2011/495
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Position → α → α → Id α)

/-- Two trees with one root agree at leaf `j < 2^h`, or the search on their paths succeeds. -/
theorem root_binding [DecidableEq α] (leaves leaves' : Nat → Id α) {h j : Nat} (hj : j < 2 ^ h)
    (same : (root hash leaves h).run = (root hash leaves' h).run) :
    (leaves j).run = (leaves' j).run ∨
      (findCollision hash ⟨0, j⟩ (leaves j).run (leaves' j).run
        (path hash leaves h j).run.toList (path hash leaves' h j).run.toList).isSome := by
  -- Both honest climbs reach the shared root.
  have climbs := (climb_path_root hash leaves hj).trans
    (same.trans (climb_path_root hash leaves' hj).symm)
  rcases climb_binding hash _ _ _ _ _ (by simp) climbs with ⟨hleaf, -⟩ | hsome
  · exact .inl hleaf
  · exact .inr hsome

/-- Two trees with one root agree on every leaf below `2^h`, or the search succeeds at some leaf. -/
theorem root_binding_leaves [DecidableEq α] (leaves leaves' : Nat → Id α) {h : Nat}
    (same : (root hash leaves h).run = (root hash leaves' h).run) :
    (∀ j < 2 ^ h, (leaves j).run = (leaves' j).run) ∨
      ∃ j < 2 ^ h, (findCollision hash ⟨0, j⟩ (leaves j).run (leaves' j).run
        (path hash leaves h j).run.toList (path hash leaves' h j).run.toList).isSome := by
  by_cases found : ∃ j < 2 ^ h, (findCollision hash ⟨0, j⟩ (leaves j).run (leaves' j).run
      (path hash leaves h j).run.toList (path hash leaves' h j).run.toList).isSome
  · exact .inr found
  refine .inl fun j hj => (root_binding hash leaves leaves' hj same).resolve_right ?_
  exact fun hsome => found ⟨j, hj, hsome⟩

end EthLib.Cryptography.Merkle
