import EthLib.Cryptography.Xmss.Tree
import EthLib.Cryptography.Proofs.Merkle.Binding

/-!
# Proofs: `Xmss.Tree`

An honest path leads from a key's leaf to the root of its tree.

On the bottom layer, key `idx` reaches the root of bottom tree `floor(idx / 2^16)`.

On the top layer, key `b < 2^16` reaches the root of the one top tree.

Another path that reaches the same root exposes a second preimage of `Th`, under one node address.

Each statement specializes one proved for every Merkle tree.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {pp : PublicParam} {seed : Seed} {layer : Layer}

/-! ## Unfolding a node -/

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (l j : Nat) :
    node pp seed layer (l + 1) j = nodeHash pp layer (l + 1) j
      (node pp seed layer l (2 * j)) (node pp seed layer l (2 * j + 1)) :=
  rfl

/-! ## The path reaches the root -/

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^16)` on the top level. -/
theorem fold_path (e : Nat) :
    fold pp layer e (node pp seed layer 0 e) (path pp seed layer e)
      = node pp seed layer LAYER_HEIGHT (e >>> LAYER_HEIGHT) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Merkle.climb_path _ _ _ _

/-- On the top layer, key `b < 2^16` reaches the root of the one top tree. -/
theorem fold_path_top {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT) :
    fold pp .top b (node pp seed .top 0 b) (path pp seed .top b)
      = node pp seed .top LAYER_HEIGHT 0 :=
  Merkle.climb_path_root _ _ hb

/-! ## A path binds its leaf -/

/-- A path from key `e`'s leaf that reaches the root of its tree is honest.

That root is node `floor(e / 2^16)` on the top level: bottom tree `b`'s, or the top tree's.

Otherwise some level holds a second preimage of `Th` under the address of an ancestor of the leaf:

- one input is that ancestor's two honest children;
- the other is a different pair with the same hash.
-/
theorem fold_binding {e : Nat} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (heq : fold pp layer e leaf pi = node pp seed layer LAYER_HEIGHT (e >>> LAYER_HEIGHT)) :
    (leaf = node pp seed layer 0 e ∧ pi = path pp seed layer e) ∨
      ∃ k < LAYER_HEIGHT,
        Merkle.SecondPreimage (nodeHash pp layer) (leaves pp seed layer) k (e / 2 ^ (k + 1)) := by
  rw [Nat.shiftRight_eq_div_pow] at heq
  rcases Merkle.climb_binding_node (nodeHash pp layer) (leaves pp seed layer) LAYER_HEIGHT 0 e
      leaf pi.toList (by simp) heq with ⟨hleaf, hpi⟩ | ⟨k, hk, hsp⟩
  · -- The siblings are the honest path, as lists and so as vectors.
    exact .inl ⟨hleaf, Vector.toList_inj.mp hpi⟩
  · exact .inr ⟨k, hk, by simpa using hsp⟩

end EthLib.Cryptography.Xmss
