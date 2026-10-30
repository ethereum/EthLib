import EthLib.Cryptography.Xmss.Tree
import EthLib.Cryptography.Proofs.Merkle.Binding

/-!
# Proofs: `Xmss.Tree`

An honest path leads from a key's leaf to the root of its tree.

On the bottom layer, key `idx` reaches the root of bottom tree `floor(idx / 2^16)`.

On the top layer, key `b < 2^16` reaches the root of the one top tree.

A forged path that reaches the same root exposes a second preimage of `Th`.

Each statement specializes one proved for every Merkle tree.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {pp : PublicParam} {seed : Seed} {layer : Layer}

/-! ## Unfolding a node -/

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (l : Nat) (h : l + 1 ≤ LAYER_HEIGHT) (j : Nat) :
    node pp seed layer (l + 1) h j = nodeHash pp layer ⟨l + 1, by omega⟩ j
      (node pp seed layer l (by omega) (2 * j)) (node pp seed layer l (by omega) (2 * j + 1)) :=
  rfl

/-! ## The path reaches the root -/

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^16)` on the top level. -/
theorem fold_path (e : Nat) :
    fold pp layer e (node pp seed layer 0 (by omega) e) (path pp seed layer e)
      = node pp seed layer LAYER_HEIGHT (Nat.le_refl _) (e >>> LAYER_HEIGHT) :=
  Merkle.fold_path e

/-- On the top layer, key `b < 2^16` reaches the root of the one top tree. -/
theorem fold_path_top {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT) :
    fold pp .top b (node pp seed .top 0 (by omega) b) (path pp seed .top b)
      = node pp seed .top LAYER_HEIGHT (Nat.le_refl _) 0 :=
  Merkle.fold_path_root hb

/-! ## A path binds its leaf -/

/-- A path from key `e`'s leaf that reaches the root of its tree is honest.

That root is node `floor(e / 2^16)` on the top level: bottom tree `b`'s, or the top tree's.

Otherwise some level `lambda` holds a second preimage of `Th` under `A_node(l, lambda, floor(e / 2^lambda))`:

- one input is that node's two honest children;
- the other is the pair the forged path hashes there.
-/
theorem fold_eq_node_binding {e : Nat} {leaf : Digest} {pi : Vector Digest LAYER_HEIGHT}
    (heq : fold pp layer e leaf pi
      = node pp seed layer LAYER_HEIGHT (Nat.le_refl _) (e >>> LAYER_HEIGHT)) :
    (leaf = node pp seed layer 0 (by omega) e ∧ pi = path pp seed layer e) ∨
      ∃ l : Fin LAYER_HEIGHT, Merkle.Collision (nodeHash pp layer) l.succ (e >>> (l.val + 1))
        (node pp seed layer l (by omega) (2 * (e >>> (l.val + 1))),
          node pp seed layer l (by omega) (2 * (e >>> (l.val + 1)) + 1))
        (Merkle.climbChildren (nodeHash pp layer) e pi leaf l) :=
  Merkle.fold_eq_node_binding heq

end EthLib.Cryptography.Xmss
