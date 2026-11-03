module

public import EthLib.Cryptography.Sphincs.Tree
public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: `Sphincs.Tree`

An honest path leads from a key's leaf to the root of its tree.

The key `e` of a tree of height `h` reaches node `floor(e / 2^h)` on the top level.

So a key below `2^h`, which every key of the tree is, reaches the root.

The tree hashes only at levels 1 to its height, so no node address holds a level reduced modulo 11.

Each statement specializes one proved for every Merkle tree.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {pp : PublicParam} {seed : Seed} {layer : Layer} {tree : Nat}

/-! ## Unfolding a node -/

/-- A node on level 0 is the leaf of one-time key `j`. -/
theorem node_zero (j : Nat) : node pp seed layer tree 0 j = otsPublicLeaf pp seed ⟨layer, tree, j⟩ :=
  rfl

/-- A node above level 0 is the hash of its two children. -/
theorem node_succ (l j : Nat) :
    node pp seed layer tree (l + 1) j
      = nodeHash pp layer tree (l + 1) j (node pp seed layer tree l (2 * j))
          (node pp seed layer tree l (2 * j + 1)) :=
  rfl

/-! ## Every level is read exactly -/

/-- On levels up to 10, the node hash reads its level exactly into the address. -/
theorem nodeHash_of_le {level : Nat} (hlevel : level ≤ TOP_HEIGHT) (j : Nat) (left right : Digest) :
    nodeHash pp layer tree level j left right
      = th pp (addrNode layer tree ⟨level, by omega⟩ j) (packBytes left ++ packBytes right) := by
  simp only [nodeHash, Fin.ofNat, Nat.mod_eq_of_lt (Nat.lt_succ_of_le hlevel)]

/-- A path is the same with any node hash that agrees on the levels of the tree. -/
theorem path_eq_of_agree (hash' : Nat → Nat → Digest → Digest → Id Digest)
    (agree : ∀ k, 1 ≤ k → k ≤ layer.height → nodeHash pp layer tree k = hash' k) (e : Nat) :
    path pp seed layer tree e = (Merkle.path hash' (leaves pp seed layer tree) layer.height e).run := by
  rw [path, Merkle.path_congr _ hash' _ _ e fun k h1 h2 => agree k h1 (by omega)]

/-- A fold is the same with any node hash that agrees on the levels of the tree. -/
theorem fold_eq_of_agree (hash' : Nat → Nat → Digest → Digest → Id Digest)
    (agree : ∀ k, 1 ≤ k → k ≤ layer.height → nodeHash pp layer tree k = hash' k) (e : Nat)
    (leaf : Digest) (pi : Vector Digest layer.height) :
    fold pp layer tree e leaf pi = (Merkle.climb hash' 0 e leaf pi.toList).run := by
  rw [fold, Merkle.climb_congr _ hash' _ 0 e leaf fun k h1 h2 => agree k (by omega) (by simpa using h2)]

/-- The root is the same with any node hash that agrees on the levels of the tree. -/
theorem treeRoot_eq_of_agree (hash' : Nat → Nat → Digest → Digest → Id Digest)
    (agree : ∀ k, 1 ≤ k → k ≤ layer.height → nodeHash pp layer tree k = hash' k) :
    treeRoot pp seed layer tree = (Merkle.root hash' (leaves pp seed layer tree) layer.height).run := by
  rw [treeRoot, Merkle.root, Merkle.root, Merkle.node_congr _ hash' _ _ 0 agree]

/-! ## The path reaches the root -/

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^h)` on the top level. -/
theorem fold_path (e : Nat) :
    fold pp layer tree e (node pp seed layer tree 0 e) (path pp seed layer tree e)
      = node pp seed layer tree layer.height (e / 2 ^ layer.height) :=
  Merkle.climb_path (nodeHash pp layer tree) (leaves pp seed layer tree) _ _

/-- A key of the tree, below `2^h`, reaches the tree's root. -/
theorem fold_path_root {e : Nat} (he : e < 2 ^ layer.height) :
    fold pp layer tree e (otsPublicLeaf pp seed ⟨layer, tree, e⟩) (path pp seed layer tree e)
      = treeRoot pp seed layer tree :=
  Merkle.climb_path_root (nodeHash pp layer tree) (leaves pp seed layer tree) he

end EthLib.Cryptography.Sphincs
