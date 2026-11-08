module

public import EthLib.Cryptography.Sphincs.Tree
public import EthLib.Cryptography.Proofs.Merkle.Completeness

/-!
# Proofs: the trees of the leanSPHINCS hypertree

An honest path leads from a key's leaf to the root of its tree.

The key `e` of a tree of height `h` reaches node `floor(e / 2^h)` at the top height.

So a key below `2^h`, which every key of the tree is, reaches the root.

A tree hashes only at heights 1 to its own height, so only those node hashes matter.

Each statement specializes one proved for every Merkle tree.

The unfolding equations hold in every monad.

The other statements hold for every hash function `f`, run in the identity monad.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Unfolding, in any monad -/

section Monad

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))
  {pkSeed : PkSeed} {prf : Prf m} {layer : Layer} {tree : Nat}

/-- A node at height 0 is the leaf of one-time key `j`. -/
theorem node_zero (j : Nat) :
    node H pkSeed prf layer tree 0 j = otsPublicLeaf H pkSeed prf ⟨layer, tree, j⟩ :=
  rfl

/-- A node above height 0 hashes its two children, the left subtree first. -/
theorem node_succ (z j : Nat) :
    node H pkSeed prf layer tree (z + 1) j = (do
      let left ← node H pkSeed prf layer tree z (2 * j)
      let right ← node H pkSeed prf layer tree z (2 * j + 1)
      nodeHash H pkSeed layer tree (z + 1) j left right) :=
  rfl

/-! ## Only the heights of the tree matter -/

/-- A path is the same with any node hash that agrees on the heights of the tree. -/
theorem path_eq_of_agree (hash' : Nat → Nat → Digest → Digest → m Digest)
    (agree : ∀ k, 1 ≤ k → k ≤ layer.height → nodeHash H pkSeed layer tree k = hash' k) (e : Nat) :
    path H pkSeed prf layer tree e
      = Merkle.path hash' (leaves H pkSeed prf layer tree) layer.height e :=
  Merkle.path_congr _ hash' _ _ e fun k h1 h2 => agree k h1 (by omega)

/-- A fold is the same with any node hash that agrees on the heights of the tree. -/
theorem fold_eq_of_agree (hash' : Nat → Nat → Digest → Digest → m Digest)
    (agree : ∀ k, 1 ≤ k → k ≤ layer.height → nodeHash H pkSeed layer tree k = hash' k) (e : Nat)
    (leaf : Digest) (pi : Vector Digest layer.height) :
    fold H pkSeed layer tree e leaf pi = Merkle.climb hash' 0 e leaf pi.toList :=
  Merkle.climb_congr _ hash' _ 0 e leaf fun k h1 h2 => agree k (by omega) (by simpa using h2)

/-- The root is the same with any node hash that agrees on the heights of the tree. -/
theorem treeRoot_eq_of_agree (hash' : Nat → Nat → Digest → Digest → m Digest)
    (agree : ∀ k, 1 ≤ k → k ≤ layer.height → nodeHash H pkSeed layer tree k = hash' k) :
    treeRoot H pkSeed prf layer tree
      = Merkle.root hash' (leaves H pkSeed prf layer tree) layer.height :=
  Merkle.node_congr _ hash' _ _ 0 agree

end Monad

/-! ## The path reaches the root -/

variable {f : ByteArray → Vector UInt8 32} {pkSeed : PkSeed} {prf : Prf Id} {layer : Layer}
  {tree : Nat}

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^h)` at the top height. -/
theorem fold_path (e : Nat) :
    (fold (pureHash f) pkSeed layer tree e (node (pureHash f) pkSeed prf layer tree 0 e).run
        (path (pureHash f) pkSeed prf layer tree e).run).run
      = (node (pureHash f) pkSeed prf layer tree layer.height (e / 2 ^ layer.height)).run :=
  Merkle.climb_path _ _ _ _

/-- A key of the tree, below `2^h`, reaches the tree's root. -/
theorem fold_path_root {e : Nat} (he : e < 2 ^ layer.height) :
    (fold (pureHash f) pkSeed layer tree e
        (otsPublicLeaf (pureHash f) pkSeed prf ⟨layer, tree, e⟩).run
        (path (pureHash f) pkSeed prf layer tree e).run).run
      = (treeRoot (pureHash f) pkSeed prf layer tree).run :=
  Merkle.climb_path_root (nodeHash (pureHash f) pkSeed layer tree)
    (leaves (pureHash f) pkSeed prf layer tree) he

end EthLib.Cryptography.Sphincs
