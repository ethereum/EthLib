module

public import EthLib.Cryptography.Merkle.Tree
public import EthLib.Cryptography.Sphincs.Ots

/-!
# The trees of the leanSPHINCS hypertree

The Merkle trees of the hypertree, whose leaves are one-time keys.

Tree `tau` of layer `l` has height `h_l`, and for `1 <= lambda <= h_l`:

```text
    X_{0,j}      = the leaf of one-time key (l, tau, j)
    X_{lambda,j} = Th(P, A_node(l, tau, lambda, j), X_{lambda-1,2j} | X_{lambda-1,2j+1})
```

Its root is `X_{h_l,0}`.

A signature carries its key's path: the sibling of every node on the way up.

For example, in a tree of height 2 with leaves `l_0` to `l_3`, the path of `l_2` is:

- `l_3`, its sibling on level 0.
- `X_{1,0}`, the sibling of its parent on level 1.

The trees of a layer are the shared Merkle trees of EthLib.

Their node hash reads the position of the node into its address.

They are pure, so they run in the identity monad.

Source: `Seeded.treeNode`, `Seeded.treePath` and `treeFold` in FORS/Scheme.lean.
<https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean>
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- No layer is taller than the top one, so every level of a tree fits a node address. -/
theorem Layer.height_le (layer : Layer) : layer.height ≤ TOP_HEIGHT := by
  cases layer <;> decide

/-! ## Nodes -/

/-- The parent at index `j` on `level` of tree `tree` of a layer, from its two children.

The address holds the level modulo 11.

The tree hashes only at levels 1 to its height, at most 10, so the address names the true level. -/
def nodeHash (pp : PublicParam) (layer : Layer) (tree level j : Nat) (left right : Digest) : Id Digest :=
  -- The payload is the left child, then the right child.
  th pp (addrNode layer tree (Fin.ofNat _ level) j) (packBytes left ++ packBytes right)

/-- `X_{0,j}`: the leaf of one-time key `j` of tree `tree` of a layer. -/
def leaves (pp : PublicParam) (seed : Seed) (layer : Layer) (tree j : Nat) : Id Digest :=
  otsPublicLeaf pp seed ⟨layer, tree, j⟩

/-- `X_{level,j}`: node `j` on `level` of tree `tree` of a layer.

Computing it evaluates the `2^level` one-time keys below it. -/
def node (pp : PublicParam) (seed : Seed) (layer : Layer) (tree level j : Nat) : Digest :=
  (Merkle.node (nodeHash pp layer tree) (leaves pp seed layer tree) level j).run

/-- The root of tree `tree` of a layer: its one node on the top level. -/
def treeRoot (pp : PublicParam) (seed : Seed) (layer : Layer) (tree : Nat) : Digest :=
  (Merkle.root (nodeHash pp layer tree) (leaves pp seed layer tree) layer.height).run

/-! ## The path -/

/-- The path of key `e` of tree `tree`, from the leaf up, level 0 first.

```text
    pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}
```
-/
def path (pp : PublicParam) (seed : Seed) (layer : Layer) (tree e : Nat) : Vector Digest layer.height :=
  (Merkle.path (nodeHash pp layer tree) (leaves pp seed layer tree) layer.height e).run

/-- `Tree.fold`: the root a path leads to from the leaf of key `e` of tree `tree`. -/
def fold (pp : PublicParam) (layer : Layer) (tree e : Nat) (leaf : Digest)
    (pi : Vector Digest layer.height) : Digest :=
  (Merkle.climb (nodeHash pp layer tree) 0 e leaf pi.toList).run

end EthLib.Cryptography.Sphincs
