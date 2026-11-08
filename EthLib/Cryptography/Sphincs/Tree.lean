module

public import EthLib.Cryptography.Merkle.Tree
public import EthLib.Cryptography.Sphincs.Ots

/-!
# The trees of the leanSPHINCS hypertree

The Merkle trees of the hypertree, whose leaves are one-time keys.

Tree `tau` of layer `l` has height `h_l`, and for `1 <= z <= h_l`:

```text
    X_{0,e} = the leaf of one-time key (l, tau, e)
    X_{z,j} = H(PK.seed, ADRS_node(l, tau, z, j), X_{z-1,2j} | X_{z-1,2j+1})
```

Its root is `X_{h_l,0}`, and the top tree's root is `PK.root`.

A signature carries its key's path: the sibling of every node on the way up.

For example, in a tree of height 2 with leaves `l_0` to `l_3`, the path of `l_2` is:

- `l_3`, its sibling at height 0.
- `X_{1,0}`, the sibling of its parent at height 1.

The trees of a layer are the shared Merkle trees of EthLib.

Their node hash puts the height and the index of the node into its address.

Every definition takes the hash `H`.

A node computes its left subtree, then its right subtree, then its own hash.

Source: [main.tex][main] §4, and FIPS 205's `xmss_node` and `xmss_pkFromSig` (§6).

[main]: https://github.com/leanEthereum/leanVM/blob/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/doc/lean_sphincs/main.tex
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- No layer is taller than the top one. -/
theorem Layer.height_le (layer : Layer) : layer.height ≤ TOP_HEIGHT := by
  cases layer <;> decide

/-! ## Nodes -/

/-- The parent at index `j` and height `z` of tree `tree` of a layer, from its two children. -/
def nodeHash (pkSeed : PkSeed) (layer : Layer) (tree z j : Nat) (left right : Digest) :
    m Digest :=
  -- The payload is the left child, then the right child.
  th H pkSeed (adrsNode layer tree z j) (packBytes left ++ packBytes right)

/-- `X_{0,e}`: the leaf of one-time key `e` of tree `tree` of a layer. -/
def leaves (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (tree e : Nat) : m Digest :=
  otsPublicLeaf H pkSeed prf ⟨layer, tree, e⟩

/-- `X_{z,j}`: node `j` at height `z` of tree `tree` of a layer, FIPS 205's `xmss_node`.

Computing it evaluates the `2^z` one-time keys below it. -/
def node (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (tree z j : Nat) : m Digest :=
  Merkle.node (nodeHash H pkSeed layer tree) (leaves H pkSeed prf layer tree) z j

/-- The root of tree `tree` of a layer: its one node at the top height. -/
def treeRoot (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (tree : Nat) : m Digest :=
  Merkle.root (nodeHash H pkSeed layer tree) (leaves H pkSeed prf layer tree) layer.height

/-! ## The path -/

/-- The path of key `e` of tree `tree`, from the leaf up, height 0 first.

```text
    P_z = X_{z, floor(e / 2^z) xor 1}
```
-/
def path (pkSeed : PkSeed) (prf : Prf m) (layer : Layer) (tree e : Nat) :
    m (Vector Digest layer.height) :=
  Merkle.path (nodeHash H pkSeed layer tree) (leaves H pkSeed prf layer tree) layer.height e

/-- `Tree.fold`: the root a path leads to from the leaf of key `e` of tree `tree`.

It is the climb of FIPS 205's `xmss_pkFromSig`. -/
def fold (pkSeed : PkSeed) (layer : Layer) (tree e : Nat) (leaf : Digest)
    (pi : Vector Digest layer.height) : m Digest :=
  Merkle.climb (nodeHash H pkSeed layer tree) 0 e leaf pi.toList

end EthLib.Cryptography.Sphincs
