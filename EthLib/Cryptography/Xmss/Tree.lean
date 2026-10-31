import EthLib.Cryptography.Merkle.Tree
import EthLib.Cryptography.Xmss.Ots

/-!
# `Xmss.Tree`

The Merkle trees of one layer, whose leaves are the layer's one-time keys.

On layer `l`, for `1 <= lambda <= 16`:

```text
    X_{lambda,j} = Th(P, A_node(l, lambda, j), X_{lambda-1,2j} | X_{lambda-1,2j+1})
```

- The top layer is one tree, with root `X_{16,0}`.
- The bottom layer is `2^16` trees whose node indices are global.
- Level `lambda` of the bottom layer has `2^(32 - lambda)` nodes.
- Bottom tree `b` holds the nodes `j` with `floor(j / 2^(16 - lambda)) = b`.
- Its root is `X_{16,b}`.

A signature carries its key's path: the sibling of every node on the way up.

For example, in a tree of height 2 with leaves `l_0` to `l_3`, the path of `l_2` is:

- `l_3`, its sibling on level 0;
- `X_{1,0}`, the sibling of its parent on level 1.

These are Merkle trees whose node hash reads the node's position into its address.

Source: the leanXMSS specification draft, section "Trees".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Nodes -/

/-- The parent at index `j` on `level`, from its two children.

The level is read into the address as a level of a layer, from 1 to 16 in a tree. -/
def nodeHash (pp : PublicParam) (layer : Layer) (level j : Nat) (left right : Digest) : Digest :=
  -- The payload is the left child, then the right child.
  th pp (addrNode layer (Fin.ofNat _ level) (UInt32.ofNat j)) (packBytes left ++ packBytes right)

/-- `X_{0,j}`: the leaf of one-time key `j`. -/
def leaves (pp : PublicParam) (seed : Seed) (layer : Layer) (j : Nat) : Digest :=
  otsPublicLeaf pp seed layer (UInt32.ofNat j)

/-- `X_{level,j}`: node `j` on `level` of a layer.

Computing it evaluates the `2^level` leaves below it. -/
def node (pp : PublicParam) (seed : Seed) (layer : Layer) (level j : Nat) : Digest :=
  Merkle.node (nodeHash pp layer) (leaves pp seed layer) level j

/-! ## The path -/

/-- The path of key `e`, from the leaf up.

```text
    pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}
```
-/
def path (pp : PublicParam) (seed : Seed) (layer : Layer) (e : Nat) :
    Vector Digest LAYER_HEIGHT :=
  Merkle.path (nodeHash pp layer) (leaves pp seed layer) LAYER_HEIGHT e

/-- `Tree.fold(l, e, X, pi)`: the root a path leads to from the leaf of key `e`. -/
def fold (pp : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) : Digest :=
  Merkle.climb (nodeHash pp layer) 0 e leaf pi.toList

end EthLib.Cryptography.Xmss
