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

```text
level 2                 root
                      /      \
level 1          n_0            n_1
                /   \          /   \
level 0     l_0     l_1     l_2     l_3

signed leaf l_2
path        l_3 on level 0, then n_0 on level 1
```

The tree is `Merkle.node`, with `nodeHash` as its node hash and the one-time keys as its leaves.

Source: the leanXMSS specification draft, section "Trees".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Nodes -/

/-- The parent at index `j` on `level`, from its two children. -/
def nodeHash (pp : PublicParam) (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : Nat)
    (left right : Digest) : Digest :=
  -- The payload is the left child, then the right child.
  th pp (addrNode layer level (UInt32.ofNat j)) (packBytes left ++ packBytes right)

/-- The leaves of a layer: leaf `j` is one-time key `j`'s. -/
def leaves (pp : PublicParam) (seed : Seed) (layer : Layer) (j : Nat) : Digest :=
  otsPublicLeaf pp seed layer (UInt32.ofNat j)

/-- `X_{level,j}`: node `j` on `level` of a layer.

Computing it evaluates the `2^level` leaves below it. -/
def node (pp : PublicParam) (seed : Seed) (layer : Layer) :
    (level : Nat) → level ≤ LAYER_HEIGHT → (j : Nat) → Digest :=
  Merkle.node (nodeHash pp layer) (leaves pp seed layer)

/-! ## The path -/

/-- The path of key `e`, from the leaf up.

```text
    pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}
```
-/
def path (pp : PublicParam) (seed : Seed) (layer : Layer) (e : Nat) :
    Vector Digest LAYER_HEIGHT :=
  Merkle.path (nodeHash pp layer) (leaves pp seed layer) e

/-! ## Climbing a path -/

/-- `Tree.fold(l, e, X, pi)`: the root a path leads to from a leaf.

Bit `lambda` of `e` says whether the node held on level `lambda` is the left or the right child. -/
def fold (pp : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) : Digest :=
  Merkle.fold (nodeHash pp layer) e leaf pi

end EthLib.Cryptography.Xmss
