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

/-- `X_{level,j}`: node `j` on `level` of a layer.

Computing it evaluates the `2^level` leaves below it. -/
def node (pp : PublicParam) (seed : Seed) (layer : Layer) :
    (level : Nat) → level ≤ LAYER_HEIGHT → (j : Nat) → Digest
  -- One leaf per one-time key, and the key's index is the leaf's.
  | 0, _, j => otsPublicLeaf pp seed layer (UInt32.ofNat j)
  -- The children of node `j` on level `l + 1` are `2j` and `2j + 1` on level `l`.
  | l + 1, h, j => nodeHash pp layer ⟨l + 1, by omega⟩ j
      (node pp seed layer l (by omega) (2 * j)) (node pp seed layer l (by omega) (2 * j + 1))

/-! ## The path -/

/-- The sibling of key `e`'s ancestor on `level`: that ancestor with its low bit flipped. -/
def siblingIndex (e level : Nat) : Nat :=
  (e >>> level) ^^^ 1

/-- The path of key `e`, from the leaf up.

```text
    pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}
```
-/
def path (pp : PublicParam) (seed : Seed) (layer : Layer) (e : Nat) :
    Vector Digest LAYER_HEIGHT :=
  Vector.ofFn fun level => node pp seed layer level (by omega) (siblingIndex e level)

/-! ## Climbing a path -/

namespace Internal

/-- Hash the node held on `level` with its sibling into their parent.

Bit `level` of `e` says which child the held node is. -/
def climbStep (pp : PublicParam) (layer : Layer) (e : Nat) (level : Fin LAYER_HEIGHT)
    (current sibling : Digest) : Digest :=
  -- The parent sits one level up, at the index with one more bit shifted out.
  let parent : Fin (LAYER_HEIGHT + 1) := ⟨level.val + 1, by omega⟩
  if (e >>> level.val) % 2 == 0 then
    -- Bit zero: the held node is the left child.
    nodeHash pp layer parent (e >>> (level.val + 1)) current sibling
  else
    -- Bit one: the held node is the right child.
    nodeHash pp layer parent (e >>> (level.val + 1)) sibling current

/-- Climb the bottom `levels` levels of a path, starting from a leaf. -/
def climbUpto (pp : PublicParam) (layer : Layer) (e : Nat) (pi : Vector Digest LAYER_HEIGHT)
    (leaf : Digest) : (levels : Nat) → levels ≤ LAYER_HEIGHT → Digest
  | 0, _ => leaf
  -- The last step folds in the sibling on `l`, after climbing the `l` levels below it.
  | l + 1, h => climbStep pp layer e ⟨l, by omega⟩
      (climbUpto pp layer e pi leaf l (by omega)) (pi[l]'(by omega))

end Internal

/-- `Tree.fold(l, e, X, pi)`: the root a path leads to from a leaf. -/
def fold (pp : PublicParam) (layer : Layer) (e : Nat) (leaf : Digest)
    (pi : Vector Digest LAYER_HEIGHT) : Digest :=
  Internal.climbUpto pp layer e pi leaf LAYER_HEIGHT (Nat.le_refl _)

end EthLib.Cryptography.Xmss
