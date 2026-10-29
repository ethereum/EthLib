import EthLib.Cryptography.Sphincs.Ots

/-!
# `Sphincs.Tree`

The Merkle trees of the hypertree, whose leaves are one-time keys.

Tree `tau` of layer `l` has height `h_l`, and for `1 <= lambda <= h_l`:

```text
    X_{0,j}      = the leaf of one-time key (l, tau, j)
    X_{lambda,j} = Th(P, A_node(l, tau, lambda, j), X_{lambda-1,2j} | X_{lambda-1,2j+1})
```

Its root is `X_{h_l,0}`.

A signature carries its key's path: the sibling of every node on the way up.

For example, in a tree of height 2 with leaves `l_0` to `l_3`, the path of `l_2` is:

- `l_3`, its sibling on level 0;
- `X_{1,0}`, the sibling of its parent on level 1.

Source: `Seeded.treeNode`, `Seeded.treePath` and `treeFold` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- No layer is taller than the top one, so every level fits a node address. -/
theorem Layer.height_le (layer : Layer) : layer.height ≤ TOP_HEIGHT := by
  cases layer <;> decide

/-! ## Nodes -/

/-- The parent at index `j` on `level` of tree `tree` of a layer, from its two children. -/
def nodeHash (pp : PublicParam) (layer : Layer) (tree : Nat) (level : Fin (TOP_HEIGHT + 1))
    (j : Nat) (left right : Digest) : Digest :=
  -- The payload is the left child, then the right child.
  th pp (addrNode layer tree level j) (packBytes left ++ packBytes right)

/-- `X_{level,j}`: node `j` on `level` of tree `tree` of a layer.

Computing it evaluates the `2^level` one-time keys below it. -/
def node (pp : PublicParam) (seed : Seed) (layer : Layer) (tree : Nat) :
    (level : Nat) → level ≤ layer.height → (j : Nat) → Digest
  -- One leaf per one-time key, and the key's leaf index is the node's.
  | 0, _, j => otsPublicLeaf pp seed ⟨layer, tree, j⟩
  -- The children of node `j` on level `l + 1` are `2j` and `2j + 1` on level `l`.
  | l + 1, h, j =>
    nodeHash pp layer tree ⟨l + 1, by have := layer.height_le; omega⟩ j
      (node pp seed layer tree l (by omega) (2 * j))
      (node pp seed layer tree l (by omega) (2 * j + 1))

/-- The root of tree `tree` of a layer: its one node on the top level. -/
def treeRoot (pp : PublicParam) (seed : Seed) (layer : Layer) (tree : Nat) : Digest :=
  node pp seed layer tree layer.height (Nat.le_refl _) 0

/-! ## The path -/

/-- The sibling of key `e`'s ancestor on `level`: that ancestor with its low bit flipped. -/
def siblingIndex (e level : Nat) : Nat :=
  (e >>> level) ^^^ 1

/-- The path of key `e` of tree `tree`, from the leaf up.

```text
    pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}
```
-/
def path (pp : PublicParam) (seed : Seed) (layer : Layer) (tree e : Nat) :
    Vector Digest layer.height :=
  Vector.ofFn fun level => node pp seed layer tree level (by omega) (siblingIndex e level)

/-! ## Climbing a path -/

namespace Internal

/-- Hash the node held on `level` with its sibling into their parent.

Bit `level` of `e` says which child the held node is. -/
def climbStep (pp : PublicParam) (layer : Layer) (tree e : Nat) (level : Fin layer.height)
    (current sibling : Digest) : Digest :=
  -- The parent sits one level up, at the index with one more bit shifted out.
  let parent : Fin (TOP_HEIGHT + 1) := ⟨level.val + 1, by have := layer.height_le; omega⟩
  if (e >>> level.val) % 2 == 0 then
    -- Bit zero: the held node is the left child.
    nodeHash pp layer tree parent (e >>> (level.val + 1)) current sibling
  else
    -- Bit one: the held node is the right child.
    nodeHash pp layer tree parent (e >>> (level.val + 1)) sibling current

/-- Climb the bottom `levels` levels of a path, starting from a leaf. -/
def climbUpto (pp : PublicParam) (layer : Layer) (tree e : Nat) (pi : Vector Digest layer.height)
    (leaf : Digest) : (levels : Nat) → levels ≤ layer.height → Digest
  | 0, _ => leaf
  -- The last step folds in the sibling on `l`, after climbing the `l` levels below it.
  | l + 1, h => climbStep pp layer tree e ⟨l, by omega⟩
      (climbUpto pp layer tree e pi leaf l (by omega)) (pi[l]'(by omega))

end Internal

/-- `Tree.fold`: the root a path leads to from the leaf of key `e` of tree `tree`. -/
def fold (pp : PublicParam) (layer : Layer) (tree e : Nat) (leaf : Digest)
    (pi : Vector Digest layer.height) : Digest :=
  Internal.climbUpto pp layer tree e pi leaf layer.height (Nat.le_refl _)

end EthLib.Cryptography.Sphincs
