/-!
# `Merkle.Tree`

A perfect binary Merkle tree of height `h`, whose node hash may read the node's position.

For `1 <= lambda <= h`:

```text
    X_{0,j}      = leaves(j)
    X_{lambda,j} = nodeHash(lambda, j, X_{lambda-1,2j}, X_{lambda-1,2j+1})
```

- A hash-based signature puts `lambda` and `j` into an address, so every node hashes under its own tweak.
- A plain tree, such as SSZ's, ignores them and hashes every node the same way.

The root is `X_{h,0}`.

The path of leaf `e` holds the sibling of each of its ancestors, from the leaf up.

Folding a leaf with its path climbs back to the root.

Source: [RFC 8391](https://www.rfc-editor.org/rfc/rfc8391) §4.1.6 (`treeHash`), §4.1.9 (`buildAuth`) and §4.1.10 (`XMSS_rootFromSig`).
-/

namespace EthLib.Cryptography.Merkle

variable {α : Type} {height : Nat}

/-! ## Nodes -/

/-- `X_{level,j}`: node `j` on `level`.

The node hash receives the level of the parent it computes, from `1` to `height`.

Computing a node evaluates the `2^level` leaves below it. -/
def node (nodeHash : Fin (height + 1) → Nat → α → α → α) (leaves : Nat → α) :
    (level : Nat) → level ≤ height → (j : Nat) → α
  | 0, _, j => leaves j
  -- The children of node `j` on level `l + 1` are `2j` and `2j + 1` on level `l`.
  | l + 1, h, j => nodeHash ⟨l + 1, by omega⟩ j
      (node nodeHash leaves l (by omega) (2 * j)) (node nodeHash leaves l (by omega) (2 * j + 1))

/-- The root: the one node on the top level. -/
def root (nodeHash : Fin (height + 1) → Nat → α → α → α) (leaves : Nat → α) : α :=
  node nodeHash leaves height (Nat.le_refl _) 0

/-! ## The path -/

/-- The sibling of leaf `e`'s ancestor on `level`: that ancestor with its low bit flipped. -/
def siblingIndex (e level : Nat) : Nat :=
  (e >>> level) ^^^ 1

/-- The path of leaf `e`, from the leaf up.

```text
    pi_lambda = X_{lambda, floor(e / 2^lambda) xor 1}
```
-/
def path (nodeHash : Fin (height + 1) → Nat → α → α → α) (leaves : Nat → α) (e : Nat) :
    Vector α height :=
  Vector.ofFn fun level => node nodeHash leaves level (by omega) (siblingIndex e level)

/-! ## Climbing a path -/

namespace Internal

/-- Hash the node held on `level` with its sibling into their parent.

Bit `level` of `e` says which child the held node is. -/
def climbStep (nodeHash : Fin (height + 1) → Nat → α → α → α) (e : Nat) (level : Fin height)
    (current sibling : α) : α :=
  -- The parent sits one level up, at the index with one more bit shifted out.
  let parent : Fin (height + 1) := ⟨level.val + 1, by omega⟩
  if (e >>> level.val) % 2 == 0 then
    -- Bit zero: the held node is the left child.
    nodeHash parent (e >>> (level.val + 1)) current sibling
  else
    -- Bit one: the held node is the right child.
    nodeHash parent (e >>> (level.val + 1)) sibling current

/-- Climb the bottom `levels` levels of a path, starting from a leaf. -/
def climbUpto (nodeHash : Fin (height + 1) → Nat → α → α → α) (e : Nat) (pi : Vector α height)
    (leaf : α) : (levels : Nat) → levels ≤ height → α
  | 0, _ => leaf
  -- The last step folds in the sibling on `l`, after climbing the `l` levels below it.
  | l + 1, h => climbStep nodeHash e ⟨l, by omega⟩
      (climbUpto nodeHash e pi leaf l (by omega)) (pi[l]'(by omega))

end Internal

/-- The root a path leads to from leaf `e`, whose value is `leaf`. -/
def fold (nodeHash : Fin (height + 1) → Nat → α → α → α) (e : Nat) (leaf : α)
    (pi : Vector α height) : α :=
  Internal.climbUpto nodeHash e pi leaf height (Nat.le_refl _)

end EthLib.Cryptography.Merkle
