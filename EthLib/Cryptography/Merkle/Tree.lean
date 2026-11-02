module

/-!
# `Merkle.Tree`

Perfect binary Merkle trees.

A tree of height `h` commits to `2^h` leaves with a single node, its root.

Every node has a position `(level, j)`.

- Level 0 holds the leaves, and level `h` holds the root.
- `j` counts the nodes of a level from the left, starting at 0.
- The children of node `(level + 1, j)` are `(level, 2j)` and `(level, 2j + 1)`.

```text
    X_{0,j} = leaves(j)
    X_{level+1,j} = hash(level + 1, j, X_{level,2j}, X_{level,2j+1})
```

The node hash receives the position of the node it computes.

- A tree that tweaks every hash by its position reads it, as hash-based signatures do.
- A tree that hashes every node alike ignores it.

The path of a leaf holds the sibling of each of its ancestors, from the leaf up.

Climbing from the leaf with its path recomputes the root, so a path proves its leaf.

Every definition runs in a monad `m`, so the hash may be an oracle.

A pure tree runs in `Id`.

The order of the hash calls is fixed, so a proof in the random oracle model can count them.

- A node computes its left subtree, then its right subtree, then its own hash.
- A path computes its siblings from the leaf up.
- A climb hashes from the leaf up.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

variable {m : Type → Type} [Monad m] {α : Type} (hash : Nat → Nat → α → α → m α)

/-! ## Nodes -/

/-- `X_{level,j}`: the node at position `(level, j)`.

Computing it evaluates the `2^level` leaves below it. -/
def node (leaves : Nat → m α) : (level j : Nat) → m α
  | 0, j => leaves j
  | level + 1, j => do
    let left ← node leaves level (2 * j)
    let right ← node leaves level (2 * j + 1)
    hash (level + 1) j left right

/-- The root of the tree of height `h`: its node `(h, 0)`. -/
def root (leaves : Nat → m α) (h : Nat) : m α :=
  node hash leaves h 0

/-! ## Paths -/

/-- The siblings of the node at `(level, j)` and of its next ancestors, `n` nodes from the bottom.

The sibling of a node is the node with the low bit of its index flipped. -/
def siblings (leaves : Nat → m α) : (level j n : Nat) → m (Vector α n)
  | _, _, 0 => pure #v[]
  | level, j, n + 1 => do
    let sibling ← node hash leaves level (j ^^^ 1)
    let rest ← siblings leaves (level + 1) (j / 2) n
    return (#v[sibling] ++ rest).cast (Nat.add_comm 1 n)

/-- The path of leaf `j` in the tree of height `h`, from the leaf up. -/
def path (leaves : Nat → m α) (h j : Nat) : m (Vector α h) :=
  siblings hash leaves 0 j h

/-! ## Climbing -/

/-- The node reached by climbing from the node `current` at `(level, j)`, one sibling per level.

The low bit of `j` says whether `current` is the left or the right child.

Its parent sits at `(level + 1, j / 2)`. -/
def climb : (level j : Nat) → (current : α) → (siblings : List α) → m α
  | _, _, current, [] => pure current
  | level, j, current, sibling :: rest => do
    let parent ← if j % 2 = 0 then hash (level + 1) (j / 2) current sibling
      else hash (level + 1) (j / 2) sibling current
    climb (level + 1) (j / 2) parent rest

end EthLib.Cryptography.Merkle
