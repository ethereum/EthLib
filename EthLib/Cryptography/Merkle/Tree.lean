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
- A plain tree ignores it.

The path of a leaf holds the sibling of each of its ancestors, from the leaf up.

Climbing from the leaf with its path recomputes the root, so a path proves its leaf.
-/

namespace EthLib.Cryptography.Merkle

variable {α : Type} (hash : Nat → Nat → α → α → α)

/-! ## Nodes -/

/-- `X_{level,j}`: the node at position `(level, j)`.

Computing it evaluates the `2^level` leaves below it. -/
def node (leaves : Nat → α) : (level j : Nat) → α
  | 0, j => leaves j
  | level + 1, j => hash (level + 1) j (node leaves level (2 * j)) (node leaves level (2 * j + 1))

/-- The root of the tree of height `h`: its node `(h, 0)`. -/
def root (leaves : Nat → α) (h : Nat) : α :=
  node hash leaves h 0

/-! ## Paths -/

/-- The siblings of the node at `(level, j)` and of its next ancestors, `n` nodes from the bottom.

The sibling of a node is the node with the low bit of its index flipped. -/
def siblings (leaves : Nat → α) : (level j n : Nat) → List α
  | _, _, 0 => []
  | level, j, n + 1 => node hash leaves level (j ^^^ 1) :: siblings leaves (level + 1) (j / 2) n

/-- There is one sibling per level. -/
@[simp] theorem length_siblings (leaves : Nat → α) :
    ∀ level j n, (siblings hash leaves level j n).length = n
  | _, _, 0 => rfl
  | level, j, n + 1 => by simp [siblings, length_siblings leaves (level + 1) (j / 2) n]

/-- The path of leaf `j` in the tree of height `h`, from the leaf up. -/
def path (leaves : Nat → α) (h j : Nat) : Vector α h :=
  ⟨⟨siblings hash leaves 0 j h⟩, by simp⟩

/-! ## Climbing -/

/-- The node reached by climbing from the node `current` at `(level, j)`, one sibling per level.

The low bit of `j` says whether `current` is the left or the right child.

Its parent sits at `(level + 1, j / 2)`. -/
def climb : (level j : Nat) → (current : α) → (siblings : List α) → α
  | _, _, current, [] => current
  | level, j, current, sibling :: rest =>
    climb (level + 1) (j / 2)
      (if j % 2 = 0 then hash (level + 1) (j / 2) current sibling
        else hash (level + 1) (j / 2) sibling current) rest

end EthLib.Cryptography.Merkle
