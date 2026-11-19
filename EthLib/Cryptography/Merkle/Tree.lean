module

/-!
# Perfect binary Merkle trees

A tree of height `h` commits to `2^h` leaves with a single node, its root.

Every node has a position: its level and its index within the level.

- Level 0 holds the leaves, and level `h` holds the root.
- The index counts the nodes of a level from the left, starting at 0.
- A node above the leaves at index `j` has its children one level down, at `2j` and `2j + 1`.

```text
    X_{0,j} = leaves(j)
    X_{level+1,j} = hash(level + 1, j, X_{level,2j}, X_{level,2j+1})
```

The node hash receives the position of the node it computes.

- A tree that tweaks every hash by its position reads it, as hash-based signatures do.
- A tree that hashes every node alike ignores it.

The tree never hashes on its own.

The path of a leaf holds the sibling of each of its ancestors, from the leaf up.

Climbing from the leaf with its path recomputes the root, so a path proves its leaf.

A build computes every node under a position once, and keeps them all.

So one build gives both the node at the position and the path of each leaf below it.

Every definition runs in a monad `m`, so the hash may be an oracle.

A pure tree runs in `Id`.

The order of the hash calls is fixed, so a proof in the random oracle model can count them.

- A node computes its left subtree, then its right subtree, then its own hash.
- A build makes the calls of the node at its position, in the same order.
- A path computes its siblings from the leaf up.
- A climb hashes from the leaf up.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

/-! ## Positions -/

/-- The position of a node: its level, counted from the leaves, and its index within the level. -/
@[ext] structure Position where
  /-- The level of the node, 0 for the leaves. -/
  level : Nat
  /-- The index of the node within its level, from the left, starting at 0. -/
  index : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Position

/-- The parent of a node, one level up. -/
def parent (p : Position) : Position :=
  ⟨p.level + 1, p.index / 2⟩

/-- The sibling of a node: the other child of its parent, with the low bit of the index flipped. -/
def sibling (p : Position) : Position :=
  ⟨p.level, p.index ^^^ 1⟩

/-- The left child of a node above the leaves.

At level 0 it is the node at level 0 and at twice the index, which is not a child. -/
def left (p : Position) : Position :=
  ⟨p.level - 1, 2 * p.index⟩

/-- The right child of a node above the leaves.

At level 0 it is the node at level 0 and at twice the index plus 1, which is not a child. -/
def right (p : Position) : Position :=
  ⟨p.level - 1, 2 * p.index + 1⟩

/-- The ancestor of a node `k` levels up. -/
def ancestor (p : Position) (k : Nat) : Position :=
  ⟨p.level + k, p.index / 2 ^ k⟩

/-- A node is an ancestor of another when it sits zero or more levels above it, on its path. -/
def IsAncestor (a p : Position) : Prop :=
  ∃ k, a = p.ancestor k

/-- Whether a node is the left child of its parent: its index is even. -/
def isLeft (p : Position) : Bool :=
  p.index % 2 = 0

@[simp] theorem parent_level (p : Position) : p.parent.level = p.level + 1 := rfl
@[simp] theorem parent_index (p : Position) : p.parent.index = p.index / 2 := rfl
@[simp] theorem sibling_level (p : Position) : p.sibling.level = p.level := rfl
@[simp] theorem sibling_index (p : Position) : p.sibling.index = p.index ^^^ 1 := rfl
@[simp] theorem left_level (p : Position) : p.left.level = p.level - 1 := rfl
@[simp] theorem left_index (p : Position) : p.left.index = 2 * p.index := rfl
@[simp] theorem right_level (p : Position) : p.right.level = p.level - 1 := rfl
@[simp] theorem right_index (p : Position) : p.right.index = 2 * p.index + 1 := rfl
@[simp] theorem ancestor_level (p : Position) (k : Nat) : (p.ancestor k).level = p.level + k := rfl

@[simp] theorem ancestor_index (p : Position) (k : Nat) :
    (p.ancestor k).index = p.index / 2 ^ k := rfl

end Position

variable {m : Type → Type} [Monad m] {α : Type} (hash : Position → α → α → m α)

/-! ## Nodes -/

/-- The recursion behind a node: the node at level `level` and index `j`.

It recurses on the level, so it unfolds by definition. -/
def node.go (leaves : Nat → m α) : (level j : Nat) → m α
  | 0, j => leaves j
  | level + 1, j => do
    let left ← node.go leaves level (2 * j)
    let right ← node.go leaves level (2 * j + 1)
    hash ⟨level + 1, j⟩ left right

/-- The node at a position.

Computing it evaluates the `2^l` leaves below it, for the level `l` of the position. -/
def node (leaves : Nat → m α) (p : Position) : m α :=
  node.go hash leaves p.level p.index

/-- The root of the tree of height `h`: its node at level `h` and index 0. -/
def root (leaves : Nat → m α) (h : Nat) : m α :=
  node hash leaves ⟨h, 0⟩

/-! ## Built trees -/

/-- A tree that holds the value of every node: a leaf, or a node above its two subtrees. -/
inductive Built (β : Type) where
  /-- A leaf, with its value. -/
  | leaf (value : β)
  /-- A node above the leaves, with its value, its left subtree and its right subtree. -/
  | node (value : β) (left right : Built β)

/-- The value of the top node of a built tree. -/
def Built.value : Built α → α
  | .leaf value => value
  | .node value _ _ => value

/-- Every node under a position, each computed once.

It computes the node at the position with the same hash calls, in the same order.

Each node also keeps its two subtrees. -/
def build (leaves : Nat → m α) (p : Position) : m (Built α) :=
  node
    (fun q left right => do
      let value ← hash q left.value right.value
      return .node value left right)
    (fun j => do
      let value ← leaves j
      return .leaf value)
    p

/-- The path of leaf `j`, read from a tree built `n` levels above it, from the leaf up.

At height `k + 1`, bit `k` of `j` says which child holds the leaf, and the other child is a sibling.

A build never holds a leaf above level 0; reading one there repeats its value. -/
def Built.path : Built α → (n j : Nat) → Vector α n
  | _, 0, _ => #v[]
  | .node _ left right, n + 1, j =>
    if j / 2 ^ n % 2 = 0 then (left.path n j).push right.value
    else (right.path n j).push left.value
  | .leaf value, n + 1, _ => Vector.replicate (n + 1) value

/-! ## Paths -/

/-- The siblings of a node and of its next ancestors, `n` nodes from the bottom. -/
def siblings (leaves : Nat → m α) : (p : Position) → (n : Nat) → m (Vector α n)
  | _, 0 => pure #v[]
  | p, n + 1 => do
    let sibling ← node hash leaves p.sibling
    let rest ← siblings leaves p.parent n
    return (#v[sibling] ++ rest).cast (Nat.add_comm 1 n)

/-- The path of leaf `j` in the tree of height `h`, from the leaf up. -/
def path (leaves : Nat → m α) (h j : Nat) : m (Vector α h) :=
  siblings hash leaves ⟨0, j⟩ h

/-! ## Climbing -/

/-- The two children of a climb step, the left one first.

The node held at a position is the left child when its index is even. -/
def ordered (p : Position) (current sibling : α) : α × α :=
  if p.isLeft then (current, sibling) else (sibling, current)

/-- The node reached by climbing from the node `current` at a position, one sibling per level. -/
def climb : (p : Position) → (current : α) → (siblings : List α) → m α
  | _, current, [] => pure current
  | p, current, sibling :: rest => do
    let children := ordered p current sibling
    let parent ← hash p.parent children.1 children.2
    climb p.parent parent rest

end EthLib.Cryptography.Merkle
