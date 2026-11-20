module

public import EthLib.Cryptography.Merkle.Tree

/-!
# Merkle multiproofs

A multiproof opens several nodes of one tree, on any levels, with helper nodes.

The helpers are the siblings of their paths that no path holds, so shared nodes are sent once.

A verifier rebuilds the root from both, hashing in the order of the tree.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

namespace Position

/-- Whether the node `a` is the node `p` or one of its ancestors. -/
def covers (a p : Position) : Bool :=
  -- `a` is on the level of `p` or above it.
  p.level ≤ a.level &&
  -- Each right shift by one bit climbs one level, so the ancestor of `p` on the level of `a` is `a`.
  p.index >>> (a.level - p.level) == a.index

/-- Whether the helper node `a` comes no later than the helper node `b`.

Helpers go from the leaves up, and from right to left within a level. -/
def helperBefore (a b : Position) : Bool :=
  -- `a` is on a lower level than `b`.
  a.level < b.level ||
  -- `a` is on the level of `b`, at the same index or to its right.
  (a.level == b.level && b.index ≤ a.index)

end Position

/-- The positions from the node `p` up to the root of the tree of height `h`, the root left out. -/
def pathTo (h : Nat) (p : Position) : List Position :=
  (List.range (h - p.level)).map p.ancestor

/-- The helpers below the node at level `level` and index `j`, from the opened nodes `opened`.

A child with no opened node below it is a helper when its sibling has one. -/
def helpers.go (opened : List Position) : (level j : Nat) → List Position
  -- A leaf has no children, so no helpers below it.
  | 0, _ => []
  | level + 1, j =>
    -- The opened nodes under the left child, at index `2 * j` one level down.
    let left := opened.filter fun q => (⟨level, 2 * j⟩ : Position).covers q
    -- The opened nodes under the right child, at index `2 * j + 1` one level down.
    let right := opened.filter fun q => (⟨level, 2 * j + 1⟩ : Position).covers q
    match left.isEmpty, right.isEmpty with
    -- No opened node under either child: no helper is needed below this node.
    | true, true => []
    -- Only the right child has opened nodes: the left child is a helper.
    | true, false => ⟨level, 2 * j⟩ :: helpers.go right level (2 * j + 1)
    -- Only the left child has opened nodes: the right child is a helper.
    | false, true => ⟨level, 2 * j + 1⟩ :: helpers.go left level (2 * j)
    -- Both children have opened nodes: each one is rebuilt, so neither is a helper.
    | false, false => helpers.go left level (2 * j) ++ helpers.go right level (2 * j + 1)

/-- The helper positions of the opened positions in the tree of height `h`.

They are the siblings of the path nodes that are not path nodes themselves.

They come from the leaves up, and from right to left within a level. -/
def helpers (h : Nat) (opened : List Position) : List Position :=
  (helpers.go opened h 0).mergeSort Position.helperBefore

variable {m : Type → Type} [Monad m] {α : Type} (hash : Position → α → α → m α)

/-- The node at level `level` and index `j`, rebuilt from the nodes in `nodes`.

Each entry of `nodes` pairs a position with the value of the node there.

A node in `nodes` is taken as it is.
Otherwise the node is the hash of its two children, keyed by its position.

The result is missing when `nodes` does not determine the node. -/
def rebuild.go (nodes : List (Position × α)) : (level j : Nat) → m (Option α)
  -- A leaf has no children, so it is known only when `nodes` holds it.
  | 0, j => pure (nodes.lookup ⟨0, j⟩)
  | level + 1, j =>
    -- A node held in `nodes` is taken as it is, without looking below it.
    match nodes.lookup ⟨level + 1, j⟩ with
    | some node => pure (some node)
    | none =>
      -- With no nodes left, neither child can be rebuilt, so the walk stops early.
      if nodes.isEmpty then pure none else do
        -- The nodes under the left child, at index `2 * j` one level down, go left.
        -- All the other nodes go right.
        let (left, right) := nodes.partition fun e => (⟨level, 2 * j⟩ : Position).covers e.1
        -- The left child is rebuilt before the right one, in the order of the tree.
        match ← rebuild.go left level (2 * j) with
        -- A missing left child leaves the node undetermined.
        | none => pure none
        | some leftNode =>
          -- The right child sits at index `2 * j + 1` one level down.
          match ← rebuild.go right level (2 * j + 1) with
          -- A missing right child leaves the node undetermined.
          | none => pure none
          -- Both children are known, so the node is their hash, keyed by its position.
          | some rightNode => some <$> hash ⟨level + 1, j⟩ leftNode rightNode

/-- The root of the tree of height `h` rebuilt from the nodes given, if they determine it. -/
def rebuild (nodes : List (Position × α)) (h : Nat) : m (Option α) :=
  rebuild.go hash nodes h 0

/-- The root rebuilt from the opened nodes and the helper nodes, in the order of the helpers.

The result is missing when the nodes given do not determine the root. -/
def verify (h : Nat) (opened : List Position) (values helperValues : List α) : m (Option α) :=
  rebuild hash (opened.zip values ++ (helpers h opened).zip helperValues) h

end EthLib.Cryptography.Merkle
