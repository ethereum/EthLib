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

/-- Whether a node is another node or one of its ancestors. -/
def covers (a p : Position) : Bool :=
  p.level ≤ a.level && p.index >>> (a.level - p.level) == a.index

/-- The order of helper nodes: from the leaves up, and from right to left within a level. -/
def helperBefore (a b : Position) : Bool :=
  a.level < b.level || (a.level == b.level && b.index ≤ a.index)

end Position

/-- The positions from a node up to the root of the tree of height `h`, the root left out. -/
def pathTo (h : Nat) (p : Position) : List Position :=
  (List.range (h - p.level)).map p.ancestor

/-- The helpers below the node at level `level` and index `j`, from the opened nodes below it.

A child with no opened node below it is a helper when its sibling has one. -/
def helpers.go (opened : List Position) : (level j : Nat) → List Position
  | 0, _ => []
  | level + 1, j =>
    let left := opened.filter fun q => (⟨level, 2 * j⟩ : Position).covers q
    let right := opened.filter fun q => (⟨level, 2 * j + 1⟩ : Position).covers q
    match left.isEmpty, right.isEmpty with
    | true, true => []
    | true, false => ⟨level, 2 * j⟩ :: helpers.go right level (2 * j + 1)
    | false, true => ⟨level, 2 * j + 1⟩ :: helpers.go left level (2 * j)
    | false, false => helpers.go left level (2 * j) ++ helpers.go right level (2 * j + 1)

/-- The helper positions of the opened positions in the tree of height `h`.

They are the siblings of the path nodes that are not path nodes themselves.

They come from the leaves up, and from right to left within a level. -/
def helpers (h : Nat) (opened : List Position) : List Position :=
  (helpers.go opened h 0).mergeSort Position.helperBefore

variable {m : Type → Type} [Monad m] {α : Type} (hash : Position → α → α → m α)

/-- The node at level `level` and index `j`, rebuilt from the nodes given, if they determine it.

A node given is taken as it is, and otherwise the node is the hash of its two children. -/
def rebuild.go (nodes : List (Position × α)) : (level j : Nat) → m (Option α)
  | 0, j => pure (nodes.lookup ⟨0, j⟩)
  | level + 1, j =>
    match nodes.lookup ⟨level + 1, j⟩ with
    | some node => pure (some node)
    | none =>
      -- With no node below, the children are missing too.
      if nodes.isEmpty then pure none else do
        -- The nodes below the left child go left, and the others go right.
        let (left, right) := nodes.partition fun e => (⟨level, 2 * j⟩ : Position).covers e.1
        match ← rebuild.go left level (2 * j) with
        | none => pure none
        | some leftNode =>
          match ← rebuild.go right level (2 * j + 1) with
          | none => pure none
          | some rightNode => some <$> hash ⟨level + 1, j⟩ leftNode rightNode

/-- The root of the tree of height `h` rebuilt from the nodes given, if they determine it. -/
def rebuild (nodes : List (Position × α)) (h : Nat) : m (Option α) :=
  rebuild.go hash nodes h 0

/-- The root rebuilt from the opened nodes and the helper nodes, in the order of the helpers.

The result is missing when the nodes given do not determine the root. -/
def verify (h : Nat) (opened : List Position) (values helperValues : List α) : m (Option α) :=
  rebuild hash (opened.zip values ++ (helpers h opened).zip helperValues) h

end EthLib.Cryptography.Merkle
