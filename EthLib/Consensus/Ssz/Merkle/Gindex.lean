import EthLib.Consensus.Ssz.Codec.Error

/-! Generalized indices: naming one node of a tree, and the nodes a proof of it needs. -/

namespace EthLib.Consensus.Ssz

/--
Levels an index sits below the root, which is none at all for the root itself.

The leading bit of an index carries its depth, so the depth is the bit width less one.
-/
def gindexDepth (index : Nat) : Except Err Nat :=
  if index < 1 then .error (.notAGindex index) else .ok (Nat.log2 index)

/-- Depth of an index, which is also the number of nodes on its proof branch. -/
def gindexLength (index : Nat) : Except Err Nat := do
  let depth ← gindexDepth index
  -- The root sits on no branch, so it has no length to report.
  if depth == 0 then .error .rootHasNoBranch else .ok depth

/-- Whether the branch turns right at the given depth, counted from the leaf. -/
def gindexBit (index position : Nat) : Bool :=
  index.testBit position

/-- The bottom turns of an index, as many as the depth, with everything above dropped. -/
def gindexBelow (index depth : Nat) : Nat :=
  index % 2 ^ depth

/-- The node sharing a parent with this one. -/
def gindexSibling (index : Nat) : Nat :=
  index ^^^ 1

/-- One of the two nodes this one is the parent of. -/
def gindexChild (index : Nat) (rightSide : Bool) : Nat :=
  index * 2 + (if rightSide then 1 else 0)

/-- The node this one is a child of. -/
def gindexParent (index : Nat) : Nat :=
  index / 2

/--
An index measured from one root, rebased onto a position in a larger tree.

An index carries its depth in its leading bit, so this splices rather than multiplies.

    outer 2, inner 24  ->  40, not 48
-/
def gindexConcat (outer inner : Nat) : Except Err Nat := do
  let _ ← gindexDepth outer
  let depth ← gindexDepth inner
  -- Dropping the inner leading bit is what makes this a splice and not a multiplication.
  return outer * 2 ^ depth + (inner - 2 ^ depth)

/--
The bottom turns of an index, read as an index of a tree of their own.

Undoes a splice, handing the rest of an index to the subtree it lands in.

    splice 2 and 24  ->  40
    read 40 back at the depth of 24  ->  24
-/
def gindexRebase (index depth : Nat) : Nat :=
  2 ^ depth + gindexBelow index depth

/--
Position of one chunk on a progressive spine.

    level 1  holds chunk 0
    level 2  holds chunks 1 to 4
    level 3  holds chunks 5 to 20

A chunk keeps its place as the collection grows, so a proof of it outlives an append.

The index counts one level below the spine, since the shape mixes a word into its root.
-/
def progressiveChunkGindex (chunk : Nat) (depth : Nat := 0) (spine : Nat := 2) : Nat :=
  let width := 2 ^ depth
  -- The subtree root is the spine node's left child, and the chunk sits below it.
  if chunk < width then spine * 2 * width + chunk
  else progressiveChunkGindex (chunk - width) (depth + 2) (spine * 2 + 1)
termination_by chunk
decreasing_by
  have : 0 < 2 ^ depth := Nat.pos_of_neZero (2 ^ depth)
  omega

/-- Nodes from the given one up to the root, excluding the root. -/
def getPathIndices (index : Nat) : Except Err (List Nat) := do
  let length ← gindexLength index
  return (List.range length).map fun level => index >>> level

/-- Siblings along the path from the given node to the root, which is its proof branch. -/
def getBranchIndices (index : Nat) : Except Err (List Nat) := do
  return (← getPathIndices index).map gindexSibling

/-- Refuse any claimed node that is a strict ancestor of the current claim. -/
def rejectAncestors (indices : List Nat) (claim : Nat) : List Nat → Except Err Unit
  | [] => .ok ()
  | ancestor :: rest => do
    -- An ancestor would replace a root already rebuilt from its descendants.
    if indices.contains ancestor then throw (.nestedIndex claim)
    rejectAncestors indices claim rest

/-- Validate every claim's strict ancestors in the original request order. -/
def rejectClaimPaths (indices : List Nat) : List Nat → Except Err Unit
  | [] => .ok ()
  | claim :: rest => do
    let path ← getPathIndices claim
    -- The first path node is the claim itself, not one of its strict ancestors.
    rejectAncestors indices claim (path.drop 1)
    rejectClaimPaths indices rest

/--
Refuse an index set that cannot be verified soundly.

An empty request claims nothing, so nothing about the root would be checked.

A repeated index would keep one value and drop the other silently.

An ancestor claim can be overwritten when its descendants are folded upward.
-/
def rejectRelated (indices : List Nat) : Except Err Unit := do
  if indices.isEmpty then throw .emptyRequest
  if indices.eraseDups.length != indices.length then throw .repeatedIndex
  rejectClaimPaths indices indices

/-- The paths of several claims, flattened in the order the claims were supplied. -/
def collectPathIndices : List Nat → Except Err (List Nat)
  | [] => .ok []
  | index :: rest => do
    let path ← getPathIndices index
    let paths ← collectPathIndices rest
    return path ++ paths

/--
Nodes a proof must carry to authenticate all the given ones at once.

Every sibling on every branch, less the paths the verifier can rebuild.

Descending order fixes which proof value belongs to each helper index.
-/
def getHelperIndices (indices : List Nat) : Except Err (List Nat) := do
  rejectRelated indices
  -- Flattening the paths together is what makes a shared branch appear only once.
  let paths ← collectPathIndices indices
  let helpers := (paths.map gindexSibling).eraseDups.filter fun node => !paths.contains node
  return helpers.mergeSort fun a b => b ≤ a

end EthLib.Consensus.Ssz
