module

public import EthLib.Serialization.Ssz.Error
public import EthLib.Cryptography.Merkle.Multiproof

/-!
Generalized indices: naming one node of a tree, and the nodes a proof of it needs.

The rules are stated in EthLib's own terms, one step per comment.

The root is node 1, and node `k` has the children `2k` and `2k + 1`.

So node `k` sits `floor(log2 k)` levels below the root.

Its bits below the leading one are its turns, 1 for right, from the top down.

[EIP-7916][eip7916] places the chunks of a progressive shape on a spine.

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#progressive-merkle-tree
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
Levels an index sits below the root, which is none at all for the root itself.

The leading bit of an index carries its depth, so the depth is the bit width less one.
-/
def gindexDepth (index : Nat) : Except Err Nat :=
  -- `depth(k) = floor(log2 k)` for `k >= 1`; no node has the index 0.
  if index < 1 then .error (.notAGindex index) else .ok (Nat.log2 index)

/-- Depth of an index, which is also the number of nodes on its proof branch. -/
def gindexLength (index : Nat) : Except Err Nat := do
  let depth ← gindexDepth index
  -- EthLib's choice: the root sits on no branch, so it has no length to report.
  if depth == 0 then .error .rootHasNoBranch else .ok depth

/-- Whether the branch turns right at the given depth, counted from the leaf. -/
def gindexBit (index position : Nat) : Bool :=
  -- Bit `i` of `k` is 1 when the node `i` levels above `k` is a right child, `2j + 1`.
  index.testBit position

/-- The bottom turns of an index, as many as the depth, with everything above dropped. -/
def gindexBelow (index depth : Nat) : Nat :=
  -- `k mod 2^d`: the last `d` turns.
  index % 2 ^ depth

/-- The node sharing a parent with this one. -/
def gindexSibling (index : Nat) : Nat :=
  -- `k xor 1`: `2j` and `2j + 1` share the parent `j`.
  index ^^^ 1

/-- One of the two nodes this one is the parent of. -/
def gindexChild (index : Nat) (rightSide : Bool) : Nat :=
  -- `2k` on the left, `2k + 1` on the right.
  index * 2 + (if rightSide then 1 else 0)

/-- The node this one is a child of. -/
def gindexParent (index : Nat) : Nat :=
  -- `floor(k / 2)`.
  index / 2

/--
An index measured from one root, rebased onto a position in a larger tree.

An index carries its depth in its leading bit, so this splices rather than multiplies.

For example, the outer index 2 and the inner index 24 give 40, not 48.
-/
def gindexConcat (outer inner : Nat) : Except Err Nat := do
  let _ ← gindexDepth outer
  let depth ← gindexDepth inner
  -- `concat(o, i) = o * 2^d + (i - 2^d)`, with `d = depth(i)`.
  --
  -- Dropping the inner leading bit is what makes this a splice and not a multiplication.
  return outer * 2 ^ depth + (inner - 2 ^ depth)

/--
The bottom turns of an index, read as an index of a tree of their own.

Undoes a splice, handing the rest of an index to the subtree it lands in.

For example, the splice of 2 and 24 is 40, and 40 read back at the depth of 24 is 24.
-/
def gindexRebase (index depth : Nat) : Nat :=
  -- `2^d + (k mod 2^d)`: the last `d` turns under a fresh leading bit.
  2 ^ depth + gindexBelow index depth

/--
Position of one chunk on a progressive spine.

Level 1 holds chunk 0, level 2 holds chunks 1 to 4, and level 3 holds chunks 5 to 20.

A chunk keeps its place as the collection grows, so a proof of it outlives an append.

The index counts one level below the spine, since the shape mixes a word into its root.
-/
def progressiveChunkGindex (chunk : Nat) (depth : Nat := 0) (spine : Nat := 2) : Nat :=
  let width := 2 ^ depth
  -- EIP-7916: the subtree of a spine node `s` is its left child `2s`, with `2^d` leaves.
  --
  -- Its leaf `c` is node `2s * 2^d + c`.
  if chunk < width then spine * 2 * width + chunk
  -- A chunk past this level goes on down the spine, to `2s + 1`, four times as wide.
  else progressiveChunkGindex (chunk - width) (depth + 2) (spine * 2 + 1)
termination_by chunk
decreasing_by
  have : 0 < 2 ^ depth := Nat.pos_of_neZero (2 ^ depth)
  omega

/-- Nodes from the given one up to the root, excluding the root. -/
def getPathIndices (index : Nat) : Except Err (List Nat) := do
  let length ← gindexLength index
  -- The nodes `floor(k / 2^j)` for `0 <= j < depth(k)`.
  --
  -- EthLib refuses `k = 1`, whose path holds no node, rather than answer an empty path.
  return (List.range length).map fun level => index >>> level

/-- Siblings along the path from the given node to the root, which is its proof branch. -/
def getBranchIndices (index : Nat) : Except Err (List Nat) := do
  -- The sibling of each node of the path, from the bottom up.
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
  -- These three refusals are EthLib's, so that a multiproof checks every index it claims.
  if indices.isEmpty then throw .emptyRequest
  if indices.eraseDups.length != indices.length then throw .repeatedIndex
  rejectClaimPaths indices indices

/-- Levels a node sits below the root, which its index carries in its leading bit. -/
def levelOf (index : Nat) : Nat :=
  -- `floor(log2 k)`.
  Nat.log2 index

/-- Levels the deepest of several indices sits below the root: the height of their tree. -/
def gindexHeight (indices : List Nat) : Nat :=
  (indices.map levelOf).foldl max 0

/-- The position of the node at an index, in a tree of the given height. -/
def gindexPosition (height index : Nat) : Cryptography.Merkle.Position :=
  -- In a tree of height `h`, node `k` is at level `h - depth(k)` from the bottom.
  --
  -- It is node `k - 2^depth(k)` of that level, counted from the left.
  ⟨height - Nat.log2 index, index - 2 ^ Nat.log2 index⟩

/-- The index of the node at a position, in a tree of the given height. -/
def positionGindex (height : Nat) (p : Cryptography.Merkle.Position) : Nat :=
  -- Node `j` of level `l` from the bottom is `2^(h - l) + j`.
  2 ^ (height - p.level) + p.index

/-- The height of the tree of a request that passes the checks, and the positions of its claims. -/
def claimPositions (indices : List Nat) :
    Except Err (Nat × List Cryptography.Merkle.Position) := do
  rejectRelated indices
  let height := gindexHeight indices
  return (height, indices.map (gindexPosition height))

/--
Nodes a proof must carry to authenticate all the given ones at once.

They are the helper nodes of the Merkle multiproof, in decreasing order of their indices.
-/
def getHelperIndices (indices : List Nat) : Except Err (List Nat) := do
  let (height, opened) ← claimPositions indices
  -- The helpers are the siblings of every path node, less the path nodes themselves.
  --
  -- EthLib takes them from the generic multiproof, in the tree as deep as the deepest index.
  return (Cryptography.Merkle.helpers height opened).map (positionGindex height)

end EthLib.Serialization.Ssz
