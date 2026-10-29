import EthLib.Serialization.Ssz.Codec.Root
import EthLib.Serialization.Ssz.Merkle.Verify

/-! Reading an index against a value's data, and building the proofs that carry it. -/

namespace EthLib.Serialization.Ssz

/--
Where a walk down the spine of a progressive shape stopped.

    root
     +-- level 1, holding leaf 0
     `-- the rest of the spine
          +-- level 2, holding leaves 1 to 4
          `-- the rest of the spine
               +-- level 3, holding leaves 5 to 20
               `-- the zero node that closes it
-/
structure SpineStop where
  /-- Turns of the index still to take, once the spine has been left or exhausted. -/
  depth : Nat
  /-- First leaf of the level reached. -/
  leavesFrom : Nat
  /-- Leaves that level holds. -/
  capacity : Nat
  /-- Whether the walk turned off the spine, rather than running out of turns on it. -/
  turnedLeft : Bool

/--
Walk the spine of a progressive shape, one turn per level.

A clear bit turns left, into the level's own subtree.

A set bit turns right, onto the next level, which holds four times as many leaves.
-/
def spineWalk (leafCount index : Nat) :
    (depth : Nat) → (leavesFrom : Nat) → (capacity : Nat) → Except Err SpineStop
  | 0, leavesFrom, capacity => .ok ⟨0, leavesFrom, capacity, false⟩
  | depth + 1, leavesFrom, capacity => do
    -- A level whose first leaf is past the data is a level the spine never opened.
    if leavesFrom ≥ leafCount then throw .pathPastSpine
    if !gindexBit index depth then return ⟨depth, leavesFrom, capacity, true⟩
    spineWalk leafCount index depth (leavesFrom + capacity) (capacity * 4)

mutual

/--
Root of the subtree at one generalized index of a value's own Merkle tree.

The index is read from the top down, one bit per level.

The budget covers the declared type depth, which suffices for every addressable nested value.
-/
def nodeRootAt : Nat → Desc → Value → Nat → Except Err Bytes
  -- A budget of the type's nesting never runs out, so this answers only a budget set too low.
  | 0, _, _, _ => .error .proofIncomplete
  | budget + 1, shape, value, index => do
    if index < 1 then throw (.notAGindex index)
    -- The root sits on no branch, but it is still a node, so this walk answers for it.
    if index == 1 then return (← hashTreeRoot shape value)
    let layout ← merkleLayout shape value
    -- Every bit below the leading one is a turn, so the bit width is the depth to walk.
    let full ← gindexLength index
    -- A mixed-in word is the right child, which puts the contents one level down on the left.
    let depth := if layout.mixin.isSome then full - 1 else full
    match layout.mixin with
    | some word =>
      if gindexBit index depth then
        -- A word is one leaf, so a turn below it descends into something with no parts.
        if depth != 0 then throw .pathIntoMixin
        return word
    | none => pure ()
    match layout.limit with
    | some capacity => boundedNode budget layout index depth 0 capacity
    -- A progressive shape spreads its leaves down a spine of widening subtrees.
    | none => progressiveNode budget layout index depth 0 1
termination_by budget => (budget, 0)

/--
Root of a node of the subtree a walk ended in, or of something inside one leaf.

    turns left <= height   the index stops inside this subtree
    turns left >  height   the index passes into one leaf's own tree
-/
def boundedNode (budget : Nat) (layout : MerkleLayout)
    (index depth leavesFrom capacity : Nat) : Except Err Bytes := do
  -- A bounded tree is padded out to a power of two, which fixes its height.
  let width := nextPow2 capacity
  let treeDepth := Nat.log2 width
  if depth ≤ treeDepth then
    -- Each turn halves the run of leaves a node spans, so the turns left give its width.
    let span := width >>> depth
    let start := leavesFrom + gindexBelow index depth * span
    let chunks ← layoutChunksAt budget layout start (some (start + span))
    merkleizeBoundedUnchecked chunks (some span)
  else
    -- Past the bottom of this subtree, the remaining turns are read inside one leaf.
    let below := depth - treeDepth
    let leaf := leavesFrom + gindexBelow (index >>> below) treeDepth
    match layout.leaves with
    -- Packed data has no tree below a leaf, its elements sharing one node.
    | .packed _ => throw .pathIntoPacked
    | .nested values =>
      match values[leaf]? with
      | some (some (nestedShape, nestedValue)) =>
        nodeRootAt budget nestedShape nestedValue (gindexRebase index below)
      -- A position past the leaves, or one holding no value, has no tree to descend into.
      | _ => throw .pathIntoGap
termination_by (budget, 1)

/-- A progressive walk reads either a bounded level or the remaining spine. -/
def progressiveNode (budget : Nat) (layout : MerkleLayout)
    (index depth start capacity : Nat) : Except Err Bytes := do
  let stop ← spineWalk layout.leaves.count index depth start capacity
  if stop.turnedLeft then
    boundedNode budget layout index stop.depth stop.leavesFrom stop.capacity
  else
    -- Stopping on the spine covers the whole remaining suffix, zero terminator included.
    let rest ← layoutChunksAt budget layout stop.leavesFrom
    return merkleizeProgressiveFrom rest stop.capacity
termination_by (budget, 2)

end

/--
Root of the subtree at one generalized index of a value's own Merkle tree.

The budget is the type's nesting plus the index, which is more than the walk can spend:
each level enters one nested type or consumes one turn of the index.
-/
def nodeRoot (shape : Desc) (value : Value) (index : Nat) : Except Err Bytes :=
  nodeRootAt (shape.nesting + index) shape value index

/--
Branch that authenticates one generalized index of a value against its root.

Every node on the path contributes its sibling, bottom-up, as a verifier reads it.
-/
def buildProof (shape : Desc) (value : Value) (index : Nat) : Except Err (List Bytes) := do
  (← getBranchIndices index).mapM (nodeRoot shape value)

/--
Nodes that authenticate several generalized indices of a value at once.

Only what a verifier cannot rebuild is carried.

Branches that meet share every node above the meeting point, and those are dropped.
-/
def buildMultiproof (shape : Desc) (value : Value) (indices : List Nat) :
    Except Err (List Bytes) := do
  (← getHelperIndices indices).mapM (nodeRoot shape value)

end EthLib.Serialization.Ssz
