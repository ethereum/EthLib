import EthLib.Cryptography.Hash.Sha256
import EthLib.Consensus.Ssz.Codec.Serialize
import EthLib.Consensus.Ssz.Merkle.Merkleize

/-! The two tree shapes SSZ merkleizes into, and the words a shape hashes itself against. -/

namespace EthLib.Consensus.Ssz

/-- The all-zero node. -/
def zeroChunk : Bytes :=
  Array.replicate bytesPerChunk 0

/-- Folding two nodes into their parent. -/
def combine (left right : Bytes) : Bytes :=
  (Cryptography.Hash.Sha256.hash (ByteArray.mk (left ++ right))).data

/-- Cache depth for common capacities, with larger trees computed on demand. -/
abbrev maxZeroDepth : Nat :=
  -- The cache is a shortcut, not a bound: a deeper tree is folded instead of looked up.
  64

/--
Roots of the all-zero perfect trees up to a depth, each built from the one below.

Building each entry from the one below keeps the table linear in the depth.

Building each from scratch would make it exponential.
-/
def zeroRootsUpTo : Nat → Array Bytes
  | 0 => #[zeroChunk]
  | depth + 1 =>
    let below := zeroRootsUpTo depth
    let deepest := below[depth]?.getD zeroChunk
    below.push (combine deepest deepest)

/--
Roots of the all-zero perfect trees, indexed by depth.

Index zero is the zero node, and each following entry doubles the leaves covered.
-/
def zeroRoots : Array Bytes :=
  zeroRootsUpTo maxZeroDepth

/-- Root of an all-zero subtree at any depth, using cached roots where available. -/
def zeroSubtree (depth : Nat) : Bytes :=
  match zeroRoots[depth]? with
  | some root => root
  | none => zeroRoot combine zeroChunk depth

/-- Bytes right-padded to a node boundary and split into nodes. -/
def packBytes (data : Bytes) : Array Bytes :=
  Array.ofFn (n := (data.size + bytesPerChunk - 1) / bytesPerChunk) fun position =>
    let start := position.val * bytesPerChunk
    let piece := data.extract start (start + bytesPerChunk)
    piece ++ Array.replicate (bytesPerChunk - piece.size) 0

/--
Root of the perfect tree of a given depth, over nodes starting at a position.

Positions past the data are zero, and a subtree wholly past it is read from the table.

Every node is trusted to be 32 bytes wide.
-/
def subtreeAt (chunks : Array Bytes) (depth start : Nat) : Bytes :=
  if start ≥ chunks.size then zeroSubtree depth
  else
    match depth with
    | 0 => padded zeroChunk chunks start
    | d + 1 => combine (subtreeAt chunks d start) (subtreeAt chunks d (start + 2 ^ d))

/-- Refuse a hash operand that is not one complete 32-byte SSZ node. -/
def checkChunk (node : Bytes) : Except Err Unit :=
  -- Fixed-width children make the boundary between the two hash operands unambiguous.
  if node.size = bytesPerChunk then .ok () else .error (.count bytesPerChunk node.size)

/-- Refuse a node sequence containing a node of the wrong width. -/
def checkChunks : List Bytes → Except Err Unit
  | [] => .ok ()
  | node :: rest => do
    checkChunk node
    checkChunks rest

/--
Root of the bounded tree over a node sequence, trusting every node to be 32 bytes wide.

The capacity is a count of nodes, which the type fixes from its declared length or limit.

With no capacity given, the tree is just wide enough for the nodes it holds.

A node of another width is hashed or returned as it is, so the caller checks widths first.
-/
def merkleizeBoundedUnchecked (chunks : Array Bytes) (limit : Option Nat) : Except Err Bytes := do
  match limit with
  | some capacity =>
    -- A capacity under the data would silently drop nodes.
    if capacity < chunks.size then throw (.merkleizeLimit chunks.size capacity)
    return subtreeAt chunks (depthFor capacity) 0
  | none => return subtreeAt chunks (depthFor chunks.size) 0

/--
Root of the bounded tree over a node sequence.

Every node is checked to be 32 bytes wide, before the capacity is.
-/
def merkleizeBounded (chunks : Array Bytes) (limit : Option Nat) : Except Err Bytes := do
  -- A lone short leaf would pass as a root, and a 31-byte node beside a 33-byte one as a pair.
  checkChunks chunks.toList
  merkleizeBoundedUnchecked chunks limit

/--
Root of the progressive tree over a node sequence, per EIP-7916.

A right-leaning spine of binary subtrees, closed by a zero node.

Successive levels hold 1, 4, 16, then 64 nodes, so the capacity grows with the data.

    root
     +-- chunks 0 ..< 1, as a binary subtree of width 1
     `-- everything past them
          +-- chunks 1 ..< 5, as a binary subtree of width 4
          `-- everything past them
               +-- chunks 5 ..< 21, as a binary subtree of width 16
               `-- the zero node that closes the spine

A node keeps its index as later ones are appended.

Its branch still has to be rebuilt to authenticate the new root.

Every node is trusted to be 32 bytes wide.
-/
def merkleizeProgressiveUnchecked (chunks : List Bytes) (level : Nat := 0) : Bytes :=
  -- An exhausted input closes the spine with a plain zero node, not a zero subtree.
  if chunks.isEmpty then zeroChunk
  else
    let width := 4 ^ level
    let here := subtreeAt (chunks.take width).toArray (depthFor width) 0
    combine here (merkleizeProgressiveUnchecked (chunks.drop width) (level + 1))
termination_by chunks.length
decreasing_by
  have : 0 < 4 ^ level := Nat.pos_of_neZero (4 ^ level)
  simp only [List.length_drop]
  have : 0 < chunks.length := by
    cases chunks with
    | nil => simp_all
    | cons _ _ => simp
  omega

/--
Root of the progressive tree over a node sequence, per EIP-7916.

Every node is checked to be 32 bytes wide first.
-/
def merkleizeProgressive (chunks : List Bytes) (level : Nat := 0) : Except Err Bytes := do
  -- A node of another width would move the boundary between two hashed operands.
  checkChunks chunks
  return merkleizeProgressiveUnchecked chunks level

/--
Root of the progressive tree, starting from a level of a given width.

The width is a power of four: the capacity of whichever level the caller reached.

Every node is trusted to be 32 bytes wide.
-/
def merkleizeProgressiveFrom (chunks : Array Bytes) (width : Nat) : Bytes :=
  -- A power-of-four width has twice its progressive level as its binary logarithm.
  merkleizeProgressiveUnchecked chunks.toList (Nat.log2 width / 2)

/-- Hashing a subtree root against the word its shape mixes in, as the right child. -/
def mixIn (root word : Bytes) : Bytes :=
  combine root word

/--
The low 256 bits of a count, written as one little-endian node.

A count below 2^256 is exact, and a larger one is truncated.

A truncated count falls outside the domain of the length-binding theorem.
-/
def lengthWord (count : Nat) : Bytes :=
  uintBytes bytesPerChunk count

/-- The layout a progressive container mixes in, one bit per position, lowest first. -/
def activeFieldsWord (active : List Bool) : Bytes :=
  packBits active.toArray bytesPerChunk

end EthLib.Consensus.Ssz
