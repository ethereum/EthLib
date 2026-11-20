module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Serialization.Ssz.Packing
public import EthLib.Serialization.Ssz.Merkle.Merkleize

/-!
The two tree shapes SSZ merkleizes into, and the words a shape hashes itself against.

The hash is an argument, and it may answer inside a monad.

The specification is the identity monad with SHA-256.

So a random-oracle model can run this merkleization with a hash that queries an oracle.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The all-zero node. -/
def zeroChunk : Bytes :=
  Array.replicate bytesPerChunk 0

/-- Folding two nodes into their parent, with a hash that may answer in a monad. -/
def combineM {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) (left right : Bytes) :
    m Bytes := do
  -- Packed buffers can be joined with a byte copy.
  return (← hash (ByteArray.mk left ++ ByteArray.mk right)).data

/-- Folding two nodes into their parent, with SHA-256. -/
def combine (left right : Bytes) : Bytes :=
  (combineM (m := Id) Cryptography.Hash.Sha256.hash left right).run

/-- Cache depth for common capacities, with larger trees computed on demand. -/
abbrev maxZeroDepth : Nat :=
  -- The cache is a shortcut, not a bound: a deeper tree is folded instead of looked up.
  64

/--
Roots of the all-zero perfect trees, indexed by depth up to the cache depth.

It records the hashes of one computation of the deepest root, so entry `d` is the root of depth `d`.
-/
def zeroRoots : Array Bytes :=
  let record (left right : Bytes) : StateM (Array Bytes) Bytes :=
    modifyGet fun table => let parent := combine left right; (parent, table.push parent)
  ((zeroRootM record zeroChunk maxZeroDepth).run #[zeroChunk]).2

/-- Root of an all-zero subtree at any depth, using cached roots where available. -/
def zeroSubtree (depth : Nat) : Bytes :=
  match zeroRoots[depth]? with
  | some root => root
  | none => zeroRoot combine zeroChunk depth

/--
The hash that merkleization calls, and the roots of the all-zero subtrees that it reads.

Both answer in a monad.

The root of an all-zero subtree is itself a hash of zero nodes, so a model of the hash computes it.

The specification reads these roots from a table instead.

Nothing here ties the zero roots to the hash: a hasher built from its hash alone computes them.
-/
structure Hasher (m : Type → Type) where
  /-- The hash of the bytes of two nodes. -/
  hash : ByteArray → m ByteArray
  /-- The root of the all-zero perfect tree of a depth. -/
  zeroSubtree : Nat → m Bytes

/-- SHA-256, with the roots of the all-zero subtrees read from the table. -/
def sha256Hasher : Hasher Id :=
  ⟨Cryptography.Hash.Sha256.hash, zeroSubtree⟩

/-- A hasher that computes the roots of the all-zero subtrees with its own hash, one per level. -/
def Hasher.ofHash {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) : Hasher m :=
  ⟨hash, zeroRootM (combineM hash) zeroChunk⟩

/-- Number of nodes needed to hold a given number of bytes. -/
def chunksForBytes (byteCount : Nat) : Nat :=
  (byteCount + bytesPerChunk - 1) / bytesPerChunk

/-- Read the items in one node and right-pad their bytes to the node width. -/
@[inline] def packChunkWith (itemsPerChunk : Nat) (read : Nat → Nat → Bytes)
  (index : Nat) : Bytes :=
  let start := index * itemsPerChunk
  let piece := read start (start + itemsPerChunk)
  piece ++ Array.replicate (bytesPerChunk - piece.size) 0

/-- Bytes right-padded to a node boundary and split into nodes. -/
def packBytes (data : Bytes) : Array Bytes :=
  -- Reuse the input when it already fills the only node.
  if data.size = bytesPerChunk then #[data]
  else
    Array.ofFn (n := chunksForBytes data.size) fun position =>
      packChunkWith bytesPerChunk (fun start stop => data.extract start stop) position.val

/--
Root of a perfect tree using an action for a leaf and one for a parent of two leaves.

A subtree wholly past the data uses the all-zero root of its depth.
-/
@[specialize] def subtreeFromM {m : Type → Type} [Monad m] (hasher : Hasher m)
    (size : Nat) (leaf parentOfLeaves : (i : Nat) → i < size → m Bytes)
    (depth start : Nat) : m Bytes :=
  if within : start < size then
    match depth with
    | 0 => leaf start within
    | 1 => parentOfLeaves start within
    | d + 2 => do
      let childDepth := d + 1
      let pending :=
        -- Skip a half whose width exceeds the data before computing that width.
        if childDepth < 6 || size.log2 < childDepth then none
        else
          let half := 2 ^ childDepth
          let rightStart := start + half
          -- A fraction of the input limits the number of forks.
          let minimum := max 64 ((size + 7) / 8)
          if minimum ≤ half && rightStart + minimum ≤ size then
            some (Task.spawn fun _ =>
              subtreeFromM hasher size leaf parentOfLeaves childDepth rightStart)
          else none
      -- Bind the left action before the pure right action that the task builds.
      let left ← subtreeFromM hasher size leaf parentOfLeaves childDepth start
      let right ← match pending with
        | some task => task.get
        | none => subtreeFromM hasher size leaf parentOfLeaves childDepth (start + 2 ^ childDepth)
      combineM hasher.hash left right
  else hasher.zeroSubtree depth

/--
Root a perfect tree over an array of nodes.

Every node is trusted to be 32 bytes wide.
-/
def subtreeAtM {m : Type → Type} [Monad m] (hasher : Hasher m) (chunks : @& Array Bytes)
    (depth start : Nat) : m Bytes :=
  subtreeFromM hasher chunks.size (fun i h => pure (chunks[i]))
    (fun i h => do
      let left ← pure (chunks[i])
      let right ← (if next : i + 1 < chunks.size then pure (chunks[i + 1])
        else hasher.zeroSubtree 0)
      combineM hasher.hash left right)
    depth start

/-- Root of the perfect tree over nodes from a position, with SHA-256 and the zero table. -/
def subtreeAt (chunks : Array Bytes) (depth start : Nat) : Bytes :=
  (subtreeAtM sha256Hasher chunks depth start).run

/-- A node as a 32-byte vector, refused if it has another width. -/
def toChunk (node : Bytes) : Except Err (Vector UInt8 bytesPerChunk) :=
  Base.exactArray bytesPerChunk node (.count bytesPerChunk)

/-- Refuse a hash operand that is not one complete 32-byte SSZ node. -/
def checkChunk (node : Bytes) : Except Err Unit :=
  -- Fixed-width children make the boundary between the two hash operands unambiguous.
  (toChunk node).map fun _ => ()

/-- Refuse a node sequence containing a node of the wrong width. -/
def checkChunks : List Bytes → Except Err Unit
  | [] => .ok ()
  | node :: rest => do
    checkChunk node
    checkChunks rest

/-- Check the leaf count before choosing the depth of the bounded tree. -/
@[inline] def merkleizeBoundedFromM {m : Type → Type} [Monad m] (size : Nat)
    (root : Nat → m Bytes) (limit : Option Nat) : ExceptT Err m Bytes := do
  match limit with
  | some capacity =>
    -- A capacity under the data would silently drop nodes.
    if capacity < size then throw (.merkleizeLimit size capacity)
    ExceptT.lift (root (depthFor capacity))
  | none => ExceptT.lift (root (depthFor size))

/--
Root of the bounded tree over a node sequence, trusting every node to be 32 bytes wide.

The capacity is a count of nodes, which the type fixes from its declared length or limit.

With no capacity given, the tree is just wide enough for the nodes it holds.

A node of another width is hashed or returned as it is, so the caller checks widths first.
-/
def merkleizeBoundedUncheckedM {m : Type → Type} [Monad m] (hasher : Hasher m)
    (chunks : Array Bytes) (limit : Option Nat) : ExceptT Err m Bytes :=
  merkleizeBoundedFromM chunks.size (fun depth => subtreeAtM hasher chunks depth 0) limit

/-- Root of the bounded tree over a node sequence, with SHA-256 and the zero table. -/
def merkleizeBoundedUnchecked (chunks : Array Bytes) (limit : Option Nat) : Except Err Bytes :=
  (merkleizeBoundedUncheckedM sha256Hasher chunks limit).run

private def packedLeaf (data : @& ByteArray) (index : Nat) : Bytes :=
  packChunkWith bytesPerChunk (fun start stop => (data.extract start stop).data) index

private def packedParent (data : @& ByteArray) (size index : Nat) : Bytes :=
  let start := index * bytesPerChunk
  let stop := start + 2 * bytesPerChunk
  -- Two complete nodes can enter the hash from one byte slice.
  if stop ≤ data.size then (sha256Hasher.hash (data.extract start stop)).data
  else combine (packedLeaf data index)
    (if index + 1 < size then packedLeaf data (index + 1) else zeroChunk)

private def packedSubtree (data : @& ByteArray) (size depth : Nat) : Bytes :=
  subtreeFromM sha256Hasher size (fun i _ => packedLeaf data i)
    (fun i _ => packedParent data size i) depth 0

/-- Root a bounded tree from bytes, padding its final partial node. -/
@[inline, no_expose] def merkleizePackedBoundedUnchecked (data : ByteArray) (limit : Option Nat) :
    ExceptT Err Id Bytes :=
  let size := chunksForBytes data.size
  merkleizeBoundedFromM size (packedSubtree data size) limit

/--
Root of the progressive tree over a node sequence, per EIP-7916.

A right-leaning spine of binary subtrees, closed by a zero node.

Successive levels hold 1, 4, 16, then 64 nodes, so the capacity grows with the data.

The root holds chunk 0 in a subtree of width 1 on its left, and everything past it on its right.

That right child holds chunks 1 to 4 in a subtree of width 4, and so on.

A zero node closes the spine.

A node keeps its index as later ones are appended.

Its branch still has to be rebuilt to authenticate the new root.

Every node is trusted to be 32 bytes wide.
-/
def merkleizeProgressiveUncheckedM {m : Type → Type} [Monad m] (hasher : Hasher m)
    (chunks : List Bytes) (level : Nat := 0) : m Bytes := do
  let tops ← (progressiveWindows chunks level).mapM fun (window, windowLevel) =>
    subtreeAtM hasher window.toArray (depthFor (4 ^ windowLevel)) 0
  -- An exhausted input closes the spine with a plain zero node, not a zero subtree.
  spineM (combineM hasher.hash) zeroChunk tops

/-- Root of the progressive tree over a node sequence, with SHA-256 and the zero table. -/
def merkleizeProgressiveUnchecked (chunks : List Bytes) (level : Nat := 0) : Bytes :=
  (merkleizeProgressiveUncheckedM sha256Hasher chunks level).run

/--
Root of the progressive tree, starting from a level of a given width.

The width is a power of four: the capacity of whichever level the caller reached.

Every node is trusted to be 32 bytes wide.
-/
def merkleizeProgressiveFrom (chunks : Array Bytes) (width : Nat) : Bytes :=
  -- A power-of-four width has twice its progressive level as its binary logarithm.
  merkleizeProgressiveUnchecked chunks.toList (Nat.log2 width / 2)

/-- Hashing a subtree root against the word its shape mixes in, as the right child. -/
def mixInM {m : Type → Type} [Monad m] (hasher : Hasher m) (root word : Bytes) : m Bytes :=
  combineM hasher.hash root word

/-- Hashing a subtree root against the word its shape mixes in, with SHA-256. -/
def mixIn (root word : Bytes) : Bytes :=
  (mixInM sha256Hasher root word).run

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

end EthLib.Serialization.Ssz
