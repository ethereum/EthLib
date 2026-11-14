module

public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Serialization.Ssz.Codec.Serialize
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
  return (← hash (ByteArray.mk (left ++ right))).data

/-- Folding two nodes into their parent, with SHA-256. -/
def combine (left right : Bytes) : Bytes :=
  (combineM (m := Id) Cryptography.Hash.Sha256.hash left right).run

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

/-- The root of the all-zero perfect tree of a depth, hashed from the root one level below. -/
def zeroSubtreeM {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) : Nat → m Bytes
  | 0 => pure zeroChunk
  | depth + 1 => do
    let below ← zeroSubtreeM hash depth
    combineM hash below below

/-- A hasher that computes the roots of the all-zero subtrees with its own hash, one per level. -/
def Hasher.ofHash {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) : Hasher m :=
  ⟨hash, zeroSubtreeM hash⟩

/-- Bytes right-padded to a node boundary and split into nodes. -/
def packBytes (data : Bytes) : Array Bytes :=
  Array.ofFn (n := (data.size + bytesPerChunk - 1) / bytesPerChunk) fun position =>
    let start := position.val * bytesPerChunk
    let piece := data.extract start (start + bytesPerChunk)
    piece ++ Array.replicate (bytesPerChunk - piece.size) 0

/--
Root of the perfect tree of a given depth, over nodes starting at a position.

Positions past the data are zero, and a subtree wholly past it is an all-zero subtree.

Every node is trusted to be 32 bytes wide.
-/
def subtreeAtM {m : Type → Type} [Monad m] (hasher : Hasher m) (chunks : Array Bytes)
    (depth start : Nat) : m Bytes :=
  if start ≥ chunks.size then hasher.zeroSubtree depth
  else
    match depth with
    | 0 => pure (padded zeroChunk chunks start)
    | d + 1 => do
      let left ← subtreeAtM hasher chunks d start
      let right ← subtreeAtM hasher chunks d (start + 2 ^ d)
      combineM hasher.hash left right

/-- Root of the perfect tree over nodes from a position, with SHA-256 and the zero table. -/
def subtreeAt (chunks : Array Bytes) (depth start : Nat) : Bytes :=
  (subtreeAtM sha256Hasher chunks depth start).run

/-- Refuse a hash operand that is not one complete 32-byte SSZ node. -/
def checkChunk (node : Bytes) : Except Err Unit :=
  -- Fixed-width children make the boundary between the two hash operands unambiguous.
  if node.size = bytesPerChunk then .ok () else .error (.count bytesPerChunk node.size)

/-- A node as a 32-byte vector, refused if it has another width. -/
def toChunk (node : Bytes) : Except Err (Vector UInt8 bytesPerChunk) :=
  if width : node.size = bytesPerChunk then .ok ⟨node, width⟩
  else .error (.count bytesPerChunk node.size)

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
def merkleizeBoundedUncheckedM {m : Type → Type} [Monad m] (hasher : Hasher m)
    (chunks : Array Bytes) (limit : Option Nat) : ExceptT Err m Bytes := do
  match limit with
  | some capacity =>
    -- A capacity under the data would silently drop nodes.
    if capacity < chunks.size then throw (.merkleizeLimit chunks.size capacity)
    ExceptT.lift (subtreeAtM hasher chunks (depthFor capacity) 0)
  | none => ExceptT.lift (subtreeAtM hasher chunks (depthFor chunks.size) 0)

/-- Root of the bounded tree over a node sequence, with SHA-256 and the zero table. -/
def merkleizeBoundedUnchecked (chunks : Array Bytes) (limit : Option Nat) : Except Err Bytes :=
  (merkleizeBoundedUncheckedM sha256Hasher chunks limit).run

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
    (chunks : List Bytes) (level : Nat := 0) : m Bytes :=
  -- An exhausted input closes the spine with a plain zero node, not a zero subtree.
  if chunks.isEmpty then pure zeroChunk
  else do
    let width := 4 ^ level
    let here ← subtreeAtM hasher (chunks.take width).toArray (depthFor width) 0
    let rest ← merkleizeProgressiveUncheckedM hasher (chunks.drop width) (level + 1)
    combineM hasher.hash here rest
termination_by chunks.length
decreasing_by
  have : 0 < 4 ^ level := Nat.pos_of_neZero (4 ^ level)
  simp only [List.length_drop]
  have : 0 < chunks.length := by
    cases chunks with
    | nil => simp_all
    | cons _ _ => simp
  omega

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
