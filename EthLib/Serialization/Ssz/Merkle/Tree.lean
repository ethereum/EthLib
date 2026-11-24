module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Serialization.Ssz.Packing
public import EthLib.Serialization.Ssz.Merkle.Merkleize

/-!
The two tree shapes SSZ merkleizes into, and the words a shape hashes itself against.

The hash is an argument, and it may answer inside a monad.

The specification is the identity monad with SHA-256, written `H` in the comments.

So a random-oracle model can run this merkleization with a hash that queries an oracle.

The core rules of packing, bounded trees and mixing in are stated in EthLib's own terms.

[EIP-7916][eip7916] defines the progressive tree, and [EIP-7495][eip7495] the layout word.

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#progressive-merkle-tree
[eip7495]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#merkleization
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The all-zero node. -/
def zeroChunk : Bytes :=
  -- 32 zero bytes, the leaf that pads every tree.
  Array.replicate bytesPerChunk 0

/-- Folding two nodes into their parent, with a hash that may answer in a monad. -/
def combineM {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray) (left right : Bytes) :
    m Bytes := do
  -- A parent is `H(left || right)`, the hash of the 64 bytes of its two children.
  return (← hash (ByteArray.mk (left ++ right))).data

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
  -- Entry `d` is `Z_d`: `Z_0` the zero chunk, and `Z_{d+1} = H(Z_d || Z_d)`.
  ((zeroRootM record zeroChunk maxZeroDepth).run #[zeroChunk]).2

/-- Root of an all-zero subtree at any depth, using cached roots where available. -/
def zeroSubtree (depth : Nat) : Bytes :=
  -- `Z_d`, read from the table up to depth 64, and folded level by level past it.
  match zeroRoots[depth]? with
  | some root => root
  | none => zeroRoot combine zeroChunk depth

/--
The hash that merkleization calls, and the roots of the all-zero subtrees that it reads.

Both answer in a monad.

The specification reads the zero roots from a table.

A hasher built from its hash alone computes them.

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
  -- The root of an all-zero subtree is itself a hash of zero nodes.
  ⟨hash, zeroRootM (combineM hash) zeroChunk⟩

/-- Bytes right-padded to a node boundary and split into nodes. -/
def packBytes (data : Bytes) : Array Bytes :=
  -- Packing: `n` bytes take `ceil(n / 32)` chunks, chunk `i` starting at byte `32i`.
  --
  -- No bytes give no chunk, so the tree over them holds only zero leaves.
  Array.ofFn (n := (data.size + bytesPerChunk - 1) / bytesPerChunk) fun position =>
    let start := position.val * bytesPerChunk
    let piece := data.extract start (start + bytesPerChunk)
    -- The last chunk is right-padded with zero bytes to 32.
    piece ++ Array.replicate (bytesPerChunk - piece.size) 0

/--
Root of the perfect tree of a given depth, over nodes starting at a position.

Positions past the data are zero, and a subtree wholly past it is an all-zero subtree.

Every node is trusted to be 32 bytes wide.
-/
def subtreeAtM {m : Type → Type} [Monad m] (hasher : Hasher m) (chunks : Array Bytes)
    (depth start : Nat) : m Bytes :=
  -- A subtree whose leaves are all padding is `Z_d`, so the padding is never built.
  if start ≥ chunks.size then hasher.zeroSubtree depth
  else
    match depth with
    -- A tree of one leaf: the root is the chunk itself.
    | 0 => pure (padded zeroChunk chunks start)
    -- Depth `d + 1`: `H(left || right)`, the right subtree from leaf `start + 2^d`.
    | d + 1 => do
      let left ← subtreeAtM hasher chunks d start
      let right ← subtreeAtM hasher chunks d (start + 2 ^ d)
      combineM hasher.hash left right

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
    -- More chunks than the limit: not merkleized, an error.
    --
    -- A capacity under the data would silently drop nodes.
    if capacity < chunks.size then throw (.merkleizeLimit chunks.size capacity)
    -- Otherwise the chunks are zero-padded to the next power of two of the limit.
    ExceptT.lift (subtreeAtM hasher chunks (depthFor capacity) 0)
  -- No limit: the chunks, zero-padded to the next power of two of their count, 0 giving 1.
  | none => ExceptT.lift (subtreeAtM hasher chunks (depthFor chunks.size) 0)

/-- Root of the bounded tree over a node sequence, with SHA-256 and the zero table. -/
def merkleizeBoundedUnchecked (chunks : Array Bytes) (limit : Option Nat) : Except Err Bytes :=
  (merkleizeBoundedUncheckedM sha256Hasher chunks limit).run

/--
Root of the progressive tree over a node sequence, per EIP-7916.

A node keeps its index as later ones are appended.

Its branch still has to be rebuilt to authenticate the new root.

Every node is trusted to be 32 bytes wide.
-/
def merkleizeProgressiveUncheckedM {m : Type → Type} [Monad m] (hasher : Hasher m)
    (chunks : List Bytes) (level : Nat := 0) : m Bytes := do
  -- EIP-7916: a right-leaning spine of binary subtrees.
  --
  -- Successive levels hold 1, 4, 16, then 64 nodes, so the capacity grows with the data.
  --
  -- The root holds chunk 0 in a subtree of width 1 on its left.
  --
  -- Everything past chunk 0 is on its right.
  --
  -- That right child holds chunks 1 to 4 in a subtree of width 4, and so on.
  --
  -- EIP-7916: level `k` merkleizes its up to `4^k` chunks as a tree of `4^k` leaves.
  let tops ← (progressiveWindows chunks level).mapM fun (window, windowLevel) =>
    subtreeAtM hasher window.toArray (depthFor (4 ^ windowLevel)) 0
  -- EIP-7916: each level is hashed as `H(a || b)` against the levels after it, on its right.
  --
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
  -- EIP-7916: the recursion carries the width `4^k` of its current level, 1 at the top.
  --
  -- A power-of-four width has twice its progressive level as its binary logarithm.
  merkleizeProgressiveUnchecked chunks.toList (Nat.log2 width / 2)

/-- Hashing a subtree root against the word its shape mixes in, as the right child. -/
def mixInM {m : Type → Type} [Monad m] (hasher : Hasher m) (root word : Bytes) : m Bytes :=
  -- `H(root || word)`, the contents on the left and the 32-byte word on the right.
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
  -- A length is mixed in as a uint256: 32 bytes, little-endian.
  uintBytes bytesPerChunk count

/-- The layout a progressive container mixes in, one bit per position, lowest first. -/
def activeFieldsWord (active : List Bool) : Bytes :=
  -- EIP-7495: the layout packed as bits, bit `i` in bit `i mod 8` of byte `floor(i / 8)`.
  --
  -- EIP-7495 allows at most 256 entries, so the layout fits one chunk, zero-padded.
  packBits active.toArray bytesPerChunk

end EthLib.Serialization.Ssz
