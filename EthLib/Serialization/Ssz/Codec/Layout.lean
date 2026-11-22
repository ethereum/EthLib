module

public import EthLib.Serialization.Ssz.Codec.Deserialize
public import EthLib.Serialization.Ssz.Type.Paths
public import EthLib.Serialization.Ssz.Merkle.Tree

/-!
What a value merkleizes into, stated before any of it is hashed.

The core rules of the root of each type are stated in EthLib's own terms, one per comment.

A root mixing in a word `w` is `H(r || w)`, with `r` the root of the contents and `H` SHA-256.

[EIP-7916][eip7916], [EIP-7495][eip7495] and [EIP-8016][eip8016] root the newer types.

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#merkleization
[eip7495]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#merkleization
[eip8016]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-8016.md#merkleization
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- Whether a type packs its elements into shared nodes rather than giving each a root. -/
def Desc.isBasic : Desc → Bool
  -- The basic types are boolean and uintN; every other type is composite.
  | .bool => true
  | .uint _ => true
  | _ => false

/-- Number of nodes needed to hold a given number of bytes. -/
def chunksForBytes (byteCount : Nat) : Nat :=
  -- `ceil(n / 32)`.
  (byteCount + bytesPerChunk - 1) / bytesPerChunk

/-- Number of nodes needed to hold a given number of bits. -/
def chunksForBits (bitCount : Nat) : Nat :=
  -- `ceil(n / 256)`, 256 bits to a chunk.
  (bitCount + 8 * bytesPerChunk - 1) / (8 * bytesPerChunk)

/-- Nodes over a sequence of basic elements, packed back to back before being split. -/
def packElements (parts : List Bytes) : Array Bytes :=
  -- The serialized elements, concatenated in order, then packed into chunks.
  packBytes (parts.foldl (fun total part => total ++ part) #[])

/-- What a shape puts under its tree. -/
inductive Leaves where
  /-- Data sharing nodes, where nothing below a node can be addressed. -/
  | packed (chunks : Array Bytes)
  /-- Values with roots of their own, a position holding none merkleizing as zero. -/
  | nested (values : List (Option (Desc × Value)))
  deriving Inhabited

/-- Leaves held, one entry per leaf, whether or not it carries a value. -/
def Leaves.count : Leaves → Nat
  | .packed chunks => chunks.size
  -- Nested values count positions, gaps included, since a gap is a leaf too.
  | .nested values => values.length

/--
The subtree one value merkleizes into, before any of it is hashed.

- A container: its fields, in a tree bounded by the field count.
- A list: its elements or their packing, bounded by the limit, with the count mixed in.
- A progressive list: its elements or their packing on a progressive spine, with the count.
- A progressive container: its layout positions on a progressive spine, with the layout.
- A compatible union: the option it holds, in a tree bounded by one, with the selector.

Stating the tree rather than building it lets a root and a proof share one rule.
-/
structure MerkleLayout where
  /-- What the shape put under the tree, and which of the two ways it did it. -/
  leaves : Leaves
  /-- Node capacity of the bounded tree, or none for a progressive spine. -/
  limit : Option Nat
  /-- Word the subtree root is hashed against, or none where the shape mixes nothing in. -/
  mixin : Option Bytes
  deriving Inhabited

/-- A layout whose leaves are packed data. -/
def MerkleLayout.packing (chunks : Array Bytes) (limit : Option Nat)
    (mixin : Option Bytes := none) : MerkleLayout :=
  ⟨.packed chunks, limit, mixin⟩

/-- A layout whose leaves are the roots of nested values. -/
def MerkleLayout.nesting (values : List (Option (Desc × Value))) (limit : Option Nat)
    (mixin : Option Bytes := none) : MerkleLayout :=
  ⟨.nested values, limit, mixin⟩

/-- The option selector a compatible union mixes in, as one little-endian node. -/
def selectorWord (selector : Nat) : Except Err Bytes := do
  -- EIP-8016 mixes in the selector `s` in its uint8 serialization: the root is `H(r || s)`.
  --
  -- EIP-8016 writes one byte, and a hash operand is one node, so it is zero-extended.
  checkSelector selector
  return lengthWord selector

/-- Place consecutive field values at active positions, leaving zero leaves in gaps. -/
def placeSlots : List Bool → List (Desc × Value) → Except Err (List (Option (Desc × Value)))
  | [], [] => .ok []
  -- EIP-7495: an inactive position takes the zero chunk.
  | false :: active, fields => do
    return none :: (← placeSlots active fields)
  -- EIP-7495: an active position takes the root of the next field.
  | true :: active, field :: fields => do
    return some field :: (← placeSlots active fields)
  | _, _ => .error .badDeclaration

/-- Positions of a progressive container, each naming the field that sits there. -/
def layoutSlots (active : List Bool) (fields : List Desc) (values : List Value) :
    Except Err (List (Option (Desc × Value))) := do
  if fields.length != values.length then throw .typeMismatch
  -- EIP-7495 assigns one field to each set bit, including positions after gaps.
  let count := active.countP id
  if count != fields.length then throw (.layoutFieldCount count fields.length)
  placeSlots active (fields.zip values)

/-- Bits packed into whole nodes, which is how all three bitfields lay their leaves down. -/
def packedBits (data : Array Bool) : Array Bytes :=
  -- Bit `i` in bit `i mod 8` of byte `floor(i / 8)`, without the closing bit of a bitlist.
  --
  -- The `ceil(n / 8)` bytes are then packed into chunks.
  packBytes (packBits data ((data.size + 7) / 8))

/--
A leaf of fixed width, which fills its own nodes exactly and mixes nothing in.

The encoding is the whole content, so the nodes it packs into are the whole capacity.
-/
def fixedLeaf (shape : Desc) (value : Value) : Except Err MerkleLayout := do
  -- A basic value: its serialization, packed into one chunk, which is the root.
  let chunks := packBytes (← serialize shape value)
  return .packing chunks (some chunks.size)

/--
The subtree a sequence of elements takes.

Basic elements share nodes, so they pack into one run of bytes.

Anything else brings a root of its own, one leaf apiece.

The positions are the sequence's declared capacity, or none where a spine bounds nothing.
-/
def sequenceLayout (element : Desc) (elements : List Value) (positions : Option Nat)
    (mixin : Option Bytes := none) : Except Err MerkleLayout := do
  -- Basic elements: the chunks of their packed serializations.
  --
  -- A capacity of `N` elements of `L` bytes each is `ceil(N * L / 32)` chunks.
  if element.isBasic then
    -- Packed elements are counted in nodes, so a declared capacity is measured in bytes.
    let capacity := positions.map fun count => chunksForBytes (count * element.itemLength)
    return .packing (packElements (← serializeEach element elements)) capacity mixin
  -- Composite elements: one chunk per element, its root, and `N` chunks if a capacity is set.
  return .nesting (elements.map fun value => some (element, value)) positions mixin

/-- How one value merkleizes: its leaves, their tree shape, and the word mixed in. -/
def merkleLayout (shape : Desc) (value : Value) : Except Err MerkleLayout :=
  match shape, value with
  | .bool, _ | .uint _, _ => fixedLeaf shape value
  -- ByteVector[N], a vector of `N` bytes: the root of its packed bytes, with no mix-in.
  --
  -- The bytes pack as they are, since a root does not depend on what an offset can name.
  | .byteVector length, .bytes data => do
    if data.size != length then throw (.scope length data.size)
    return .packing (packBytes data) (some (packBytes data).size)
  | .byteList limit, .bytes data => do
    if data.size > limit then throw (.overLimit limit data.size)
    -- ByteList[N]: `H(r || len)`, `r` the root of its packed bytes in `ceil(N / 32)` chunks.
    --
    -- The count mixed in is the byte count, which is also the element count here.
    return .packing (packBytes data) (some (chunksForBytes limit)) (lengthWord data.size)
  -- Bitvector[N]: the root of its packed bits in `ceil(N / 256)` chunks.
  --
  -- A fixed bit count is recovered from the type, so nothing is mixed in.
  | .bitVector length, .bits data => do
    if data.size != length then throw (.scope length data.size)
    return .packing (packedBits data) (some (chunksForBits length))
  | .bitList limit, .bits data => do
    if data.size > limit then throw (.overLimit limit data.size)
    -- Bitlist[N]: `H(r || len)`, `r` the root of its packed bits in `ceil(N / 256)` chunks.
    return .packing (packedBits data) (some (chunksForBits limit)) (lengthWord data.size)
  -- EIP-7916, ProgressiveBitlist: `H(r || len)`, `r` the progressive root of its packed bits.
  --
  -- No capacity bounds a progressive shape, so its nodes go on a spine instead.
  | .progressiveBitList limit, .bits data => do
    -- A declared limit bounds the value as it bounds the encoding, though it shapes no tree.
    boundCheck limit data.size
    -- The count mixed in is the bit count, not the number of packed nodes.
    return .packing (packedBits data) none (lengthWord data.size)
  | .vector element length, .seq elements => do
    if elements.length != length then throw (.scope length elements.length)
    -- Vector[type, N]: the root of its elements, with no mix-in.
    --
    -- A fixed element count is recovered from the type, so nothing is mixed in.
    sequenceLayout element elements (some length)
  | .list element limit, .seq elements => do
    if elements.length > limit then throw (.overLimit limit elements.length)
    -- List[type, N]: `H(r || len)`, `r` the root of its elements, for `N` elements.
    sequenceLayout element elements (some limit) (lengthWord elements.length)
  | .progressiveList element limit, .seq elements => do
    -- EIP-7916 sets no limit; a limit EthLib declares bounds the value, though it shapes no tree.
    boundCheck limit elements.length
    -- EIP-7916, ProgressiveList[type]: `H(r || len)`, `r` the progressive root of its elements.
    --
    -- The count mixed in is the element count, never the number of nodes they packed into.
    sequenceLayout element elements none (lengthWord elements.length)
  | .container _ fields, .seq values => do
    if fields.length != values.length then throw .typeMismatch
    -- Container: the root of the roots of its fields, one chunk per field, no mix-in.
    return .nesting ((fields.zip values).map some) (some fields.length)
  | .progressiveContainer active _ fields, .seq values => do
    -- EIP-7495: `H(r || layout)`, `r` the progressive root of one chunk per layout position.
    --
    -- One leaf per layout position, not per field.
    return .nesting (← layoutSlots active fields values) none (activeFieldsWord active)
  | .compatibleUnion selectors options, .union selector data => do
    -- EIP-8016: `H(r || selector)`, `r` the root of the data of the selected option.
    --
    -- The union adds no leaf of its own, so one leaf of capacity is a tree of no depth.
    let chosen ← lookupOption selectors options selector
    return .nesting [some (chosen, data)] (some 1) (← selectorWord selector)
  | _, _ => .error .typeMismatch

end EthLib.Serialization.Ssz
