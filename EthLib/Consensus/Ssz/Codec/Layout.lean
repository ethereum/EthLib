import EthLib.Consensus.Ssz.Codec.Deserialize
import EthLib.Consensus.Ssz.Type.Paths
import EthLib.Consensus.Ssz.Merkle.Tree

/-! What a value merkleizes into, stated before any of it is hashed. -/

namespace EthLib.Consensus.Ssz

/-- Whether a type packs its elements into shared nodes rather than giving each a root. -/
def Desc.isBasic : Desc → Bool
  | .bool => true
  | .uint _ => true
  | _ => false

/-- Number of nodes needed to hold a given number of bytes. -/
def chunksForBytes (byteCount : Nat) : Nat :=
  (byteCount + bytesPerChunk - 1) / bytesPerChunk

/-- Number of nodes needed to hold a given number of bits. -/
def chunksForBits (bitCount : Nat) : Nat :=
  (bitCount + 8 * bytesPerChunk - 1) / (8 * bytesPerChunk)

/-- Nodes over a sequence of basic elements, packed back to back before being split. -/
def packElements (parts : List Bytes) : Array Bytes :=
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

    shape                 leaves               tree                        mixed in
    container             fields               bounded by the field count  -
    list                  elements or packing  bounded by the limit        count
    progressiveList       elements or packing  progressive spine           count
    progressiveContainer  layout positions     progressive spine           layout
    compatibleUnion       the option it holds  bounded by one              selector

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
  -- EIP-8016 writes one byte, and a hash operand is one node, so it is zero-extended.
  checkSelector selector
  return lengthWord selector

/-- Place consecutive field values at active positions, leaving zero leaves in gaps. -/
def placeSlots : List Bool → List (Desc × Value) → Except Err (List (Option (Desc × Value)))
  | [], [] => .ok []
  | false :: active, fields => do
    return none :: (← placeSlots active fields)
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
  packBytes (packBits data ((data.size + 7) / 8))

/--
A leaf of fixed width, which fills its own nodes exactly and mixes nothing in.

The encoding is the whole content, so the nodes it packs into are the whole capacity.
-/
def fixedLeaf (shape : Desc) (value : Value) : Except Err MerkleLayout := do
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
  if element.isBasic then
    -- Packed elements are counted in nodes, so a declared capacity is measured in bytes.
    let capacity := positions.map fun count => chunksForBytes (count * element.itemLength)
    return .packing (packElements (← serializeEach element elements)) capacity mixin
  return .nesting (elements.map fun value => some (element, value)) positions mixin

/-- How one value merkleizes: its leaves, their tree shape, and the word mixed in. -/
def merkleLayout (shape : Desc) (value : Value) : Except Err MerkleLayout :=
  match shape, value with
  | .bool, _ | .uint _, _ => fixedLeaf shape value
  -- The bytes pack as they are, since a root does not depend on what an offset can name.
  | .byteVector length, .bytes data => do
    if data.size != length then throw (.scope length data.size)
    return .packing (packBytes data) (some (packBytes data).size)
  | .byteList limit, .bytes data => do
    if data.size > limit then throw (.overLimit limit data.size)
    -- The count mixed in is the byte count, which is also the element count here.
    return .packing (packBytes data) (some (chunksForBytes limit)) (lengthWord data.size)
  -- A fixed bit count is recovered from the type, so nothing is mixed in.
  | .bitVector length, .bits data => do
    if data.size != length then throw (.scope length data.size)
    return .packing (packedBits data) (some (chunksForBits length))
  | .bitList limit, .bits data => do
    if data.size > limit then throw (.overLimit limit data.size)
    return .packing (packedBits data) (some (chunksForBits limit)) (lengthWord data.size)
  -- No capacity bounds a progressive shape, so its nodes go on a spine instead.
  | .progressiveBitList limit, .bits data => do
    -- A declared limit bounds the value as it bounds the encoding, though it shapes no tree.
    boundCheck limit data.size
    -- The count mixed in is the bit count, not the number of packed nodes.
    return .packing (packedBits data) none (lengthWord data.size)
  | .vector element length, .seq elements => do
    if elements.length != length then throw (.scope length elements.length)
    -- A fixed element count is recovered from the type, so nothing is mixed in.
    sequenceLayout element elements (some length)
  | .list element limit, .seq elements => do
    if elements.length > limit then throw (.overLimit limit elements.length)
    sequenceLayout element elements (some limit) (lengthWord elements.length)
  | .progressiveList element limit, .seq elements => do
    boundCheck limit elements.length
    -- The count mixed in is the element count, never the number of nodes they packed into.
    sequenceLayout element elements none (lengthWord elements.length)
  | .container _ fields, .seq values => do
    if fields.length != values.length then throw .typeMismatch
    return .nesting ((fields.zip values).map some) (some fields.length)
  | .progressiveContainer active _ fields, .seq values => do
    -- One leaf per layout position, not per field.
    return .nesting (← layoutSlots active fields values) none (activeFieldsWord active)
  | .compatibleUnion selectors options, .union selector data => do
    -- The union adds no leaf of its own, so one leaf of capacity is a tree of no depth.
    let chosen ← lookupOption selectors options selector
    return .nesting [some (chosen, data)] (some 1) (← selectorWord selector)
  | _, _ => .error .typeMismatch

end EthLib.Consensus.Ssz
