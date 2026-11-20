module

public import EthLib.Serialization.Ssz.Codec.Layout

/-!
The Merkle root of a value, taken from the tree its layout describes.

The hash may answer in a monad, and the specification is SHA-256 in the identity monad.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

section

variable {m : Type → Type} [Monad m] (hasher : Hasher m)

/-- Mix a layout's word into the root of its contents, where it has one. -/
@[inline] def hashLayoutFromM (mixin : Option Bytes) (contents : ExceptT Err m Bytes) :
    ExceptT Err m Bytes := do
  let root ← contents
  -- A shape mixing a word in puts its contents on the left and the word on the right.
  match mixin with
  | none => return root
  | some word => ExceptT.lift (mixInM hasher root word)

/-- Hash the leaves of a layout and mix in its word, where it has one. -/
@[inline] def hashLayoutChunksM (layout : MerkleLayout) (chunks : Array Bytes) :
    ExceptT Err m Bytes :=
  hashLayoutFromM hasher layout.mixin (match layout.limit with
    | none => ExceptT.lift (merkleizeProgressiveUncheckedM hasher chunks.toList)
    | some capacity => merkleizeBoundedUncheckedM hasher chunks (some capacity))

mutual

/--
The SSZ Merkle root of a value, read against the type it is meant to fit.

The layout supplies the leaves, the capacity, and the word to mix in.

Rooting evaluates that layout without restating any type-specific tree rule.

The budget bounds how far the rooting may descend into nested values.
-/
def hashTreeRootAtM : Nat → Desc → Value → ExceptT Err m Bytes
  -- A budget of the type's nesting never runs out, so this answers only a budget set too low.
  | 0, _, _ => throw .proofIncomplete
  | budget + 1, shape, value => do
    let layout ← merkleLayout shape value
    hashLayoutChunksM hasher layout (← layoutChunksAtM budget layout)

/--
The leaves in a half-open range, as nodes, each nested value rooted here.

A range is asked for where a proof walks into one part of a tree.

Building that proof then does not hash the whole value.
-/
def layoutChunksAtM (budget : Nat) (layout : MerkleLayout)
    (start : Nat := 0) (stop : Option Nat := none) : ExceptT Err m (Array Bytes) := do
  match layout.leaves with
  | .packed chunks =>
    if start == 0 && stop.isNone then return chunks
    return chunks.extract start (stop.getD chunks.size)
  | .nested values =>
    let slots := match start, stop with
      | 0, none => values
      | _, none => values.drop start
      | _, some last => (values.drop start).take (last - start)
    let chunks ← slots.mapM fun slot =>
      match slot with
      -- A position carrying no value merkleizes as a zero leaf.
      | none => pure zeroChunk
      | some (shape, value) => hashTreeRootAtM budget shape value
    return chunks.toArray

end

/--
The SSZ Merkle root of a value, read against the type it is meant to fit.

The budget is the type's own nesting, which is more than the rooting can spend.
-/
def hashTreeRootM (shape : Desc) (value : Value) : ExceptT Err m Bytes :=
  hashTreeRootAtM hasher shape.nesting shape value

end

/-- The SSZ Merkle root of a value, under a budget, with SHA-256. -/
def hashTreeRootAt (budget : Nat) (shape : Desc) (value : Value) : Except Err Bytes :=
  (hashTreeRootAtM sha256Hasher budget shape value).run

/-- The leaves in a half-open range, as nodes, with SHA-256. -/
def layoutChunksAt (budget : Nat) (layout : MerkleLayout)
    (start : Nat := 0) (stop : Option Nat := none) : Except Err (Array Bytes) :=
  (layoutChunksAtM sha256Hasher budget layout start stop).run

/-- The SSZ Merkle root of a value, with SHA-256. -/
def hashTreeRoot (shape : Desc) (value : Value) : Except Err Bytes :=
  (hashTreeRootM sha256Hasher shape value).run

end EthLib.Serialization.Ssz
