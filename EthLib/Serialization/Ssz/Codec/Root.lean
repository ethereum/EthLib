import EthLib.Serialization.Ssz.Codec.Layout

/-! The Merkle root of a value, taken from the tree its layout describes. -/

namespace EthLib.Serialization.Ssz

mutual

/--
The SSZ Merkle root of a value, read against the type it is meant to fit.

The layout supplies the leaves, the capacity, and the word to mix in.

Rooting evaluates that layout without restating any type-specific tree rule.

The budget bounds how far the rooting may descend into nested values.
-/
def hashTreeRootAt : Nat → Desc → Value → Except Err Bytes
  -- A budget of the type's nesting never runs out, so this answers only a budget set too low.
  | 0, _, _ => .error .proofIncomplete
  | budget + 1, shape, value => do
    let layout ← merkleLayout shape value
    let chunks ← layoutChunksAt budget layout
    let root ← match layout.limit with
      | none => .ok (merkleizeProgressiveUnchecked chunks.toList)
      | some capacity => merkleizeBoundedUnchecked chunks (some capacity)
    -- A shape mixing a word in puts its contents on the left and the word on the right.
    return match layout.mixin with
      | none => root
      | some word => mixIn root word

/--
The leaves in a half-open range, as nodes, each nested value rooted here.

A range is asked for where a proof walks into one part of a tree.

Building that proof then does not hash the whole value.
-/
def layoutChunksAt (budget : Nat) (layout : MerkleLayout)
    (start : Nat := 0) (stop : Option Nat := none) : Except Err (Array Bytes) := do
  -- An absent end means every leaf the shape produced.
  let last := stop.getD layout.leaves.count
  match layout.leaves with
  | .packed chunks => return chunks.extract start last
  | .nested values =>
    let slots := (values.drop start).take (last - start)
    let chunks ← slots.mapM fun slot =>
      match slot with
      -- A position carrying no value merkleizes as a zero leaf.
      | none => pure zeroChunk
      | some (shape, value) => hashTreeRootAt budget shape value
    return chunks.toArray

end

/--
The SSZ Merkle root of a value, read against the type it is meant to fit.

The budget is the type's own nesting, which is more than the rooting can spend.
-/
def hashTreeRoot (shape : Desc) (value : Value) : Except Err Bytes :=
  hashTreeRootAt shape.nesting shape value

end EthLib.Serialization.Ssz
