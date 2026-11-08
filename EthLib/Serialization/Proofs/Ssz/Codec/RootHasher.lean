module

public import EthLib.Serialization.Proofs.Ssz.Merkle.Hasher
public import EthLib.Serialization.Ssz.Codec.Root

/-!
# Proofs: the SHA-256 instance of the root of a value

The root of a value takes a hash that may answer in a monad.

With SHA-256 it runs in the identity monad, and each step reads as a plain computation.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open EthLib.Base

/-- A spent budget gives no root. -/
theorem hashTreeRootAt_zero (shape : Desc) (value : Value) :
    hashTreeRootAt 0 shape value = .error .proofIncomplete := by
  simp only [hashTreeRootAt, hashTreeRootAtM]
  rfl

/-- One more unit of budget roots the layout of the value, then mixes in its word. -/
theorem hashTreeRootAt_succ (budget : Nat) (shape : Desc) (value : Value) :
    hashTreeRootAt (budget + 1) shape value = (do
      let layout ← merkleLayout shape value
      let chunks ← layoutChunksAt budget layout
      let root ← match layout.limit with
        | none => .ok (merkleizeProgressiveUnchecked chunks.toList)
        | some capacity => merkleizeBoundedUnchecked chunks (some capacity)
      return match layout.mixin with
        | none => root
        | some word => mixIn root word : Except Err Bytes) := by
  simp only [hashTreeRootAt, hashTreeRootAtM, ExceptT.run, exceptT_id_bind, exceptT_id_monadLift,
    exceptT_id_lift, exceptT_id_pure, except_bind_eq]
  cases merkleLayout shape value with
  | error => rfl
  | ok layout =>
    simp only [Except.bind]
    cases layout.limit <;> cases layout.mixin <;> rfl

/-- The leaves in a range, each nested value rooted with SHA-256. -/
theorem layoutChunksAt_eq (budget : Nat) (layout : MerkleLayout) (start : Nat)
    (stop : Option Nat) :
    layoutChunksAt budget layout start stop = (do
      let last := stop.getD layout.leaves.count
      match layout.leaves with
      | .packed chunks => return chunks.extract start last
      | .nested values =>
        let slots := (values.drop start).take (last - start)
        let chunks ← slots.mapM fun slot =>
          match slot with
          | none => pure zeroChunk
          | some (shape, value) => hashTreeRootAt budget shape value
        return chunks.toArray : Except Err (Array Bytes)) := by
  simp only [layoutChunksAt, layoutChunksAtM, ExceptT.run]
  cases layout.leaves with
  | packed chunks => rfl
  | nested values =>
    simp only [exceptT_id_bind, except_bind_eq]
    rw [exceptT_id_mapM]
    rfl

/-- The root of a value spends the nesting of its type as its budget. -/
theorem hashTreeRoot_eq_nesting (shape : Desc) (value : Value) :
    hashTreeRoot shape value = hashTreeRootAt shape.nesting shape value :=
  rfl

end EthLib.Serialization.Ssz
