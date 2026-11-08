module

public import EthLib.Base.Proofs.ExceptT
public import EthLib.Serialization.Ssz.Merkle.Tree

/-!
# Proofs: the SHA-256 instances of the merkleization

The merkleization takes a hash that may answer in a monad.

With SHA-256 it runs in the identity monad, and each step reads as a plain computation.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open EthLib.Base

/-- Folding two nodes hashes their concatenation with SHA-256. -/
theorem combine_eq (left right : Bytes) :
    combine left right = (Cryptography.Hash.Sha256.hash (ByteArray.mk (left ++ right))).data :=
  rfl

/-- A subtree past the data is the zero subtree, a leaf is padded, and a parent folds two halves. -/
theorem subtreeAt_eq (chunks : Array Bytes) (depth start : Nat) :
    subtreeAt chunks depth start =
      if start ≥ chunks.size then zeroSubtree depth
      else
        match depth with
        | 0 => padded zeroChunk chunks start
        | d + 1 => combine (subtreeAt chunks d start) (subtreeAt chunks d (start + 2 ^ d)) := by
  unfold subtreeAt
  rw [subtreeAtM.eq_def]
  split
  · rfl
  · cases depth <;> rfl

/-- The bounded root checks the capacity, then roots the perfect tree of its depth. -/
theorem merkleizeBoundedUnchecked_eq (chunks : Array Bytes) (limit : Option Nat) :
    merkleizeBoundedUnchecked chunks limit = (do
      match limit with
      | some capacity =>
        if capacity < chunks.size then throw (.merkleizeLimit chunks.size capacity)
        return subtreeAt chunks (depthFor capacity) 0
      | none => return subtreeAt chunks (depthFor chunks.size) 0 : Except Err Bytes) := by
  unfold merkleizeBoundedUnchecked merkleizeBoundedUncheckedM
  cases limit with
  | none => rfl
  | some capacity =>
    by_cases over : capacity < chunks.size
    · simp only [over, ↓reduceIte]
      rfl
    · simp only [over, ↓reduceIte]
      rfl

/-- The progressive root closes an empty suffix with a zero node.

Otherwise it hashes the root of one level against the root of the rest. -/
theorem merkleizeProgressiveUnchecked_unfold (chunks : List Bytes) (level : Nat) :
    merkleizeProgressiveUnchecked chunks level =
      if chunks.isEmpty then zeroChunk
      else
        combine (subtreeAt (chunks.take (4 ^ level)).toArray (depthFor (4 ^ level)) 0)
          (merkleizeProgressiveUnchecked (chunks.drop (4 ^ level)) (level + 1)) := by
  unfold merkleizeProgressiveUnchecked
  rw [merkleizeProgressiveUncheckedM.eq_def]
  split <;> rfl

/-- Mixing a word in folds it in as the right child, with SHA-256. -/
theorem mixIn_eq (root word : Bytes) : mixIn root word = combine root word :=
  rfl

end EthLib.Serialization.Ssz
