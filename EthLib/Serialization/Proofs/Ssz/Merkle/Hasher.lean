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

/-- Folding two nodes calls the hash on their concatenation. -/
theorem combineM_eq {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (left right : Bytes) :
    combineM hash left right = (do return (← hash (ByteArray.mk (left ++ right))).data) := by
  unfold combineM
  have appended : ByteArray.mk left ++ ByteArray.mk right = ByteArray.mk (left ++ right) :=
    ByteArray.ext ByteArray.data_append
  rw [appended]

/-- Folding two nodes hashes their concatenation with SHA-256. -/
theorem combine_eq (left right : Bytes) :
    combine left right = (Cryptography.Hash.Sha256.hash (ByteArray.mk (left ++ right))).data := by
  rw [combine, combineM_eq]
  rfl

/-- The shortcuts preserve the hash arguments and the order of the binds. -/
theorem subtreeAtM_unfold {m : Type → Type} [Monad m] (hasher : Hasher m)
    (chunks : Array Bytes) (depth start : Nat) :
    subtreeAtM hasher chunks depth start =
      if start ≥ chunks.size then hasher.zeroSubtree depth
      else
        match depth with
        | 0 => pure (padded zeroChunk chunks start)
        | d + 1 => (do
          let left ← subtreeAtM hasher chunks d start
          let right ← subtreeAtM hasher chunks d (start + 2 ^ d)
          combineM hasher.hash left right) := by
  have leaf (position : Nat) :
      subtreeAtM hasher chunks 0 position =
        if inside : position < chunks.size then pure chunks[position]
        else hasher.zeroSubtree 0 := by
    rw [subtreeAtM, subtreeFromM.eq_def]
  rw [subtreeAtM, subtreeFromM.eq_def]
  by_cases past : chunks.size ≤ start
  · simp only [past, Nat.not_lt.mpr past, ↓reduceDIte, ↓reduceIte]
  · have within := Nat.lt_of_not_ge past
    simp only [past, within, ↓reduceDIte, ↓reduceIte]
    cases depth with
    | zero => simp only [padded, Array.getElem?_eq_getElem within, Option.getD_some]
    | succ d =>
      cases d with
      | zero => simp only [leaf, within, Nat.pow_zero, ↓reduceDIte]
      | succ d =>
        let childDepth := d + 1
        by_cases serial :
            (decide (childDepth < 6) || decide (chunks.size.log2 < childDepth)) = true
        · simp only [childDepth] at serial
          simp only [serial, ↓reduceIte]
          rfl

        · simp only [childDepth] at serial
          simp only [serial]
          let minimum := max 64 ((chunks.size + 7) / 8)
          by_cases fork : (decide (minimum ≤ 2 ^ childDepth) &&
              decide (start + 2 ^ childDepth + minimum ≤ chunks.size)) = true
          · simp only [childDepth, minimum] at fork
            rw [ite_eq_left fork]
            rfl
          · simp only [childDepth, minimum] at fork
            rw [ite_eq_right fork]
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
  rw [subtreeAtM_unfold]
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
  unfold merkleizeBoundedUnchecked merkleizeBoundedUncheckedM merkleizeBoundedFromM
  cases limit with
  | none => rfl
  | some capacity =>
    by_cases over : capacity < chunks.size
    · simp only [over, ↓reduceIte]
      rfl
    · simp only [over, ↓reduceIte]
      rfl

/-- With any hasher in the identity monad, the bounded root checks the capacity first. -/
theorem merkleizeBoundedUncheckedM_id_eq (hasher : Hasher Id) (chunks : Array Bytes)
    (limit : Option Nat) :
    (merkleizeBoundedUncheckedM hasher chunks limit).run = (do
      match limit with
      | some capacity =>
        if capacity < chunks.size then throw (.merkleizeLimit chunks.size capacity)
        return (subtreeAtM hasher chunks (depthFor capacity) 0).run
      | none => return (subtreeAtM hasher chunks (depthFor chunks.size) 0).run
        : Except Err Bytes) := by
  unfold merkleizeBoundedUncheckedM merkleizeBoundedFromM
  cases limit with
  | none => rfl
  | some capacity =>
    by_cases over : capacity < chunks.size
    · simp only [over, ↓reduceIte]
      rfl
    · simp only [over, ↓reduceIte]
      rfl

/-- The progressive root, in any lawful monad, closes an empty suffix with a zero node.

Otherwise it roots one level, then the rest, then hashes the two. -/
theorem merkleizeProgressiveUncheckedM_unfold {m : Type → Type} [Monad m] [LawfulMonad m]
    (hasher : Hasher m) (chunks : List Bytes) (level : Nat) :
    merkleizeProgressiveUncheckedM hasher chunks level =
      if chunks.isEmpty then pure zeroChunk
      else
        subtreeAtM hasher (chunks.take (4 ^ level)).toArray (depthFor (4 ^ level)) 0
          >>= fun here =>
            merkleizeProgressiveUncheckedM hasher (chunks.drop (4 ^ level)) (level + 1)
              >>= fun rest => combineM hasher.hash here rest := by
  unfold merkleizeProgressiveUncheckedM
  rw [progressiveWindows]
  split
  · simp [spineM]
  · -- The first run is rooted before the others, and its root is hashed last.
    simp [List.mapM_cons, spineM, List.foldrM_cons]

/-- The progressive root closes an empty suffix with a zero node.

Otherwise it hashes the root of one level against the root of the rest. -/
theorem merkleizeProgressiveUnchecked_unfold (chunks : List Bytes) (level : Nat) :
    merkleizeProgressiveUnchecked chunks level =
      if chunks.isEmpty then zeroChunk
      else
        combine (subtreeAt (chunks.take (4 ^ level)).toArray (depthFor (4 ^ level)) 0)
          (merkleizeProgressiveUnchecked (chunks.drop (4 ^ level)) (level + 1)) := by
  unfold merkleizeProgressiveUnchecked
  rw [merkleizeProgressiveUncheckedM_unfold]
  split <;> rfl

/-- Mixing a word in folds it in as the right child, with SHA-256. -/
theorem mixIn_eq (root word : Bytes) : mixIn root word = combine root word :=
  rfl

end EthLib.Serialization.Ssz
