module

public import EthLib.Serialization.Proofs.Ssz.Codec.Admits
public import EthLib.Serialization.Proofs.Ssz.Codec.LengthBinding
public import EthLib.Serialization.Proofs.Ssz.Codec.RootLaws

/-!
The layout mixed into a progressive container's root tells absent fields from zero values.

Two layouts under one root are equal, or a search finds a SHA-256 collision.

The search compares the last hash inputs of the two roots, so it can come back empty.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The input of a root's last hash when its shape mixes a word in.

It is the contents node, then the word.

A shape that mixes in no word, or a value that does not fit, has no such input. -/
def mixinMessage (shape : Desc) (value : Value) : Option Bytes := do
  let layout ← (merkleLayout shape value).toOption
  let chunks ← (layoutChunksAt (shape.nesting - 1) layout).toOption
  let contents ← (match layout.limit with
    | none => Except.ok (merkleizeProgressiveUnchecked chunks.toList)
    | some capacity => merkleizeBoundedUnchecked chunks (some capacity)).toOption
  let word ← layout.mixin
  return contents ++ word

/-- A progressive container's root hashes a 32-byte contents node beside its layout word. -/
theorem hashTreeRoot_progressiveContainer_mixin {active : List Bool} {names : List String}
    {fields : List Desc} {value : Value} {root : Bytes}
    (rooted : hashTreeRoot (.progressiveContainer active names fields) value = .ok root) :
    ∃ contents : Bytes, contents.size = bytesPerChunk ∧
      mixinMessage (.progressiveContainer active names fields) value
        = some (contents ++ activeFieldsWord active) ∧
      root = combine contents (activeFieldsWord active) := by
  obtain ⟨layout, chunks, contents, laid, chunked, merkleized, mixed⟩ :=
    hashTreeRoot_materializes _ _ _ rooted
  -- The last hash input is read from the same layout, leaves and contents as the root.
  have message : ∀ word, layout.mixin = some word →
      mixinMessage (.progressiveContainer active names fields) value = some (contents ++ word) := by
    intro word mixes
    simp only [mixinMessage, laid, chunked, mixes, Except.toOption, Option.bind_some, bind, pure]
    split at merkleized <;> simp_all
  -- Only a sequence value has a layout under this declaration.
  cases value <;> simp only [merkleLayout, bind, Except.bind] at laid <;> try contradiction
  split at laid
  · contradiction
  · cases laid
    simp [MerkleLayout.nesting] at merkleized mixed
    subst merkleized
    exact ⟨_, merkleizeProgressiveUnchecked_size _ _, message _ rfl, mixed⟩

/-- The SHA-256 collision between the last hash inputs of two roots, if they collide there.

It reads only the two shapes and the two values. -/
def findMixinCollision (leftShape rightShape : Desc) (left right : Value) :
    Option (Bytes × Bytes) := do
  let a ← mixinMessage leftShape left
  let b ← mixinMessage rightShape right
  if a ≠ b ∧ Cryptography.Hash.Sha256.hash (ByteArray.mk a)
      = Cryptography.Hash.Sha256.hash (ByteArray.mk b) then
    some (a, b)
  else none

/-- The search returns the last hash inputs of the two roots, which differ and share a digest. -/
theorem findMixinCollision_valid {leftShape rightShape : Desc} {left right : Value}
    {a b : Bytes} (found : findMixinCollision leftShape rightShape left right = some (a, b)) :
    mixinMessage leftShape left = some a ∧ mixinMessage rightShape right = some b ∧ a ≠ b ∧
      Cryptography.Hash.Sha256.hash (ByteArray.mk a)
        = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  simp only [findMixinCollision, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
  obtain ⟨a', leftMessage, b', rightMessage, found⟩ := found
  split at found
  · cases found
    exact ⟨leftMessage, rightMessage, ‹_ ∧ _›⟩
  · contradiction

/-- One value compared with itself runs into no collision. -/
theorem findMixinCollision_self (shape : Desc) (value : Value) :
    findMixinCollision shape shape value value = none := by
  -- The two inputs are the same input.
  cases h : mixinMessage shape value <;> simp [findMixinCollision, h]

/--
Two legal progressive containers with one root have one layout, or the search finds a collision.

The final hash takes the contents node and the layout word, 64 bytes in all.

Equal inputs would give equal layout words, and legal layouts with equal words are equal.

So different layouts give different inputs with one digest, and the search returns them.
-/
theorem hashTreeRoot_progressiveContainer_layouts_separate
    {leftActive rightActive : List Bool} {leftNames rightNames : List String}
    {leftFields rightFields : List Desc} {left right : Value} {root : Bytes}
    (leftLegal : (Desc.progressiveContainer leftActive leftNames leftFields).wellFormed = .ok ())
    (rightLegal : (Desc.progressiveContainer rightActive rightNames rightFields).wellFormed = .ok ())
    (first : hashTreeRoot (.progressiveContainer leftActive leftNames leftFields) left = .ok root)
    (second : hashTreeRoot (.progressiveContainer rightActive rightNames rightFields) right = .ok root) :
    leftActive = rightActive ∨
      ∃ a b, findMixinCollision (.progressiveContainer leftActive leftNames leftFields)
          (.progressiveContainer rightActive rightNames rightFields) left right = some (a, b) ∧
        a.size = 2 * bytesPerChunk ∧ b.size = 2 * bytesPerChunk ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a)
          = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  obtain ⟨leftContents, leftWidth, leftMessage, rfl⟩ :=
    hashTreeRoot_progressiveContainer_mixin first
  obtain ⟨rightContents, rightWidth, rightMessage, joined⟩ :=
    hashTreeRoot_progressiveContainer_mixin second
  by_cases same : leftContents ++ activeFieldsWord leftActive = rightContents ++ activeFieldsWord rightActive
  · -- Equal 32-byte left halves leave equal right halves, which are the layout words.
    have ⟨leftEnds, leftBounded⟩ := wellFormed_progressiveContainer_layout leftLegal
    have ⟨rightEnds, rightBounded⟩ := wellFormed_progressiveContainer_layout rightLegal
    -- At most 256 positions is exactly one bit per position of the word.
    exact .inl (activeFieldsWord_injective_of_legal leftEnds rightEnds
      (by simpa [bitsPerChunk, bytesPerChunk] using leftBounded)
      (by simpa [bitsPerChunk, bytesPerChunk] using rightBounded)
      (Array.append_inj same (leftWidth.trans rightWidth.symm)).2)
  · -- Different inputs reached the same root, so the search stops at them.
    have hashed :
        Cryptography.Hash.Sha256.hash (ByteArray.mk (leftContents ++ activeFieldsWord leftActive))
          = Cryptography.Hash.Sha256.hash
              (ByteArray.mk (rightContents ++ activeFieldsWord rightActive)) := by
      apply ByteArray.ext
      simpa [combine] using joined
    refine .inr ⟨_, _, ?_, by simp [leftWidth, Nat.two_mul], by simp [rightWidth, Nat.two_mul],
      same, hashed⟩
    simp [findMixinCollision, leftMessage, rightMessage, same, hashed]

end EthLib.Serialization.Ssz
