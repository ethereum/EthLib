module

public import EthLib.Serialization.Proofs.Ssz.Codec.Admits
public import EthLib.Serialization.Proofs.Ssz.Codec.LengthBinding
public import EthLib.Serialization.Proofs.Ssz.Codec.RootLaws

/-!
The layout mixed into a progressive container's root tells absent fields from zero values.

Two layouts under one root are equal, or a search finds a SHA-256 collision.

The same holds for any hash with 32-byte digests, with the zero subtrees computed by that hash.

The search compares the last hash inputs of the two roots, so it can come back empty.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open EthLib.Base

/-- The input of a root's last hash when its shape mixes a word in, with a hash in any monad.

It is the contents node, then the word.

A shape that mixes in no word has no such input. -/
def mixinMessageM {m : Type → Type} [Monad m] (hasher : Hasher m) (shape : Desc) (value : Value) :
    ExceptT Err m (Option Bytes) := do
  let layout ← merkleLayout shape value
  let chunks ← layoutChunksAtM hasher (shape.nesting - 1) layout
  let contents ← match layout.limit with
    | none => ExceptT.lift (merkleizeProgressiveUncheckedM hasher chunks.toList)
    | some capacity => merkleizeBoundedUncheckedM hasher chunks (some capacity)
  return layout.mixin.map (contents ++ ·)

/-- The input of a root's last hash when its shape mixes a word in.

It is the contents node, then the word.

The hash is SHA-256 unless another one is given, and it computes the zero subtrees too.

A shape that mixes in no word, or a value that does not fit, has no such input. -/
def mixinMessage (shape : Desc) (value : Value)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) : Option Bytes :=
  match (mixinMessageM (Hasher.ofHash (m := Id) hash) shape value).run with
  | .ok message => message
  | .error _ => none

/-- With any hasher in the identity monad, the input reads the layout, leaves and contents. -/
theorem mixinMessageM_id_eq (hasher : Hasher Id) (shape : Desc) (value : Value) :
    (mixinMessageM hasher shape value).run = (do
      let layout ← merkleLayout shape value
      let chunks ← (layoutChunksAtM hasher (shape.nesting - 1) layout).run
      let contents ← match layout.limit with
        | none => .ok (merkleizeProgressiveUncheckedM hasher chunks.toList).run
        | some capacity => (merkleizeBoundedUncheckedM hasher chunks (some capacity)).run
      return layout.mixin.map (contents ++ ·) : Except Err (Option Bytes)) := by
  simp only [mixinMessageM, ExceptT.run, exceptT_id_bind, exceptT_id_monadLift,
    exceptT_id_lift, exceptT_id_pure, except_bind_eq]
  cases merkleLayout shape value with
  | error => rfl
  | ok layout =>
    simp only [Except.bind]
    cases layout.limit <;> rfl

/-- A progressive container's root hashes a 32-byte contents node beside its layout word.

The root is the one that a hash with 32-byte digests computes. -/
theorem hashTreeRootM_progressiveContainer_mixin (hash : ByteArray → ByteArray)
    (width : ∀ x, (hash x).size = 32) {active : List Bool} {names : List String}
    {fields : List Desc} {value : Value} {root : Bytes}
    (rooted : (hashTreeRootM (Hasher.ofHash (m := Id) hash)
      (.progressiveContainer active names fields) value).run = .ok root) :
    ∃ contents : Bytes, contents.size = bytesPerChunk ∧
      mixinMessage (.progressiveContainer active names fields) value hash
        = some (contents ++ activeFieldsWord active) ∧
      root = (hash (ByteArray.mk (contents ++ activeFieldsWord active))).data := by
  -- The root spends one level of its budget, and both read the leaves with the rest.
  have budget : (Desc.progressiveContainer active names fields).nesting
      = Desc.deepestNesting fields + 1 := by
    simp [Desc.nesting]
  rw [hashTreeRootM, budget, hashTreeRootAtM_id_succ] at rooted
  simp only [mixinMessage, mixinMessageM_id_eq, budget, Nat.add_sub_cancel]
  -- Only a sequence value has a layout under this declaration.
  cases value <;> simp only [merkleLayout, bind, Except.bind] at rooted ⊢ <;> try contradiction
  rename_i elements
  -- The layout places the fields on a progressive spine and mixes the layout word in.
  cases placed : layoutSlots active fields elements with
  | error => simp [placed] at rooted
  | ok slots =>
    simp only [placed, pure, Except.pure, MerkleLayout.nesting] at rooted ⊢
    split at rooted
    · contradiction
    · simp only [Option.map]
      refine ⟨_, ?_, rfl, (Except.ok.inj rooted).symm⟩
      -- A progressive root is a zero node or a digest, so it is one node wide.
      rw [merkleizeProgressiveUncheckedM]
      split
      · exact zeroChunk_size
      · exact width _

/-- A progressive container's root hashes a 32-byte contents node beside its layout word. -/
theorem hashTreeRoot_progressiveContainer_mixin {active : List Bool} {names : List String}
    {fields : List Desc} {value : Value} {root : Bytes}
    (rooted : hashTreeRoot (.progressiveContainer active names fields) value = .ok root) :
    ∃ contents : Bytes, contents.size = bytesPerChunk ∧
      mixinMessage (.progressiveContainer active names fields) value
        = some (contents ++ activeFieldsWord active) ∧
      root = combine contents (activeFieldsWord active) := by
  -- The specification's hasher is the one built from SHA-256 alone.
  rw [hashTreeRoot, ← ofHash_sha256] at rooted
  obtain ⟨contents, width, message, rfl⟩ := hashTreeRootM_progressiveContainer_mixin _
    Cryptography.Hash.Sha256.hash_size rooted
  exact ⟨contents, width, message, (combine_eq _ _).symm⟩

/-- The collision between the last hash inputs of two roots, if they collide there.

The hash is SHA-256 unless another one is given.

It reads only the two shapes and the two values. -/
def findMixinCollision (leftShape rightShape : Desc) (left right : Value)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) : Option (Bytes × Bytes) := do
  let a ← mixinMessage leftShape left hash
  let b ← mixinMessage rightShape right hash
  if a ≠ b ∧ hash (ByteArray.mk a) = hash (ByteArray.mk b) then
    some (a, b)
  else none

/-- The search returns the last hash inputs of the two roots, which differ and share a digest. -/
theorem findMixinCollision_valid {leftShape rightShape : Desc} {left right : Value}
    {hash : ByteArray → ByteArray} {a b : Bytes}
    (found : findMixinCollision leftShape rightShape left right hash = some (a, b)) :
    mixinMessage leftShape left hash = some a ∧ mixinMessage rightShape right hash = some b ∧
      a ≠ b ∧ hash (ByteArray.mk a) = hash (ByteArray.mk b) := by
  simp only [findMixinCollision, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
  obtain ⟨a', leftMessage, b', rightMessage, found⟩ := found
  split at found
  · cases found
    exact ⟨leftMessage, rightMessage, ‹_ ∧ _›⟩
  · contradiction

/-- One value compared with itself runs into no collision. -/
theorem findMixinCollision_self (shape : Desc) (value : Value)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) :
    findMixinCollision shape shape value value hash = none := by
  -- The two inputs are the same input.
  cases h : mixinMessage shape value hash <;> simp [findMixinCollision, h]

/--
Two legal progressive containers with one root have one layout, or the search finds a collision.

The root is the one that a hash with 32-byte digests computes.

The final hash takes the contents node and the layout word, 64 bytes in all.

Equal inputs would give equal layout words, and legal layouts with equal words are equal.

So different layouts give different inputs with one digest, and the search returns them.
-/
theorem hashTreeRootM_progressiveContainer_layouts_separate (hash : ByteArray → ByteArray)
    (width : ∀ x, (hash x).size = 32)
    {leftActive rightActive : List Bool} {leftNames rightNames : List String}
    {leftFields rightFields : List Desc} {left right : Value} {root : Bytes}
    (leftLegal : (Desc.progressiveContainer leftActive leftNames leftFields).wellFormed = .ok ())
    (rightLegal :
      (Desc.progressiveContainer rightActive rightNames rightFields).wellFormed = .ok ())
    (first : (hashTreeRootM (Hasher.ofHash (m := Id) hash)
      (.progressiveContainer leftActive leftNames leftFields) left).run = .ok root)
    (second : (hashTreeRootM (Hasher.ofHash (m := Id) hash)
      (.progressiveContainer rightActive rightNames rightFields) right).run = .ok root) :
    leftActive = rightActive ∨
      ∃ a b, findMixinCollision (.progressiveContainer leftActive leftNames leftFields)
          (.progressiveContainer rightActive rightNames rightFields) left right hash = some (a, b) ∧
        a.size = 2 * bytesPerChunk ∧ b.size = 2 * bytesPerChunk ∧ a ≠ b ∧
        hash (ByteArray.mk a) = hash (ByteArray.mk b) := by
  obtain ⟨leftContents, leftWidth, leftMessage, rfl⟩ :=
    hashTreeRootM_progressiveContainer_mixin hash width first
  obtain ⟨rightContents, rightWidth, rightMessage, joined⟩ :=
    hashTreeRootM_progressiveContainer_mixin hash width second
  by_cases same :
      leftContents ++ activeFieldsWord leftActive = rightContents ++ activeFieldsWord rightActive
  · -- Equal 32-byte left halves leave equal right halves, which are the layout words.
    have ⟨leftEnds, leftBounded⟩ := wellFormed_progressiveContainer_layout leftLegal
    have ⟨rightEnds, rightBounded⟩ := wellFormed_progressiveContainer_layout rightLegal
    -- At most 256 positions is exactly one bit per position of the word.
    exact .inl (activeFieldsWord_injective_of_legal leftEnds rightEnds
      (by simpa [bitsPerChunk, bytesPerChunk] using leftBounded)
      (by simpa [bitsPerChunk, bytesPerChunk] using rightBounded)
      (Array.append_inj same (leftWidth.trans rightWidth.symm)).2)
  · -- Different inputs reached the same root, so the search stops at them.
    have hashed : hash (ByteArray.mk (leftContents ++ activeFieldsWord leftActive))
        = hash (ByteArray.mk (rightContents ++ activeFieldsWord rightActive)) :=
      ByteArray.ext joined
    refine .inr ⟨_, _, ?_, by simp [leftWidth, Nat.two_mul], by simp [rightWidth, Nat.two_mul],
      same, hashed⟩
    simp [findMixinCollision, leftMessage, rightMessage, same, hashed]

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
    (rightLegal :
      (Desc.progressiveContainer rightActive rightNames rightFields).wellFormed = .ok ())
    (first : hashTreeRoot (.progressiveContainer leftActive leftNames leftFields) left = .ok root)
    (second :
      hashTreeRoot (.progressiveContainer rightActive rightNames rightFields) right = .ok root) :
    leftActive = rightActive ∨
      ∃ a b, findMixinCollision (.progressiveContainer leftActive leftNames leftFields)
          (.progressiveContainer rightActive rightNames rightFields) left right = some (a, b) ∧
        a.size = 2 * bytesPerChunk ∧ b.size = 2 * bytesPerChunk ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a)
          = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  -- The specification's hasher is the one built from SHA-256 alone.
  rw [hashTreeRoot, ← ofHash_sha256] at first second
  exact hashTreeRootM_progressiveContainer_layouts_separate _ Cryptography.Hash.Sha256.hash_size
    leftLegal rightLegal first second

end EthLib.Serialization.Ssz
