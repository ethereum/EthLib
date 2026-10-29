import EthLib.Consensus.Proofs.Ssz.Codec.Admits
import EthLib.Consensus.Proofs.Ssz.Codec.LengthBinding
import EthLib.Consensus.Proofs.Ssz.Codec.RootLaws

/-! The layout mixed into a progressive container's root tells absent fields from zero values. -/

namespace EthLib.Consensus.Ssz

/-- A progressive container's root hashes a 32-byte contents node beside its layout word. -/
theorem hashTreeRoot_progressiveContainer_mixin {active : List Bool} {names : List String}
    {fields : List Desc} {value : Value} {root : Bytes}
    (rooted : hashTreeRoot (.progressiveContainer active names fields) value = .ok root) :
    ∃ contents : Bytes, contents.size = bytesPerChunk ∧
      root = combine contents (activeFieldsWord active) := by
  obtain ⟨layout, chunks, contents, laid, _, merkleized, mixed⟩ :=
    hashTreeRoot_materializes _ _ _ rooted
  -- Only a sequence value has a layout under this declaration.
  cases value <;> simp only [merkleLayout, bind, Except.bind] at laid <;> try contradiction
  split at laid
  · contradiction
  · cases laid
    simp [MerkleLayout.nesting] at merkleized mixed
    subst merkleized
    exact ⟨_, merkleizeProgressiveUnchecked_size _ _, mixed⟩

/--
Two legal progressive containers with different layouts and one root expose a SHA-256 collision.
The final hash takes the contents node and the layout word, 64 bytes in all.
Equal inputs would give equal layout words, and legal layouts with equal words are equal.
So different layouts give different inputs with one digest.
-/
theorem hashTreeRoot_progressiveContainer_layouts_separate
    {leftActive rightActive : List Bool} {leftNames rightNames : List String}
    {leftFields rightFields : List Desc} {left right : Value} {root : Bytes}
    (leftLegal : (Desc.progressiveContainer leftActive leftNames leftFields).wellFormed = .ok ())
    (rightLegal : (Desc.progressiveContainer rightActive rightNames rightFields).wellFormed = .ok ())
    (first : hashTreeRoot (.progressiveContainer leftActive leftNames leftFields) left = .ok root)
    (second : hashTreeRoot (.progressiveContainer rightActive rightNames rightFields) right = .ok root) :
    leftActive = rightActive ∨
      ∃ a b : Bytes, a.size = 2 * bytesPerChunk ∧ b.size = 2 * bytesPerChunk ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  obtain ⟨leftContents, leftWidth, rfl⟩ := hashTreeRoot_progressiveContainer_mixin first
  obtain ⟨rightContents, rightWidth, joined⟩ := hashTreeRoot_progressiveContainer_mixin second
  by_cases same : leftContents ++ activeFieldsWord leftActive = rightContents ++ activeFieldsWord rightActive
  · -- Equal 32-byte left halves leave equal right halves, which are the layout words.
    have ⟨leftEnds, leftBounded⟩ := wellFormed_progressiveContainer_layout leftLegal
    have ⟨rightEnds, rightBounded⟩ := wellFormed_progressiveContainer_layout rightLegal
    -- At most 256 positions is exactly one bit per position of the word.
    exact .inl (activeFieldsWord_injective_of_legal leftEnds rightEnds
      (by simpa [bitsPerChunk, bytesPerChunk] using leftBounded)
      (by simpa [bitsPerChunk, bytesPerChunk] using rightBounded)
      (Array.append_inj same (leftWidth.trans rightWidth.symm)).2)
  · -- Different inputs reached the same root, which is the collision.
    refine .inr ⟨_, _, by simp [leftWidth, Nat.two_mul], by simp [rightWidth, Nat.two_mul], same, ?_⟩
    apply ByteArray.ext
    simpa [combine] using joined

end EthLib.Consensus.Ssz
