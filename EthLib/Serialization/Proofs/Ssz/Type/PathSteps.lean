import EthLib.Serialization.Proofs.Ssz.Type.PathLaws

/-! Each type path step names its declared field, packed chunk, or mixing word. -/

namespace EthLib.Serialization.Ssz

/-- A vector element selects the chunk containing its byte range. -/
theorem resolveStep_vector (element : Desc) (count ordinal : Nat) (inside : ordinal < count) :
    (Desc.vector element count).resolveStep (.position ordinal) = .ok
      (nextPow2 ((count * element.itemLength + bytesPerChunk - 1) / bytesPerChunk) +
        ordinal * element.itemLength / bytesPerChunk, some element) := by
  -- Basic elements share chunks, while composite elements occupy all thirty-two bytes.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Desc.chunkCount, Nat.not_le.mpr inside, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A bounded list element selects its packed chunk below the contents child. -/
theorem resolveStep_list (element : Desc) (count ordinal : Nat) (inside : ordinal < count) :
    (Desc.list element count).resolveStep (.position ordinal) = (do
      let index ← gindexConcat 2
        (nextPow2 ((count * element.itemLength + bytesPerChunk - 1) / bytesPerChunk) +
          ordinal * element.itemLength / bytesPerChunk)
      pure (index, some element)) := by
  -- The extra leading left turn passes the list's length word.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Desc.chunkCount, Nat.not_le.mpr inside, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A progressive list element selects its packed chunk along the growing spine. -/
theorem resolveStep_progressiveList (element : Desc) {limit : Option Nat} (ordinal : Nat) :
    (Desc.progressiveList element limit).resolveStep (.position ordinal) = .ok
      (progressiveChunkGindex (ordinal * element.itemLength / bytesPerChunk), some element) := by
  -- A bound never reaches the tree, so every position has a type-level address.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A byte vector position selects the chunk containing that byte. -/
theorem resolveStep_byteVector (count ordinal : Nat) (inside : ordinal < count) :
    (Desc.byteVector count).resolveStep (.position ordinal) = .ok
      (nextPow2 ((count + bytesPerChunk - 1) / bytesPerChunk) + ordinal / bytesPerChunk,
        some (.uint 1)) := by
  -- Thirty-two consecutive bytes share one generalized index.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Desc.itemLength, Desc.chunkCount, Nat.not_le.mpr inside,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A byte list position selects its chunk below the length-bearing root. -/
theorem resolveStep_byteList (count ordinal : Nat) (inside : ordinal < count) :
    (Desc.byteList count).resolveStep (.position ordinal) = (do
      let index ← gindexConcat 2
        (nextPow2 ((count + bytesPerChunk - 1) / bytesPerChunk) + ordinal / bytesPerChunk)
      pure (index, some (.uint 1))) := by
  -- Byte packing agrees with a list of one-byte unsigned integers.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Desc.itemLength, Desc.chunkCount, Nat.not_le.mpr inside,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A bit vector position selects the chunk containing that bit. -/
theorem resolveStep_bitVector (count ordinal : Nat) (inside : ordinal < count) :
    (Desc.bitVector count).resolveStep (.position ordinal) = .ok
      (nextPow2 ((count + 8 * bytesPerChunk - 1) / (8 * bytesPerChunk)) +
        ordinal / (8 * bytesPerChunk), some .bool) := by
  -- Two hundred fifty-six consecutive bits share one generalized index.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Desc.chunkCount, Nat.not_le.mpr inside, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A bounded bit list position selects its chunk below the contents child. -/
theorem resolveStep_bitList (count ordinal : Nat) (inside : ordinal < count) :
    (Desc.bitList count).resolveStep (.position ordinal) = (do
      let index ← gindexConcat 2
        (nextPow2 ((count + 8 * bytesPerChunk - 1) / (8 * bytesPerChunk)) +
          ordinal / (8 * bytesPerChunk))
      pure (index, some .bool)) := by
  -- The length word is separate from the packed data and its zero padding.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Desc.chunkCount, Nat.not_le.mpr inside, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A progressive bit list position selects its packed chunk along the spine. -/
theorem resolveStep_progressiveBitList {limit : Option Nat} (ordinal : Nat) :
    (Desc.progressiveBitList limit).resolveStep (.position ordinal) = .ok
      (progressiveChunkGindex (ordinal / (8 * bytesPerChunk)), some .bool) := by
  -- The spine grows by chunks, independently of the bit's offset inside its chunk.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.positionCount,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A progressive field selects its active layout position, including preceding gaps. -/
theorem resolveStep_progressiveContainer (active : List Bool) (names : List String)
    (fields : List Desc) (ordinal position : Nat) (child : Desc)
    (selected : fields[ordinal]? = some child)
    (placed : layoutPosition active ordinal = .ok position) :
    (Desc.progressiveContainer active names fields).resolveStep (.position ordinal) =
      .ok (progressiveChunkGindex position, some child) := by
  -- EIP-7495 fields follow active positions rather than their consecutive ordinals.
  simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, selected, placed,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Every declared union option selects the contents child opposite the selector word. -/
theorem resolveStep_compatibleUnion (selectors : List Nat) (options : List Desc)
    (selector slot : Nat) (selected : selectors.idxOf? selector = some slot) :
    (Desc.compatibleUnion selectors options).resolveStep (.position selector) =
      .ok (2, some options[slot]!) := by
  -- EIP-8016 keeps the option's own tree under the left child regardless of its selector.
  simp [Desc.resolveStep, selected, Pure.pure, Except.pure]

end EthLib.Serialization.Ssz
