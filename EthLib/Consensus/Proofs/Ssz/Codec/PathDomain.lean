import EthLib.Consensus.Proofs.Ssz.Codec.PathSelection
import EthLib.Consensus.Proofs.Ssz.Codec.RootDomain

/-! Admissible packed values select the complete chunk containing each addressed byte or bit. -/

namespace EthLib.Consensus.Ssz

private theorem byte_position_inside (count ordinal : Nat) (inside : ordinal < count) :
    ordinal / bytesPerChunk < chunksForBytes count := by
  -- Rounding the byte count upward includes the chunk containing every earlier byte.
  simp only [chunksForBytes, bytesPerChunk]
  omega

private theorem bit_position_inside (count ordinal : Nat) (inside : ordinal < count) :
    ordinal / (8 * bytesPerChunk) < chunksForBits count := by
  -- Each complete chunk covers 256 consecutive bits, including a partial final group.
  simp only [chunksForBits, bytesPerChunk]
  omega

private theorem packedBits_size (data : Array Bool) :
    (packedBits data).size = chunksForBits data.size := by
  -- Rounding first to bytes and then to chunks equals rounding directly to 256 bits.
  simp only [packedBits, packBytes_size, packBits, Array.size_ofFn, chunksForBits, bytesPerChunk]
  omega

private theorem packing_materialized (budget : Nat) (chunks : Array Bytes)
    (limit : Option Nat) (mixin : Option Bytes) :
    layoutChunksAt budget (.packing chunks limit mixin) = .ok chunks := by
  -- Packed data already consists of leaves, so materialization only preserves their order.
  simp [layoutChunksAt, MerkleLayout.packing, Leaves.count, Pure.pure, Except.pure]

/-- A byte-vector position selects its containing packed chunk. -/
theorem PathSelects.byteVector (count : Nat) (data : Bytes)
    (fitted : Fits (.byteVector count) (.bytes data)) (ordinal : Nat) (inside : ordinal < count) :
    PathSelects (.byteVector count) (.bytes data) [.position ordinal]
      (padded zeroChunk (packBytes data) (ordinal / bytesPerChunk)) := by
  -- Fixed byte vectors commit to the encoding's chunks without a length word.
  cases fitted with
  | byteVector exact =>
    refine PathSelects.packed (layout := .packing (packBytes data) (some (chunksForBytes count)))
      ?_ (packing_materialized _ _ _ _) rfl rfl rfl ?_
      (byte_position_inside count ordinal inside) (resolveStep_byteVector count ordinal inside)
    · simp [merkleLayout, exact, packBytes_size, chunksForBytes, Pure.pure, Except.pure]
    · simp [packBytes_size, exact, chunksForBytes]

/-- A byte-list position selects its containing chunk beneath the length word. -/
theorem PathSelects.byteList (limit : Nat) (data : Bytes)
    (fitted : Fits (.byteList limit) (.bytes data)) (ordinal : Nat) (inside : ordinal < limit) :
    PathSelects (.byteList limit) (.bytes data) [.position ordinal]
      (padded zeroChunk (packBytes data) (ordinal / bytesPerChunk)) := by
  -- Declared but unfilled capacity is represented by zero padding in the same packed tree.
  cases fitted with
  | byteList within =>
    -- The selected byte offset lies in a chunk within the declared byte capacity.
    have chunkInside := byte_position_inside limit ordinal inside
    refine PathSelects.packedMixed (child := .uint 1)
      (layout := .packing (packBytes data) (some (chunksForBytes limit)) (lengthWord data.size))
      ?_ (packing_materialized _ _ _ _) rfl rfl rfl ?_ chunkInside ?_
    · simp [merkleLayout, Nat.not_lt.mpr within, Pure.pure, Except.pure]
    · simp only [packBytes_size, chunksForBytes, bytesPerChunk]; omega
    -- The list’s length word adds one left turn before the packed chunk’s own path.
    · have joined := gindexConcat_mixed_leaf chunkInside
      simp only [chunksForBytes] at joined ⊢
      rw [resolveStep_byteList limit ordinal inside, joined]
      rfl

/-- A bit-vector position selects the chunk containing its 256-bit group. -/
theorem PathSelects.bitVector (count : Nat) (data : Array Bool)
    (fitted : Fits (.bitVector count) (.bits data)) (ordinal : Nat) (inside : ordinal < count) :
    PathSelects (.bitVector count) (.bits data) [.position ordinal]
      (padded zeroChunk (packedBits data) (ordinal / (8 * bytesPerChunk))) := by
  -- Fixed bits carry no delimiter or length word in their Merkle chunks.
  cases fitted with
  | bitVector exact =>
    refine PathSelects.packed (layout := .packing (packedBits data) (some (chunksForBits count)))
      ?_ (packing_materialized _ _ _ _) rfl rfl rfl ?_
      (bit_position_inside count ordinal inside) (resolveStep_bitVector count ordinal inside)
    · simp [merkleLayout, exact, Pure.pure, Except.pure]
    · simp [packedBits_size, exact]

/-- A bounded bit-list position selects its chunk beneath the separate bit count. -/
theorem PathSelects.bitList (limit : Nat) (data : Array Bool)
    (fitted : Fits (.bitList limit) (.bits data)) (ordinal : Nat) (inside : ordinal < limit) :
    PathSelects (.bitList limit) (.bits data) [.position ordinal]
      (padded zeroChunk (packedBits data) (ordinal / (8 * bytesPerChunk))) := by
  -- The declared capacity bounds packed data, while the current length is committed separately.
  cases fitted with
  | bitList within =>
    -- The declared bit capacity bounds the selected group of 256 bits.
    have chunkInside := bit_position_inside limit ordinal inside
    refine PathSelects.packedMixed (child := .bool)
      (layout := .packing (packedBits data) (some (chunksForBits limit)) (lengthWord data.size))
      ?_ (packing_materialized _ _ _ _) rfl rfl rfl ?_ chunkInside ?_
    · simp [merkleLayout, Nat.not_lt.mpr within, Pure.pure, Except.pure]
    · simp only [packedBits_size, chunksForBits, bytesPerChunk]; omega
    -- The list’s length word adds one left turn before the packed chunk’s own path.
    · have joined := gindexConcat_mixed_leaf chunkInside
      simp only [chunksForBits] at joined ⊢
      rw [resolveStep_bitList limit ordinal inside, joined]
      rfl

/-- A progressive bit-list position selects the occupied chunk containing that bit. -/
theorem PathSelects.progressiveBitList {limit : Option Nat} (data : Array Bool)
    (within : withinBound limit data.size = true) (ordinal : Nat) (inside : ordinal < data.size) :
    PathSelects (.progressiveBitList limit) (.bits data) [.position ordinal]
      (padded zeroChunk (packedBits data) (ordinal / (8 * bytesPerChunk))) := by
  -- An actual bit lies in an occupied chunk, which determines a finite level on the progressive spine.
  refine PathSelects.packedProgressive
    (layout := .packing (packedBits data) none (lengthWord data.size))
    (by simp [merkleLayout, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind]; rfl)
    (packing_materialized _ _ _ _) rfl rfl rfl ?_ (resolveStep_progressiveBitList ordinal)
  exact packedBits_size data ▸ bit_position_inside data.size ordinal inside

private theorem basic_width_positive (element : Desc) (basic : element.isBasic = true)
    (sound : element.wellFormed = .ok ()) : 0 < element.itemLength := by
  -- Booleans occupy one byte, and the permitted unsigned widths are all positive.
  cases element <;> simp only [Desc.isBasic, Bool.false_eq_true] at basic
  case bool => decide
  case uint width => rw [Desc.wellFormed] at sound; cases width <;> simp_all [Desc.itemLength]

/-- A basic vector element selects the chunk containing its serialized bytes. -/
theorem PathSelects.vector_basic (element : Desc) (count : Nat) (values : List Value)
    (basic : element.isBasic = true) (sound : (Desc.vector element count).wellFormed = .ok ())
    (fitted : Fits (.vector element count) (.seq values)) (ordinal : Nat) (inside : ordinal < count) :
    ∃ parts, serializeEach element values = .ok parts ∧
      PathSelects (.vector element count) (.seq values) [.position ordinal]
        (padded zeroChunk (packElements parts) (ordinal * element.itemLength / bytesPerChunk)) := by
  -- Basic elements pack consecutively, so the first byte offset determines the containing chunk.
  cases fitted with
  | vector counted each =>
    -- Basic elements always serialize successfully to a fixed-width stream without offset tables.
    obtain ⟨parts, wrote, size⟩ := serializeEach_basic_size basic values each
    have width := basic_width_positive element basic (wellFormed_vector sound)
    -- The selected byte offset lies in a chunk within the declared byte capacity.
    have chunkInside := byte_position_inside (count * element.itemLength) (ordinal * element.itemLength)
      (Nat.mul_lt_mul_of_pos_right inside width)
    refine ⟨parts, wrote, PathSelects.packed (child := element)
      (layout := .packing (packElements parts) (some (chunksForBytes (count * element.itemLength))))
      ?_ (packing_materialized _ _ _ _) rfl rfl rfl ?_ chunkInside
      (resolveStep_vector element count ordinal inside)⟩
    · simp [merkleLayout, sequenceLayout, counted, basic, wrote,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [packElements, packBytes_size, size, counted, chunksForBytes]

/-- A basic bounded-list element selects its packed chunk beneath the element count. -/
theorem PathSelects.list_basic (element : Desc) (limit : Nat) (values : List Value)
    (basic : element.isBasic = true) (sound : (Desc.list element limit).wellFormed = .ok ())
    (fitted : Fits (.list element limit) (.seq values)) (ordinal : Nat) (inside : ordinal < limit) :
    ∃ parts, serializeEach element values = .ok parts ∧
      PathSelects (.list element limit) (.seq values) [.position ordinal]
        (padded zeroChunk (packElements parts) (ordinal * element.itemLength / bytesPerChunk)) := by
  -- The declared element capacity is converted to byte capacity before selecting a packed node.
  cases fitted with
  | list within each =>
    -- Basic elements always serialize successfully to a fixed-width stream without offset tables.
    obtain ⟨parts, wrote, size⟩ := serializeEach_basic_size basic values each
    have width := basic_width_positive element basic (wellFormed_list sound)
    -- The selected byte offset lies in a chunk within the declared byte capacity.
    have chunkInside := byte_position_inside (limit * element.itemLength) (ordinal * element.itemLength)
      (Nat.mul_lt_mul_of_pos_right inside width)
    refine ⟨parts, wrote, PathSelects.packedMixed (child := element)
      (layout := .packing (packElements parts) (some (chunksForBytes (limit * element.itemLength)))
        (lengthWord values.length))
      ?_ (packing_materialized _ _ _ _) rfl rfl rfl ?_ chunkInside ?_⟩
    · simp [merkleLayout, sequenceLayout, Nat.not_lt.mpr within, basic, wrote,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    -- An element-count bound also bounds the total bytes because every element has the same width.
    · have bytesWithin := Nat.mul_le_mul_right element.itemLength within
      simp only [packElements, packBytes_size, size, chunksForBytes, bytesPerChunk]
      omega
    -- The list’s length word adds one left turn before the packed chunk’s own path.
    · have joined := gindexConcat_mixed_leaf chunkInside
      simp only [chunksForBytes] at joined ⊢
      rw [resolveStep_list element limit ordinal inside, joined]
      rfl

/-- A present basic progressive-list element selects an occupied chunk on the spine. -/
theorem PathSelects.progressiveList_basic (element : Desc) {limit : Option Nat}
    (values : List Value) (basic : element.isBasic = true)
    (sound : (Desc.progressiveList element limit).wellFormed = .ok ())
    (fitted : Fits (.progressiveList element limit) (.seq values)) (ordinal : Nat)
    (inside : ordinal < values.length) :
    ∃ parts, serializeEach element values = .ok parts ∧
      PathSelects (.progressiveList element limit) (.seq values) [.position ordinal]
        (padded zeroChunk (packElements parts) (ordinal * element.itemLength / bytesPerChunk)) := by
  -- Present elements lie in occupied chunks, whose spine positions remain stable as the list grows.
  cases fitted with
  | progressiveList within each =>
    -- Basic elements always serialize successfully to a fixed-width stream without offset tables.
    obtain ⟨parts, wrote, size⟩ := serializeEach_basic_size basic values each
    have width := basic_width_positive element basic (wellFormed_progressiveList sound)
    -- The selected byte offset lies in a chunk within the declared byte capacity.
    have chunkInside := byte_position_inside (values.length * element.itemLength)
      (ordinal * element.itemLength) (Nat.mul_lt_mul_of_pos_right inside width)
    refine ⟨parts, wrote, PathSelects.packedProgressive (child := element)
      (layout := .packing (packElements parts) none (lengthWord values.length))
      ?_ (packing_materialized _ _ _ _) rfl rfl rfl ?_ (resolveStep_progressiveList element ordinal)⟩
    · simp [merkleLayout, sequenceLayout, basic, wrote, boundCheck_of_withinBound limit _ within,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simpa [packElements, packBytes_size, size, chunksForBytes] using chunkInside

end EthLib.Consensus.Ssz
