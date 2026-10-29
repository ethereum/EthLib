import EthLib.Consensus.Proofs.Ssz.Codec.RoundTrip
import EthLib.Consensus.Proofs.Ssz.Codec.Layout

/-! Packing preserves payloads when their lengths are known. -/

namespace EthLib.Consensus.Ssz

/-- Equal packed nodes and equal byte counts determine the original bytes. -/
theorem packBytes_injective {left right : Bytes} (lengths : left.size = right.size)
    (packed : packBytes left = packBytes right) : left = right := by
  -- Recover each payload byte by its packed-node number and its offset inside that node.
  apply Array.ext lengths
  intro i hi hj
  -- Division by 32 selects the node, while the remainder selects a byte within it.
  have position : i % bytesPerChunk < bytesPerChunk := Nat.mod_lt _ (by decide)
  -- Recombining the node number and byte offset recovers the original payload position.
  have indexEq : i / bytesPerChunk * bytesPerChunk + i % bytesPerChunk = i := by simpa [Nat.mul_comm] using Nat.div_add_mod i bytesPerChunk
  -- Every original payload byte lies inside one of the rounded-up packed nodes.
  have inLeft : i / bytesPerChunk < (packBytes left).size := by
    simp only [packBytes_size, bytesPerChunk] at *
    omega
  have inRight : i / bytesPerChunk < (packBytes right).size := packed ▸ inLeft
  -- Reading a packed byte inside the payload returns the corresponding original byte.
  have a := packBytes_get left (i / bytesPerChunk) (i % bytesPerChunk) inLeft position
    (by omega)
  have b := packBytes_get right (i / bytesPerChunk) (i % bytesPerChunk) inRight position
    (by omega)
  simp only [indexEq] at a b
  -- Both original bytes are therefore reads from the same packed node at the same offset.
  rw [← a, ← b]
  congr 1
  simpa only [getElem!_pos, inLeft, inRight] using congrArg (fun chunks : Array Bytes => chunks[i / bytesPerChunk]!) packed

/-- A sufficient byte buffer preserves every bit of a known-length bit string. -/
theorem packBits_injective {left right : Array Bool} {byteCount : Nat}
    (lengths : left.size = right.size) (room : left.size ≤ byteCount * 8)
    (packed : packBits left byteCount = packBits right byteCount) : left = right := by
  -- Unpacking a sufficient byte buffer recovers every bit up to the known original count.
  rw [← unpackBits_packBits left byteCount (by omega),
    ← unpackBits_packBits right byteCount (by omega), lengths, packed]

/-- Node packing preserves a bit string once its bit count is known. -/
theorem packedBits_injective {left right : Array Bool} (lengths : left.size = right.size)
    (packed : packedBits left = packedBits right) : left = right := by
  -- First remove node padding using the known packed-byte count, then unpack the known number of bits.
  apply packBits_injective lengths (byteCount := (left.size + 7) / 8) (by omega)
  apply packBytes_injective (by simp [packBits, lengths])
  simpa [packedBits, lengths] using packed

/-- Fixed-width parts have a unique split when their counts agree. -/
theorem concatParts_injective {left right : List Bytes} {width : Nat}
    (counts : left.length = right.length)
    (leftWidths : ∀ part ∈ left, part.size = width)
    (rightWidths : ∀ part ∈ right, part.size = width)
    (joined : concatParts left = concatParts right) : left = right := by
  -- A fixed part width gives the same extraction boundaries in both concatenated byte strings.
  rw [← map_extract_concatParts width left leftWidths,
    ← map_extract_concatParts width right rightWidths, counts, joined]

/-- Fixed-width element streams uniquely determine their same-length value sequences. -/
theorem serializeEach_concat_injective {shape : Desc} {width : Nat}
    {left right : List Value} {leftParts rightParts : List Bytes}
    (sound : shape.wellFormed = .ok ()) (fixed : shape.fixedSize = some width)
    (counts : left.length = right.length)
    (leftFits : ∀ value ∈ left, Fits shape value)
    (rightFits : ∀ value ∈ right, Fits shape value)
    (leftWrote : serializeEach shape left = .ok leftParts)
    (rightWrote : serializeEach shape right = .ok rightParts)
    (joined : concatParts leftParts = concatParts rightParts) : left = right := by
  -- Admissibility and the fixed element type give every encoded part the same byte width.
  have leftWidths := serializeEach_widths shape left leftParts width fixed leftWrote
    (fun value member _ wrote => serialize_size_of_wellFormed sound (leftFits value member)
      fixed wrote)
  have rightWidths := serializeEach_widths shape right rightParts width fixed rightWrote
    (fun value member _ wrote => serialize_size_of_wellFormed sound (rightFits value member)
      fixed wrote)
  -- Equal counts and widths make the split of the common byte stream unique.
  have partsEqual := concatParts_injective
    (by rw [serializeEach_length shape left leftParts leftWrote,
      serializeEach_length shape right rightParts rightWrote, counts])
    leftWidths rightWidths joined
  -- Each admissible element is recovered by decoding its own encoded part.
  have leftRead := deserializeEach_reads_back shape left leftParts leftWrote
    (fun value member _ wrote => roundTrip_of_wellFormed sound (leftFits value member) wrote)
  have rightRead := deserializeEach_reads_back shape right rightParts rightWrote
    (fun value member _ wrote => roundTrip_of_wellFormed sound (rightFits value member) wrote)
  -- The same list of parts cannot decode to two different lists of values.
  rw [partsEqual, rightRead] at leftRead
  exact (Except.ok.inj leftRead).symm

/-- The executable accumulation of parts is their ordered concatenation. -/
theorem fold_parts_eq_concat (parts : List Bytes) (front : Bytes) :
    parts.foldl (fun total part => total ++ part) front = front ++ concatParts parts := by
  -- Appending parts to a running prefix preserves their order by associativity of byte concatenation.
  induction parts generalizing front with
  | nil => simp [concatParts]
  | cons part rest ih => simp [concatParts, ih, Array.append_assoc]

/-- Packed fixed-width element streams preserve same-length value sequences. -/
theorem packElements_injective {shape : Desc} {width : Nat}
    {left right : List Value} {leftParts rightParts : List Bytes}
    (sound : shape.wellFormed = .ok ()) (fixed : shape.fixedSize = some width)
    (counts : left.length = right.length)
    (leftFits : ∀ value ∈ left, Fits shape value)
    (rightFits : ∀ value ∈ right, Fits shape value)
    (leftWrote : serializeEach shape left = .ok leftParts)
    (rightWrote : serializeEach shape right = .ok rightParts)
    (packed : packElements leftParts = packElements rightParts) : left = right := by
  -- The fixed element width determines each encoded part's size on both sides.
  have leftWidths := serializeEach_widths shape left leftParts width fixed leftWrote
    (fun value member _ wrote => serialize_size_of_wellFormed sound (leftFits value member)
      fixed wrote)
  have rightWidths := serializeEach_widths shape right rightParts width fixed rightWrote
    (fun value member _ wrote => serialize_size_of_wellFormed sound (rightFits value member)
      fixed wrote)
  -- It suffices to recover the unpadded encoded stream before decoding its parts.
  apply serializeEach_concat_injective sound fixed counts leftFits rightFits leftWrote rightWrote
  -- Equal part counts and widths determine the byte length needed to remove node padding.
  -- Successful element encoding preserves the number of elements.
  apply packBytes_injective
  · rw [concatParts_size width leftParts leftWidths, concatParts_size width rightParts rightWidths,
      serializeEach_length shape left leftParts leftWrote,
      serializeEach_length shape right rightParts rightWrote, counts]
  · simpa [packElements, fold_parts_eq_concat] using packed

end EthLib.Consensus.Ssz
