import EthLib.Serialization.Proofs.Ssz.Merkle.Tree
import EthLib.Serialization.Ssz.Codec.Root

/-! A byte array and its sequence of one-byte integer values have the same SSZ meaning. -/

namespace EthLib.Serialization.Ssz

/-- Re-express each byte as the value of a one-byte unsigned integer. -/
def byteValues (data : Bytes) : List Value :=
  data.toList.map fun byte => .uint byte.toNat

/-- Each byte encodes to itself when read as a one-byte integer. -/
theorem serializeEach_bytes (data : List UInt8) :
    serializeEach (.uint 1) (data.map fun byte => .uint byte.toNat) =
      .ok (data.map fun byte => #[byte]) := by
  -- Encoding proceeds one byte at a time and preserves both its value and its position.
  have bound (byte : UInt8) : byte.toNat < 256 := byte.toNat_lt
  induction data <;> simp_all [serializeEach, serialize, uintBytes, Nat.mod_eq_of_lt,
    Bind.bind, Except.bind, pure, Except.pure]

/-- Singleton fixed slots contribute one byte each, all in the fixed part. -/
private theorem byteSlots_width (data : List UInt8) :
    headWidth (data.map fun byte => (true, #[byte])) = data.length ∧
      bodyWidth (data.map fun byte => (true, #[byte])) = 0 := by
  -- There are no offsets or trailing bodies for fixed-width elements.
  induction data <;> simp_all [headWidth, bodyWidth, Nat.add_comm]

/-- Singleton fixed slots concatenate to the original byte sequence. -/
private theorem byteSlots_content (data : List UInt8) (start : Nat) :
    headOf start (data.map fun byte => (true, #[byte])) = data.toArray ∧
      bodiesOf (data.map fun byte => (true, #[byte])) = #[] := by
  -- Each slot appends one original byte without changing it.
  induction data <;> simp_all [headOf, bodiesOf]

/-- Byte sequences use no offsets, so they encode to their input or meet the size bound. -/
theorem serializeSequence_bytes (data : Bytes) :
    serializeSequence (.uint 1) (byteValues data) =
      if data.size ≥ 2 ^ (8 * bytesPerOffset) then .error (.offsetOverflow data.size)
      else .ok data := by
  -- Treat each original byte as one fixed-width integer payload.
  unfold serializeSequence byteValues
  rw [serializeEach_bytes]
  simp only [Bind.bind, Except.bind, Desc.isFixed, Desc.fixedSize, Option.isSome_some]
  -- The sequence contains exactly one inline slot for each byte.
  have slots : ((data.toList.map fun byte => #[byte]).map fun _ => true).zip
      (data.toList.map fun byte => #[byte]) = data.toList.map fun byte => (true, #[byte]) := by
    induction data.toList <;> simp_all
  simp only [assemble, slots]
  rw [(byteSlots_width _).1, (byteSlots_width _).2]
  simp only [Array.length_toList, Nat.add_zero]
  -- The bound counts every byte, though no offset is ever written.
  split <;> simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure, *, (byteSlots_content _ _).1, (byteSlots_content data.toList 0).2]

/-- Re-expressing bytes preserves the number of sequence elements. -/
@[simp] theorem byteValues_length (data : Bytes) : (byteValues data).length = data.size := by
  simp [byteValues]

/-- Both fixed-byte spellings serialize alike, every refusal included. -/
theorem serialize_byteVector_alias (data : Bytes) (length : Nat) :
    serialize (.byteVector length) (.bytes data) =
      serialize (.vector (.uint 1) length) (.seq (byteValues data)) := by
  -- The count is checked first on both paths, then the same size bound.
  by_cases counted : data.size = length <;>
    simp [serialize, counted, serializeSequence_bytes, Bind.bind, Except.bind, pure,
      Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- Both bounded-byte spellings serialize alike, every refusal included. -/
theorem serialize_byteList_alias (data : Bytes) (limit : Nat) :
    serialize (.byteList limit) (.bytes data) =
      serialize (.list (.uint 1) limit) (.seq (byteValues data)) := by
  -- The limit is checked first on both paths, then the same size bound.
  by_cases within : data.size ≤ limit <;>
    simp [serialize, within, Nat.not_lt.mpr, serializeSequence_bytes, Bind.bind, Except.bind,
      pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- One-byte slices decode to the integers their bytes hold. -/
private theorem deserializeEach_bytes :
    ∀ (slices : List Bytes), (∀ slice ∈ slices, slice.size = 1) →
      deserializeEach (.uint 1) slices = .ok (slices.map fun slice => .uint (slice[0]!).toNat)
  | [], _ => by simp [deserializeEach]
  | slice :: rest, single => by
    -- Each slice passes the width check and reads back as its only byte.
    have tail := deserializeEach_bytes rest fun other member =>
      single other (List.mem_cons_of_mem _ member)
    simp [deserializeEach, deserialize, single slice List.mem_cons_self, readUint, tail,
      Bind.bind, Except.bind, pure, Except.pure]

/-- Cutting bytes into one-byte slices and decoding each gives the integer spelling. -/
private theorem deserializeEach_byteSlices (data : Bytes) :
    deserializeEach (.uint 1) ((List.range data.size).map fun i => data.extract i (i + 1)) =
      .ok (byteValues data) := by
  rw [deserializeEach_bytes _ (by simp; omega)]
  congr 1
  -- The slice at each position holds exactly the byte at that position.
  apply List.ext_getElem
  · simp [byteValues]
  · intro i inside _
    simp only [List.length_map, List.length_range] at inside
    simp only [List.getElem_map, List.getElem_range, byteValues, Array.getElem_toList]
    rw [getElem!_pos _ 0 (by simp; omega)]
    simp

/-- Both fixed-byte spellings decode the same input alike, every refusal included. -/
theorem deserialize_byteVector_alias (data : Bytes) (length : Nat) :
    deserialize (.vector (.uint 1) length) data =
      (deserialize (.byteVector length) data).map fun _ => .seq (byteValues data) := by
  simp only [deserialize, vectorSlices, Desc.fixedSize]
  -- The size bound is checked first on both paths, then the same byte count.
  by_cases large : data.size ≥ 2 ^ (8 * bytesPerOffset)
  · simp [large, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Except.map]
  by_cases counted : data.size = length
  · subst counted
    simp [large, deserializeEach_byteSlices, Bind.bind, Except.bind, Except.map, pure,
      Except.pure]
  · simp [large, counted, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
      Except.map]

/-- Both bounded-byte spellings decode the same input alike, every refusal included. -/
theorem deserialize_byteList_alias (data : Bytes) (limit : Nat) :
    deserialize (.list (.uint 1) limit) data =
      (deserialize (.byteList limit) data).map fun _ => .seq (byteValues data) := by
  simp only [deserialize, listSlices, Desc.fixedSize]
  -- The size bound is checked first on both paths, then the same limit.
  by_cases large : data.size ≥ 2 ^ (8 * bytesPerOffset)
  · simp [large, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Except.map]
  -- An empty input is an empty list on one path and empty bytes on the other.
  by_cases empty : data = #[]
  · subst empty
    simp [deserializeEach, byteValues, Bind.bind, Except.bind, Except.map, pure, Except.pure]
  -- Otherwise each byte is one element, so the element count is the byte count.
  have filled : data.size ≠ 0 := fun zero => empty (Array.eq_empty_of_size_eq_zero zero)
  by_cases within : data.size ≤ limit
  · simp [large, filled, Nat.mod_one, Nat.not_lt.mpr within, deserializeEach_byteSlices,
      Bind.bind, Except.bind, Except.map, pure, Except.pure]
  · simp [large, filled, Nat.mod_one, Nat.lt_of_not_le within, throw, throwThe,
      MonadExceptOf.throw, Bind.bind, Except.bind, Except.map]

/-- Appending one-byte encodings reconstructs the original bytes after any prefix. -/
private theorem fold_byteParts (data : List UInt8) (front : Bytes) :
    (data.map fun byte => #[byte]).foldl (fun total part => total ++ part) front =
      front ++ data.toArray := by
  -- Generalizing the prefix lets each induction step append the next original byte.
  induction data generalizing front <;> simp_all

/-- Packing one-byte integer encodings gives the same nodes as packing the byte array. -/
theorem packElements_bytes (data : Bytes) :
    packElements (data.toList.map fun byte => #[byte]) = packBytes data := by
  -- Concatenating the one-byte integer encodings recovers the original byte array before chunking.
  simp [packElements, fold_byteParts]

/-- A fixed byte array and a vector of bytes lay down the same tree, or refuse alike. -/
theorem merkleLayout_byteVector_alias (data : Bytes) (length : Nat) :
    merkleLayout (.byteVector length) (.bytes data) =
      merkleLayout (.vector (.uint 1) length) (.seq (byteValues data)) := by
  -- The byte count determines the same rounded-up node capacity on both paths.
  by_cases counted : data.size = length <;>
    simp [merkleLayout, counted, sequenceLayout, Desc.isBasic, Desc.itemLength, byteValues,
      serializeEach_bytes, packElements_bytes, chunksForBytes, packBytes_size, Bind.bind,
      Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- A bounded byte array and a list of bytes lay down the same nodes and length commitment. -/
theorem merkleLayout_byteList_alias (data : Bytes) (limit : Nat) :
    merkleLayout (.byteList limit) (.bytes data) =
      merkleLayout (.list (.uint 1) limit) (.seq (byteValues data)) := by
  -- Both the element count and the capacity count bytes, so even limit failures coincide.
  simp [merkleLayout, sequenceLayout, Desc.isBasic, Desc.itemLength,
    byteValues, serializeEach_bytes, packElements_bytes, Bind.bind, Except.bind, pure, Except.pure]

/-- Fixed byte arrays and byte vectors have identical Merkle roots, or refuse alike. -/
theorem hashTreeRoot_byteVector_alias (data : Bytes) (length : Nat) :
    hashTreeRoot (.byteVector length) (.bytes data) =
      hashTreeRoot (.vector (.uint 1) length) (.seq (byteValues data)) := by
  -- Packed leaves consume no recursive rooting budget, so the two type depths are immaterial.
  by_cases counted : data.size = length <;>
    simp [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, counted, sequenceLayout,
      Desc.isBasic, Desc.itemLength, byteValues, serializeEach_bytes, packElements_bytes,
      chunksForBytes, packBytes_size, layoutChunksAt, MerkleLayout.packing, Leaves.count,
      Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- Bounded byte arrays and byte lists have identical roots and identical limit failures. -/
theorem hashTreeRoot_byteList_alias (data : Bytes) (limit : Nat) :
    hashTreeRoot (.byteList limit) (.bytes data) =
      hashTreeRoot (.list (.uint 1) limit) (.seq (byteValues data)) := by
  -- Both paths pack the same bytes and mix in the same element count.
  by_cases over : limit < data.size <;>
    simp [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, over, sequenceLayout,
      Desc.isBasic, Desc.itemLength, byteValues, serializeEach_bytes, packElements_bytes,
      layoutChunksAt, MerkleLayout.packing, Leaves.count, Bind.bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw]

end EthLib.Serialization.Ssz
