import EthLib.Consensus.Proofs.Ssz.Codec.DecodeFits
import EthLib.Consensus.Proofs.Ssz.Codec.RoundTrip

/-! Accepted scalar encodings have a unique byte representation. -/

namespace EthLib.Consensus.Ssz

/-- Reading every byte as an integer and writing it at the same width preserves the bytes. -/
theorem uintBytes_readUint (data : Bytes) :
    uintBytes data.size (readUint data 0 data.size) = data := by
  -- Induct over the bytes in little-endian order.
  cases data with
  | mk bytes =>
    induction bytes with
    | nil => rfl
    | cons byte bytes ih =>
      -- The first byte is the low digit, and the rest starts one position later.
      have split : ({ toList := byte :: bytes } : Bytes) = #[byte] ++ ({ toList := bytes } : Bytes) := by simp
      rw [split]
      simp only [Array.size_append, Array.size_singleton]
      rw [Nat.add_comm 1, readUint]
      have first : (#[byte] ++ ({ toList := bytes } : Bytes))[0]?.getD 0 = byte := by simp
      have low := UInt8.toNat_lt byte
      rw [first, readUint_shift, uintBytes]
      -- Reduction modulo 256 recovers the low byte without interference from higher digits.
      have remainder : (byte.toNat + 256 * readUint ({ toList := bytes } : Bytes) 0 ({ toList := bytes } : Bytes).size) % 256 =
          byte.toNat := by omega
      -- Division by 256 removes that low byte and recovers the remaining integer.
      have quotient : (byte.toNat + 256 * readUint ({ toList := bytes } : Bytes) 0 ({ toList := bytes } : Bytes).size) / 256 =
          readUint ({ toList := bytes } : Bytes) 0 ({ toList := bytes } : Bytes).size := by omega
      -- Reattach the recovered low byte to the recursively recovered suffix.
      rw [remainder, quotient, ih]
      simp

/-- An accepted integer encoding is reproduced exactly, including its leading zero bytes. -/
theorem canonical_uint {width : Nat} {data : Bytes} {value : Value}
    (read : deserialize (.uint width) data = .ok value) :
    serialize (.uint width) value = .ok data := by
  -- The decoder fixes the width and reads all bytes as one little-endian integer.
  simp only [deserialize] at read
  split at read <;> simp [Bind.bind, Except.bind, pure, Except.pure] at read
  -- The accepted value is the recovered payload, whose encoding preserves the original bytes.
  subst value
  have sized : data.size = width := by simp_all
  simp [serialize, readUint_lt, ← sized, uintBytes_readUint]

/-- A fixed byte string is already its canonical representation. -/
theorem canonical_byteVector {length : Nat} {data : Bytes} {value : Value}
    (read : deserialize (.byteVector length) data = .ok value) :
    serialize (.byteVector length) value = .ok data := by
  -- Acceptance establishes the size bound and the exact declared byte count.
  -- The accepted value is the recovered payload, whose encoding preserves the original bytes.
  simp only [deserialize, throw_error, Bind.bind, Except.bind] at read
  repeat' split at read
  all_goals cases read
  simp_all [serialize, Bind.bind, Except.bind, pure, Except.pure]

/-- A bounded byte string is already its canonical representation. -/
theorem canonical_byteList {limit : Nat} {data : Bytes} {value : Value}
    (read : deserialize (.byteList limit) data = .ok value) :
    serialize (.byteList limit) value = .ok data := by
  -- Acceptance establishes the size bound and the byte capacity without changing the payload.
  -- The accepted value is the recovered payload, whose encoding preserves the original bytes.
  simp only [deserialize, throw_error, Bind.bind, Except.bind] at read
  repeat' split at read
  all_goals cases read
  simp only [serialize, Bind.bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

set_option maxRecDepth 4096 in
private theorem byte_bit (byte : UInt8) (offset : Fin 8) :
    ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1) = byte.toBitVec.getLsbD offset.val := by
  -- There are 256 bytes and eight positions, checked by the kernel.
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte =>
      revert byte offset
      decide

private theorem byte_eq_of_bits {left right : UInt8}
    (same : ∀ offset, offset < 8 →
      ((left >>> UInt8.ofNat offset) &&& 1 == 1) =
      ((right >>> UInt8.ofNat offset) &&& 1 == 1)) : left = right := by
  -- Two eight-bit words are equal when each of their eight bit positions agrees.
  apply UInt8.eq_iff_toBitVec_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro offset small
  -- Translate the byte-mask observations into the bitvector equality criterion.
  simpa only [byte_bit left ⟨offset, small⟩, byte_bit right ⟨offset, small⟩] using
    same offset small

/-- Repacking recovered bits preserves every byte when the discarded padding is zero. -/
theorem packBits_unpackBits {data : Bytes} {count : Nat}
    (padding : ∀ index, index < data.size → ∀ offset, offset < 8 →
      count ≤ index * 8 + offset →
      ((data[index]! >>> UInt8.ofNat offset) &&& 1 == 1) = false) :
    packBits (unpackBits data count) data.size = data := by
  -- Compare output length first, then compare every bit of every byte.
  apply Array.ext
  · simp [packBits]
  · intro index _ inside
    simp only [packBits, Array.getElem_ofFn]
    apply byte_eq_of_bits
    intro offset small
    rw [packByte_bit _ _ _ small]
    -- A position is either retained data or padding beyond the declared bit count.
    by_cases held : index * 8 + offset < count
    · -- A retained bit is read from exactly its original byte and position.
      have fits : index * 8 + offset < (unpackBits data count).size := by simpa using held
      rw [Array.getElem?_eq_getElem fits, Option.getD_some]
      simp only [unpackBits, Array.getElem_map, Array.getElem_range]
      have quotient : (index * 8 + offset) / 8 = index := by omega
      have remainder : (index * 8 + offset) % 8 = offset := by omega
      simp [quotient, remainder, getElem!_pos, inside]
    · -- A discarded bit is clear on both sides by the canonical padding rule.
      rw [Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt held)]
      simpa [getElem!_pos, inside] using (padding index inside offset small (by omega)).symm

private theorem byte_padding (byte : UInt8) (start offset : Fin 8)
    (clear : byte >>> UInt8.ofNat start.val = 0) (above : start.val ≤ offset.val) :
    ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1) = false := by
  -- Shifting away the low bits exposes every bit in the padding region.
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte =>
      revert byte start offset
      decide +kernel

/-- Fixed bitfields accept only the packed representation with zero high padding. -/
theorem canonical_bitVector {length : Nat} {data : Bytes} {value : Value}
    (read : deserialize (.bitVector length) data = .ok value) :
    serialize (.bitVector length) value = .ok data := by
  -- Acceptance forces the smallest byte count capable of holding the declared bits.
  have sized : data.size = (length + 7) / 8 := Decidable.byContradiction fun same => by
    simp [deserialize, same, Bind.bind, Except.bind] at read
  have padding : ∀ index, index < data.size → ∀ offset, offset < 8 →
      length ≤ index * 8 + offset →
      ((data[index]! >>> UInt8.ofNat offset) &&& 1 == 1) = false := by
    intro index inside offset small above
    -- Only the final byte can contain padding, and only after the last declared bit.
    have last : index = data.size - 1 := by omega
    have remainder : length % 8 ≠ 0 := by omega
    have lower : length % 8 ≤ offset := by omega
    -- A nonzero high padding region would have caused the decoder to reject the final byte.
    have clear : data[data.size - 1]! >>> UInt8.ofNat (length % 8) = 0 :=
      Decidable.byContradiction fun same => by
        rw [sized] at same
        simp [deserialize, sized, remainder, same, show 1 ≤ length by omega,
          throw_error, Bind.bind, Except.bind] at read
    subst index
    exact byte_padding _ ⟨length % 8, by omega⟩ ⟨offset, small⟩ clear lower
  -- The data bits and zero padding together determine every original byte.
  have canonical := packBits_unpackBits padding
  simp only [deserialize] at read
  -- Discard rejected decoder paths and apply that reconstruction to each successful path.
  repeat' split at read
  all_goals simp_all [Bind.bind, Except.bind, pure, Except.pure]
  all_goals
    subst value
    simp only [serialize, unpackBits_size, beq_self_eq_true, ite_eq_left]
    exact congrArg Except.ok (by simpa only [sized] using canonical)

/-- A boolean has exactly one accepted byte for each of its two values. -/
theorem canonical_bool {data : Bytes} {value : Value}
    (read : deserialize .bool data = .ok value) : serialize .bool value = .ok data := by
  -- A boolean consumes exactly one byte.
  have sized : data.size = 1 := Decidable.byContradiction fun same => by
    simp [deserialize, same, Bind.bind, Except.bind] at read
  -- Expose that sole byte so the two accepted boolean encodings can be checked directly.
  obtain ⟨byte, rfl⟩ := Array.size_eq_one_iff.mp sized
  simp [deserialize] at read
  -- Only zero and one can survive the decoder, and each re-encodes to itself.
  split at read
  all_goals simp_all [pure, Except.pure]
  all_goals subst value; simp [serialize]

end EthLib.Consensus.Ssz
