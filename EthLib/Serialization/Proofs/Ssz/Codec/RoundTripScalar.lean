import EthLib.Serialization.Proofs.Ssz.Codec.Table
import EthLib.Serialization.Proofs.Ssz.Codec.Admits

/-! Packing and round trips for scalar values and bitfields. -/

namespace EthLib.Serialization.Ssz

/--
Every bit reads back where it was put, and no other bit of the byte disturbs it.

One byte holds eight bits and an offset names one of them, so what is left once the offset is fixed is a finite check.
-/
theorem packByte_bit (bits : Array Bool) (byteIndex offset : Nat) (small : offset < 8) :
    ((packByte bits byteIndex >>> UInt8.ofNat offset) &&& 1 == 1)
      = bits[byteIndex * 8 + offset]?.getD false := by
  -- The offset is one of eight, so it is made concrete before anything is named.
  match offset, small with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [packByte]
    -- The eight bits of this byte are arbitrary, so they are named and the rest decided.
    generalize bits[byteIndex * 8 + 0]?.getD false = b0
    generalize bits[byteIndex * 8 + 1]?.getD false = b1
    generalize bits[byteIndex * 8 + 2]?.getD false = b2
    generalize bits[byteIndex * 8 + 3]?.getD false = b3
    generalize bits[byteIndex * 8 + 4]?.getD false = b4
    generalize bits[byteIndex * 8 + 5]?.getD false = b5
    generalize bits[byteIndex * 8 + 6]?.getD false = b6
    generalize bits[byteIndex * 8 + 7]?.getD false = b7
    revert b0 b1 b2 b3 b4 b5 b6 b7
    decide

private theorem byte_testBit (byte : UInt8) (offset : Nat) (small : offset < 8) :
    ((byte >>> UInt8.ofNat offset) &&& 1 == 1) = byte.toNat.testBit offset := by
  -- A one-bit mask reads the same bit as the natural-number bit test.
  have bound : offset < UInt8.size := by change offset < 256; omega
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, ← UInt8.toNat_inj, UInt8.toNat_and, UInt8.toNat_shiftRight,
    UInt8.toNat_ofNat_of_lt' bound, Nat.mod_eq_of_lt small, UInt8.toNat_one,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_eq]

/-- Shifting past the supplied bits leaves zero, so unused high bits are canonical. -/
theorem packByte_high_clear (bits : Array Bool) (byteIndex offset : Nat)
    (small : offset < 8) (past : bits.size ≤ byteIndex * 8 + offset) :
    packByte bits byteIndex >>> UInt8.ofNat offset = 0 := by
  -- The byte shift is exact because its offset lies below the machine-word width.
  have offsetBound : offset < UInt8.size := by change offset < 256; omega
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_shiftRight, UInt8.toNat_ofNat_of_lt' offsetBound,
    Nat.mod_eq_of_lt small, UInt8.toNat_zero]
  -- Extensional equality compares every bit of the shifted byte with zero.
  apply Nat.eq_of_testBit_eq
  intro position
  rw [Nat.testBit_shiftRight, Nat.zero_testBit]
  by_cases within : offset + position < 8
  · -- Within the byte, every remaining position lies beyond the supplied bits.
    rw [← byte_testBit _ _ within, packByte_bit _ _ _ within, Array.getElem?_eq_none (by omega)]
    rfl
  · -- Above bit seven, any eight-bit value is already zero.
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (packByte bits byteIndex).toNat_lt
      (Nat.pow_le_pow_right (by decide) (by omega)))

/--
Bits packed into enough bytes are the bits that come back out.

The room is what the caller must supply: a bit past the last byte has nowhere to land.
-/
theorem unpackBits_packBits (bits : Array Bool) (byteCount : Nat)
    (room : bits.size ≤ 8 * byteCount) :
    unpackBits (packBits bits byteCount) bits.size = bits := by
  -- Compare the recovered bit count and then each bit at its original position.
  apply Array.ext
  · simp [unpackBits]
  · intro position inRead inBits
    simp only [unpackBits, Array.getElem_map, Array.getElem_range]
    -- The byte this bit lands in is one the packing wrote.
    have inBytes : position / 8 < byteCount := by omega
    have byteIs : (packBits bits byteCount)[position / 8]! = packByte bits (position / 8) := by
      simp [packBits, getElem!_pos, inBytes]
    rw [byteIs, packByte_bit bits (position / 8) (position % 8) (by omega)]
    -- The byte and the offset within it name the position they came from.
    have index : position / 8 * 8 + position % 8 = position := by omega
    rw [index, Array.getElem?_eq_getElem inBits, Option.getD_some]

/-- A boolean survives being written and read back. -/
theorem roundTrip_bool (b : Bool) :
    serialize .bool (.bool b) >>= deserialize .bool = .ok (.bool b) := by
  -- Two values, two encodings, and each is checked by computing the decode of one byte.
  cases b <;> simp [serialize, deserialize, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- An integer of a width its value fits survives being written and read back. -/
theorem roundTrip_uint {width value : Nat} (bound : value < 2 ^ (8 * width)) :
    serialize (.uint width) (.uint value) >>= deserialize (.uint width)
      = .ok (.uint value) := by
  -- The value fits its width, so the encoder writes rather than refusing.
  simp only [serialize, ite_eq_left bound]
  show deserialize (.uint width) (uintBytes width value) = _
  -- The decoder's width check passes because the encoding is exactly that wide.
  simp [deserialize, uintBytes_size, readUint_uintBytes width value bound, Pure.pure, Except.pure]

/--
A fixed-width byte string survives being written and read back.

The encoder may refuse one too long for an offset to name, leaving nothing to read.
-/
theorem roundTrip_byteVector {length : Nat} {data : Bytes} (fits : data.size = length) :
    ∀ bytes, serialize (.byteVector length) (.bytes data) = .ok bytes →
      deserialize (.byteVector length) bytes = .ok (.bytes data) := by
  intro bytes wrote
  subst fits
  -- A byte string is its own encoding, so both sides check the same count and size.
  by_cases large : data.size ≥ 2 ^ (8 * bytesPerOffset) <;>
    simp [serialize, large, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at wrote
  subst wrote
  simp [deserialize, large, Pure.pure, Except.pure]

/--
The highest set bit is the one nothing above it disturbs.

The delimiter is found this way, so this is what recovers a bit count from a byte count.
-/
theorem highestBit_eq (byte : UInt8) (offset : Nat) (small : offset < 8)
    (isSet : (byte >>> UInt8.ofNat offset) &&& 1 = 1)
    (above : ∀ j, offset < j → j < 8 → (byte >>> UInt8.ofNat j) &&& 1 ≠ 1) :
    highestBit byte = offset := by
  -- The answer is one of eight, and each is settled by what lies above it.
  match offset, small with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp (disch := omega) only [highestBit, beq_iff_eq, isSet, above, ↓reduceIte]

/--
The bits before a closing one are the bits that were packed.

This is the delimited encoding read back: the closing bit is one more bit, so the positions below it are the data.
-/
theorem unpackBits_packBits_push (bits : Array Bool) (byteCount : Nat)
    (room : bits.size + 1 ≤ 8 * byteCount) :
    unpackBits (packBits (bits.push true) byteCount) bits.size = bits := by
  -- Compare only the data prefix, excluding the appended closing bit.
  apply Array.ext
  · simp [unpackBits]
  · intro position inRead inBits
    simp only [unpackBits, Array.getElem_map, Array.getElem_range]
    -- The room assumption includes the delimiter, so every earlier data bit lies in an allocated byte.
    have inBytes : position / 8 < byteCount := by omega
    have byteIs : (packBits (bits.push true) byteCount)[position / 8]!
        = packByte (bits.push true) (position / 8) := by
      simp [packBits, getElem!_pos, inBytes]
    rw [byteIs, packByte_bit _ (position / 8) (position % 8) (by omega)]
    -- The byte and the offset within it name the position they came from.
    have index : position / 8 * 8 + position % 8 = position := by omega
    -- The position is inside the data, so the closing bit is not the one read.
    rw [index, Array.getElem?_eq_getElem (by simp; omega), Option.getD_some,
      Array.getElem_push_lt inBits]

/--
A delimited encoding gives back exactly the bits it was made from.

Both bit lists encode this way and differ only in the capacity they check, so the whole recovery is stated once here.
-/
theorem unpackDelimited_packBitsDelimited (limit : Option Nat) (data : Array Bool)
    (within : ∀ cap, limit = some cap → data.size ≤ cap) :
    unpackDelimited limit (packBitsDelimited data) = .ok data := by
  -- Everything below is about the packing itself, so the delimiter is put in first.
  show unpackDelimited limit (packBits (data.push true) ((data.size + 8) / 8)) = .ok data
  have widthIs : (packBits (data.push true) ((data.size + 8) / 8)).size
      = (data.size + 8) / 8 := by simp [packBits]
  -- The last byte is the one the closing bit landed in.
  have finalIs : (packBits (data.push true) ((data.size + 8) / 8))[data.size / 8]!
      = packByte (data.push true) (data.size / 8) := by
    simp [packBits, getElem!_pos]
  -- The closing bit is set, one position past the last of the data.
  have isSet : (packByte (data.push true) (data.size / 8) >>> UInt8.ofNat (data.size % 8))
      &&& 1 = 1 := by
    have found := packByte_bit (data.push true) (data.size / 8) (data.size % 8) (by omega)
    rw [show data.size / 8 * 8 + data.size % 8 = data.size by omega] at found
    simp only [Array.getElem?_eq_getElem (show data.size < (data.push true).size by simp),
      Option.getD_some, Array.getElem_push_eq] at found
    simpa using found
  -- Nothing above it is set, every position there lying past the closing bit.
  have above : ∀ j, data.size % 8 < j → j < 8 →
      (packByte (data.push true) (data.size / 8) >>> UInt8.ofNat j) &&& 1 ≠ 1 := by
    intro j over small
    have clear := packByte_bit (data.push true) (data.size / 8) j small
    rw [Array.getElem?_eq_none (by simp; omega)] at clear
    simpa using clear
  -- A byte with a bit set is not the zero byte.
  have notZero : ¬ (packByte (data.push true) (data.size / 8) = 0) := by
    intro zero; simp [zero] at isSet
  -- The number of complete earlier bytes plus the delimiter position recovers the exact data-bit count.
  have counted : 8 * ((data.size + 8) / 8 - 1)
      + highestBit (packBits (data.push true) ((data.size + 8) / 8))[data.size / 8]!
      = data.size := by
    rw [finalIs, highestBit_eq _ (data.size % 8) (by omega) isSet above]
    omega
  -- Reading that many bits excludes the delimiter and restores the original data.
  have recovered : unpackBits (packBits (data.push true) ((data.size + 8) / 8)) data.size
      = data := unpackBits_packBits_push data _ (by omega)
  simp only [unpackDelimited, widthIs, beq_iff_eq,
    show ¬ (data.size + 8) / 8 = 0 by omega, ite_eq_right, not_false_eq_true,
    show (data.size + 8) / 8 - 1 = data.size / 8 by omega, finalIs, ite_eq_right notZero]
  rw [show (data.size + 8) / 8 - 1 = data.size / 8 by omega, finalIs] at counted
  -- The declared capacity, where there is one, holds the count that came back.
  cases limit with
  | none => simp only [counted, recovered, Pure.pure, Except.pure]
  | some cap =>
    simp only [counted, recovered, Pure.pure, Except.pure,
      ite_eq_right (show ¬ data.size > cap by have := within cap rfl; omega)]

/-- A fixed bit sequence survives being written and read back. -/
theorem roundTrip_bitVector {length : Nat} {data : Array Bool} (fits : data.size = length) :
    serialize (.bitVector length) (.bits data) >>= deserialize (.bitVector length)
      = .ok (.bits data) := by
  -- The count is the declared one, so the encoder writes rather than refusing.
  simp only [serialize, fits, beq_self_eq_true, ite_eq_left]
  show deserialize (.bitVector length) (packBits data ((length + 7) / 8)) = _
  -- The encoding is exactly as many bytes as the declared count needs.
  have width : (packBits data ((length + 7) / 8)).size = (length + 7) / 8 := by simp [packBits]
  simp only [deserialize, width, bne_self_eq_false, ite_eq_right, Bool.false_eq_true, not_false_eq_true]
  -- Nothing is set above the last declared bit, so the padding check passes.
  have padded : ∀ h : length % 8 != 0 ∧ (length + 7) / 8 > 0,
      (packBits data ((length + 7) / 8))[(length + 7) / 8 - 1]! >>> UInt8.ofNat (length % 8)
        = 0 := by
    intro ⟨odd, room⟩
    have inBytes : (length + 7) / 8 - 1 < (length + 7) / 8 := by omega
    have byteIs : (packBits data ((length + 7) / 8))[(length + 7) / 8 - 1]!
        = packByte data ((length + 7) / 8 - 1) := by simp [packBits, getElem!_pos, inBytes]
    rw [byteIs]
    refine packByte_high_clear data _ _ (by omega) ?_
    -- The last byte starts a whole number of bytes in, and the data ends inside it.
    simp only [bne_iff_ne, ne_eq] at odd
    omega
  -- The bits come back because the bytes hold every one of them.
  have unpacked : unpackBits (packBits data ((length + 7) / 8)) length = data := by
    subst fits; exact unpackBits_packBits data _ (by omega)
  -- Either the count fills its last byte, or the padding check runs and passes.
  split
  · rename_i checked
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    rw [ite_eq_right (by simp [padded checked])]
    simp [unpacked, Pure.pure, Except.pure]
  · simp [unpacked, Pure.pure, Except.pure]

/-- A bounded bit sequence survives being written and read back. -/
theorem roundTrip_bitList {limit : Nat} {data : Array Bool} (fits : data.size ≤ limit) :
    serialize (.bitList limit) (.bits data) >>= deserialize (.bitList limit)
      = .ok (.bits data) := by
  -- The count is under the capacity, so neither side refuses it.
  simp only [serialize, ite_eq_left fits]
  show deserialize (.bitList limit) (packBitsDelimited data) = _
  simp only [deserialize,
    unpackDelimited_packBitsDelimited (some limit) data (fun _ named => by cases named; exact fits)]
  rfl

/-- A progressive bit sequence its capacity admits survives being written and read back. -/
theorem roundTrip_progressiveBitList {limit : Option Nat} {data : Array Bool}
    (within : withinBound limit data.size = true) :
    serialize (.progressiveBitList limit) (.bits data)
        >>= deserialize (.progressiveBitList limit)
      = .ok (.bits data) := by
  simp only [serialize, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  show deserialize (.progressiveBitList limit) (packBitsDelimited data) = _
  simp only [deserialize,
    unpackDelimited_packBitsDelimited limit data (fun bound named => by
      subst named
      simpa [withinBound] using within)]
  rfl

/--
A bounded byte string survives being written and read back.

The encoder may refuse one too long for an offset to name, leaving nothing to read.
-/
theorem roundTrip_byteList {limit : Nat} {data : Bytes} (fits : data.size ≤ limit) :
    ∀ bytes, serialize (.byteList limit) (.bytes data) = .ok bytes →
      deserialize (.byteList limit) bytes = .ok (.bytes data) := by
  intro bytes wrote
  -- The count is under the capacity, so only the size bound could refuse it.
  by_cases large : data.size ≥ 2 ^ (8 * bytesPerOffset) <;>
    simp [serialize, Nat.not_lt.mpr fits, large, throw, throwThe, MonadExceptOf.throw,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
  subst wrote
  simp [deserialize, Nat.not_lt.mpr fits, large, Pure.pure, Except.pure]

end EthLib.Serialization.Ssz
