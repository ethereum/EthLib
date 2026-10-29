import EthLib.Consensus.Proofs.Ssz.Codec.Canonical

/-! Delimited bit encodings preserve every byte when decoded and re-encoded. -/

namespace EthLib.Consensus.Ssz

private theorem highestBit_spec (byte : UInt8) (nonzero : byte ≠ 0) :
    highestBit byte < 8 ∧
    ((byte >>> UInt8.ofNat (highestBit byte)) &&& 1 == 1) = true ∧
    ∀ offset : Fin 8, highestBit byte < offset.val →
      ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1) = false := by
  -- For a nonzero byte the highest set bit exists and all higher bits are clear.
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte =>
      revert byte
      decide +kernel

private theorem unpackBits_push {data : Bytes} {count : Nat}
    (closing : ((data[count / 8]! >>> UInt8.ofNat (count % 8)) &&& 1 == 1) = true) :
    (unpackBits data count).push true = unpackBits data (count + 1) := by
  -- Appending the delimiter increases the recovered prefix by exactly one bit.
  apply Array.ext
  · simp
  · intro position left right
    -- Earlier positions keep their data bit.
    -- The final position is the closing bit.
    by_cases before : position < count
    · simp [Array.getElem_push, unpackBits, before]
    · obtain rfl : position = count := by simp at right; omega
      simpa [unpackBits, Array.getElem_push] using closing.symm

/-- Re-encoding a successfully decoded delimited bit sequence reproduces its input. -/
theorem packBitsDelimited_unpackDelimited {limit : Option Nat} {data : Bytes}
    {bits : Array Bool} (read : unpackDelimited limit data = .ok bits) :
    packBitsDelimited bits = data := by
  -- A delimited bit sequence needs at least one byte to hold its closing one bit.
  have nonempty : data.size ≠ 0 := by
    intro empty
    simp [unpackDelimited, empty, throw_error, Bind.bind, Except.bind] at read
  -- The final byte cannot be zero because its highest set bit marks the end of the sequence.
  have nonzero : data[data.size - 1]! ≠ 0 := by
    intro zero
    simp [unpackDelimited, nonempty, zero, throw_error, Bind.bind, Except.bind] at read
    split at read <;> cases read
  -- Each earlier byte contributes eight data bits, followed by the data below the closing bit.
  let count := 8 * (data.size - 1) + highestBit data[data.size - 1]!
  -- Successful decoding keeps precisely that data prefix, regardless of a capacity limit.
  have decoded : bits = unpackBits data count := by
    cases limit <;> simp [unpackDelimited, nonempty, nonzero, throw_error, Bind.bind, Except.bind,
      pure, Except.pure] at read <;> (try split at read) <;> simp_all [count]
  -- The highest set bit supplies both the delimiter and the clear padding above it.
  obtain ⟨small, set, high⟩ := highestBit_spec _ nonzero
  -- Locate the delimiter in the final byte and recover its position within that byte.
  have quotient : count / 8 = data.size - 1 := by dsimp [count]; omega
  have remainder : count % 8 = highestBit data[data.size - 1]! := by dsimp [count]; omega
  have closing : ((data[count / 8]! >>> UInt8.ofNat (count % 8)) &&& 1 == 1) = true := by
    simpa only [quotient, remainder] using set
  -- Reattaching the delimiter restores exactly the original byte count.
  have width : (count + 8) / 8 = data.size := by dsimp [count]; omega
  have padding : ∀ index, index < data.size → ∀ offset, offset < 8 →
      count + 1 ≤ index * 8 + offset →
      ((data[index]! >>> UInt8.ofNat offset) &&& 1 == 1) = false := by
    intro index inside offset below past
    -- Any bit beyond the delimiter must lie in the high padding of the final byte.
    have last : index = data.size - 1 := by dsimp [count] at past; omega
    subst index
    apply high ⟨offset, below⟩
    change highestBit data[data.size - 1]! < offset
    dsimp [count] at past
    omega
  -- Appending the closing bit restores exactly the retained prefix of the input bits.
  rw [decoded, packBitsDelimited, unpackBits_size, unpackBits_push closing, width]
  exact packBits_unpackBits padding

/-- Bounded bit lists have a unique accepted delimited encoding. -/
theorem canonical_bitList {limit : Nat} {data : Bytes} {value : Value}
    (read : deserialize (.bitList limit) data = .ok value) :
    serialize (.bitList limit) value = .ok data := by
  -- Successful decoding must have recovered a delimited bit sequence.
  cases decoded : unpackDelimited (some limit) data <;>
    simp [deserialize, decoded, Bind.bind, Except.bind, pure, Except.pure] at read
  -- Re-encode the recovered data bits with the same closing bit and padding.
  subst value
  simp [serialize, unpackDelimited_bound decoded, packBitsDelimited_unpackDelimited decoded]

/-- Progressive bit lists have the same canonical delimiter rule under their own bound. -/
theorem canonical_progressiveBitList {limit : Option Nat} {data : Bytes} {value : Value}
    (read : deserialize (.progressiveBitList limit) data = .ok value) :
    serialize (.progressiveBitList limit) value = .ok data := by
  -- Successful decoding must have recovered a delimited bit sequence.
  cases decoded : unpackDelimited limit data <;>
    simp [deserialize, decoded, Bind.bind, Except.bind, pure, Except.pure] at read
  -- Re-encode the recovered data bits with the same closing bit and padding.
  subst value
  simp [serialize, boundCheck_of_withinBound limit _ (unpackDelimited_within decoded),
    Bind.bind, Except.bind, Pure.pure, Except.pure, packBitsDelimited_unpackDelimited decoded]

end EthLib.Consensus.Ssz
