module

public import EthLib.Serialization.Rlp.Encode
public import EthLib.Serialization.Proofs.Rlp.Item

/-!
# `Serialization.Proofs.Rlp.Encode`

The bound on a length in the RLP encoding.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-! ## The bound of a length

A length must be below `2^64`.

No test vector comes near it: no byte string that long fits in memory.

So the bound is proved instead.

Below it, the first byte of a long prefix fits in a byte.

From it on, the encoding fails. -/

/-- Below `2^64`, the first byte of a long prefix is at most `offset + 63`.

That is `0xbf` for a byte string, below every list, and `0xff` for a list, still a byte.

So the first byte of a prefix never wraps around 256. -/
theorem lengthPrefix_first_byte_le (kind : PayloadKind) (length : Nat) (h : length < 2 ^ 64) :
    kind.offset + 55 + (bigEndian length).size ≤ kind.offset + 63 := by
  -- `2^64 = 256^8`, so the length has at most 8 digits in base 256.
  have := bigEndian_size_le length 8 (by simpa using h)
  omega

/-- `lengthPrefix` refuses every length from `2^64` on, for a byte string or a list. -/
theorem lengthPrefix_too_long (kind : PayloadKind) (length : Nat) (h : 2 ^ 64 ≤ length) :
    lengthPrefix kind length = .error (.payloadTooLong length) := by
  -- `length` is below neither bound of `lengthPrefix`, 56 or `2^64`.
  have notShort : ¬ length < 56 := Nat.not_lt.mpr (Nat.le_trans (by decide) h)
  have notLong : ¬ length < 2 ^ 64 := Nat.not_lt.mpr h
  rw [lengthPrefix, ite_eq_right notShort, ite_eq_right notLong]

/-- `encode` refuses a byte string of `2^64` bytes or more. -/
theorem encode_bytes_too_long (data : ByteArray) (h : 2 ^ 64 ≤ data.size) :
    encode (.bytes data) = .error (.payloadTooLong data.size) := by
  -- More than one byte, so the byte string is not its own encoding and takes a prefix.
  have notOne : data.size ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) h)
  have notSingle : isSingleLowByte data = false := by simp [isSingleLowByte, notOne]
  rw [encode, encodeBytes, notSingle]
  -- The prefix fails, so the encoding fails with it.
  show (fun prefixBytes => prefixBytes ++ data) <$> lengthPrefix .bytes data.size = _
  rw [lengthPrefix_too_long .bytes data.size h]
  rfl

/-- `encode` refuses a list whose items encode to a payload of `2^64` bytes or more. -/
theorem encode_list_too_long (items : List Item) (payload : ByteArray)
    (hp : joinEncodings items = .ok payload) (h : 2 ^ 64 ≤ payload.size) :
    encode (.list items) = .error (.payloadTooLong payload.size) := by
  rw [encode, hp]
  -- The prefix of the payload fails, so the encoding fails with it.
  show (fun prefixBytes => prefixBytes ++ payload) <$> lengthPrefix .list payload.size = _
  rw [lengthPrefix_too_long .list payload.size h]
  rfl

end EthLib.Serialization.Rlp
