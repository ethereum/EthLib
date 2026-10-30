import EthLib.Serialization.Rlp.Decode

/-!
# `Serialization.Proofs.Rlp.Strict`

The decoder rejects every non-canonical form, whatever bytes follow it.

Each theorem is stated on the front of an input, and `decode_eq_error` lifts it to a whole input.

These are the five quasi-encodings of Coglio, [Ethereum's Recursive Length Prefix in ACL2](https://doi.org/10.4204/EPTCS.327.11), §4.2.1.

Each one could be read as an item, but the encoding writes that item with fewer bytes:

- `81 x`, with `x < 0x80`, for the byte string `[x]`, which encodes as `x`;
- `b7 + k`, then a length with a leading zero byte, for a byte string;
- `b8 l`, with `0 < l < 56`, for a byte string of `l` bytes, which encodes as `80 + l`;
- `f7 + k`, then a length with a leading zero byte, for a list;
- `f8 l`, with `0 < l < 56`, for a list payload of `l` bytes, which encodes as `c0 + l`.
-/

namespace EthLib.Serialization.Rlp

/-- A whole input whose first item fails fails with the same error. -/
theorem decode_eq_error (input : ByteArray) (e : RlpError) (h : decodeItem input.data.toList = .error e) :
    decode input = .error e := by
  simp [decode, h, bind, Except.bind]

/-- `81 x`, with `x < 0x80`: the byte `x` written with a prefix. -/
theorem decodeItem_singleByteWithPrefix (x : UInt8) (hx : x < 0x80) (rest : List UInt8) :
    decodeItem (0x81 :: x :: rest) = .error (.singleByteWithPrefix x) := by
  rw [decodeItem.eq_def]
  simp [readPrefix, hx, bind, Except.bind]

/-- `b7 + k`, then `k` length bytes of which the first is zero, for `1 <= k <= 8`. -/
theorem decodeItem_leadingZero_bytes (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (lengthTail rest : List UInt8)
    (hLen : lengthTail.length + 1 = k) :
    decodeItem (UInt8.ofNat (0xb7 + k) :: (0 :: lengthTail) ++ rest) = .error .leadingZeroInLength := by
  subst hLen
  have hMod : (0xb7 + (lengthTail.length + 1)) % 256 = 0xb7 + (lengthTail.length + 1) :=
    Nat.mod_eq_of_lt (by omega)
  rw [decodeItem.eq_def]
  simp [readPrefix, readPrefix.readLongLength, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', hMod,
    show ¬ 0xb7 + (lengthTail.length + 1) < 0x80 by omega,
    show ¬ 0xb7 + (lengthTail.length + 1) < 0xb8 by omega,
    show 0xb7 + (lengthTail.length + 1) < 0xc0 by omega,
    show ¬ lengthTail.length + rest.length < lengthTail.length by omega,
    bind, Except.bind]

/-- `f7 + k`, then `k` length bytes of which the first is zero, for `1 <= k <= 8`. -/
theorem decodeItem_leadingZero_list (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (lengthTail rest : List UInt8)
    (hLen : lengthTail.length + 1 = k) :
    decodeItem (UInt8.ofNat (0xf7 + k) :: (0 :: lengthTail) ++ rest) = .error .leadingZeroInLength := by
  subst hLen
  have hMod : (0xf7 + (lengthTail.length + 1)) % 256 = 0xf7 + (lengthTail.length + 1) :=
    Nat.mod_eq_of_lt (by omega)
  rw [decodeItem.eq_def]
  simp [readPrefix, readPrefix.readLongLength, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', hMod,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0x80 by omega,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0xb8 by omega,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0xc0 by omega,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0xf8 by omega,
    show ¬ lengthTail.length + rest.length < lengthTail.length by omega,
    bind, Except.bind]

/-- `b8 l`, with `0 < l < 56`: a short byte-string length in the long form. -/
theorem decodeItem_longFormForShortLength_bytes (l : UInt8) (h0 : 0 < l) (h56 : l < 56) (rest : List UInt8) :
    decodeItem (0xb8 :: l :: rest) = .error (.longFormForShortLength l.toNat) := by
  rw [decodeItem.eq_def]
  simp only [UInt8.lt_iff_toNat_lt] at h0 h56
  simp [readPrefix, readPrefix.readLongLength, ofBigEndian, UInt8.lt_iff_toNat_lt, bind, Except.bind,
    show l ≠ 0 from fun h => by simp [h] at h0, show l.toNat < 56 from h56]

/-- `f8 l`, with `0 < l < 56`: a short list-payload length in the long form. -/
theorem decodeItem_longFormForShortLength_list (l : UInt8) (h0 : 0 < l) (h56 : l < 56) (rest : List UInt8) :
    decodeItem (0xf8 :: l :: rest) = .error (.longFormForShortLength l.toNat) := by
  rw [decodeItem.eq_def]
  simp only [UInt8.lt_iff_toNat_lt] at h0 h56
  simp [readPrefix, readPrefix.readLongLength, ofBigEndian, UInt8.lt_iff_toNat_lt, bind, Except.bind,
    show l ≠ 0 from fun h => by simp [h] at h0, show l.toNat < 56 from h56]

end EthLib.Serialization.Rlp
