module

import EthLib.Base.Proofs.Bytes
public import EthLib.Serialization.Proofs.Rlp.Bytes

/-!
# `Serialization.Proofs.Rlp.Strict`

The decoder rejects every non-canonical form, whatever bytes follow it.

Each theorem is stated on the bytes the decoder reads, and a lemma lifts it to a whole input.

The theorems cover the five quasi-encodings in §4.2.1 of Coglio, [the RLP paper][coglio].

That paper is "Ethereum's Recursive Length Prefix in ACL2".

Each one could be read as an item, but the encoding writes that item with fewer bytes:

- `81 x`, with `x < 0x80`, for the byte string `[x]`, which encodes as `x`.
- `b7 + k`, then a length with a leading zero byte, for a byte string.
- `b8 l`, with `0 < l < 56`, for a byte string of `l` bytes, which encodes as `80 + l`.
- `f7 + k`, then a length with a leading zero byte, for a list.
- `f8 l`, with `0 < l < 56`, for a list payload of `l` bytes, which encodes as `c0 + l`.

[coglio]: https://doi.org/10.4204/EPTCS.327.11
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

open EthLib.Base (byteArray_getElem_eq_get!)

/-- A whole input whose first item fails fails with the same error. -/
theorem decode_eq_error (input : ByteArray) (e : RlpError)
    (h : decodeItem input 0 input.size = .error e) :
    decode input = .error e := by
  simp [decode, h, bind, Except.bind]

/-- `81 x`, with `x < 0x80`: the byte `x` written with a prefix. -/
theorem decodeItem_singleByteWithPrefix (x : UInt8) (hx : x < 0x80) {input : ByteArray}
    {pos stop : Nat} {rest : List UInt8} (hStop : stop ≤ input.size)
    (h : (input.extract pos stop).data.toList = 0x81 :: x :: rest) :
    decodeItem input pos stop = .error (.singleByteWithPrefix x) := by
  obtain ⟨hPos, hFirst, hTail⟩ := extract_toList_eq_cons hStop h
  obtain ⟨hPos', hSecond, -⟩ := extract_toList_eq_cons hStop hTail
  rw [decodeItem.eq_def]
  simp [byteArray_getElem_eq_get!, hPos, hFirst, readPrefix, hx, bind, Except.bind, hSecond,
    show pos + 1 + 1 ≤ stop by omega, show pos + 1 < input.size by omega]

/-- `b7 + k`, then `k` length bytes of which the first is zero, for `1 <= k <= 8`. -/
theorem decodeItem_leadingZero_bytes (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (lengthTail : List UInt8)
    {input : ByteArray} {pos stop : Nat} {rest : List UInt8} (hLen : lengthTail.length + 1 = k)
    (hStop : stop ≤ input.size)
    (h : (input.extract pos stop).data.toList =
      UInt8.ofNat (0xb7 + k) :: (0 :: lengthTail) ++ rest) :
    decodeItem input pos stop = .error .leadingZeroInLength := by
  subst hLen
  have hMod : (0xb7 + (lengthTail.length + 1)) % 256 = 0xb7 + (lengthTail.length + 1) :=
    Nat.mod_eq_of_lt (by omega)
  have hCount := congrArg List.length h
  rw [length_extract_toList input pos stop hStop] at hCount
  simp only [List.length_cons, List.length_append] at hCount
  obtain ⟨hPos, hFirst, hTail⟩ := extract_toList_eq_cons hStop h
  obtain ⟨-, hZero, -⟩ := extract_toList_eq_cons hStop (by rw [hTail]; rfl)
  rw [decodeItem.eq_def]
  simp [byteArray_getElem_eq_get!, hPos, hFirst, hZero, readPrefix, readPrefix.readLongLength,
    UInt8.lt_iff_toNat_lt,
    UInt8.toNat_ofNat', hMod,
    show ¬ 0xb7 + (lengthTail.length + 1) < 0x80 by omega,
    show ¬ 0xb7 + (lengthTail.length + 1) < 0xb8 by omega,
    show 0xb7 + (lengthTail.length + 1) < 0xc0 by omega,
    show ¬ stop - (pos + 1) < lengthTail.length + 1 by omega,
    bind, Except.bind]

/-- `f7 + k`, then `k` length bytes of which the first is zero, for `1 <= k <= 8`. -/
theorem decodeItem_leadingZero_list (k : Nat) (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (lengthTail : List UInt8)
    {input : ByteArray} {pos stop : Nat} {rest : List UInt8} (hLen : lengthTail.length + 1 = k)
    (hStop : stop ≤ input.size)
    (h : (input.extract pos stop).data.toList =
      UInt8.ofNat (0xf7 + k) :: (0 :: lengthTail) ++ rest) :
    decodeItem input pos stop = .error .leadingZeroInLength := by
  subst hLen
  have hMod : (0xf7 + (lengthTail.length + 1)) % 256 = 0xf7 + (lengthTail.length + 1) :=
    Nat.mod_eq_of_lt (by omega)
  have hCount := congrArg List.length h
  rw [length_extract_toList input pos stop hStop] at hCount
  simp only [List.length_cons, List.length_append] at hCount
  obtain ⟨hPos, hFirst, hTail⟩ := extract_toList_eq_cons hStop h
  obtain ⟨-, hZero, -⟩ := extract_toList_eq_cons hStop (by rw [hTail]; rfl)
  rw [decodeItem.eq_def]
  simp [byteArray_getElem_eq_get!, hPos, hFirst, hZero, readPrefix, readPrefix.readLongLength,
    UInt8.lt_iff_toNat_lt,
    UInt8.toNat_ofNat', hMod,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0x80 by omega,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0xb8 by omega,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0xc0 by omega,
    show ¬ 0xf7 + (lengthTail.length + 1) < 0xf8 by omega,
    show ¬ stop - (pos + 1) < lengthTail.length + 1 by omega,
    bind, Except.bind]

/-- `b8 l`, with `0 < l < 56`: a short byte-string length in the long form. -/
theorem decodeItem_longFormForShortLength_bytes (l : UInt8) (h0 : 0 < l) (h56 : l < 56)
    {input : ByteArray} {pos stop : Nat} {rest : List UInt8} (hStop : stop ≤ input.size)
    (h : (input.extract pos stop).data.toList = 0xb8 :: l :: rest) :
    decodeItem input pos stop = .error (.longFormForShortLength l.toNat) := by
  obtain ⟨hPos, hFirst, hTail⟩ := extract_toList_eq_cons hStop h
  obtain ⟨hPos', hSecond, -⟩ := extract_toList_eq_cons hStop hTail
  rw [decodeItem.eq_def]
  simp only [UInt8.lt_iff_toNat_lt] at h0 h56
  simp [byteArray_getElem_eq_get!, hPos, hFirst, hSecond, readPrefix, readPrefix.readLongLength,
    readBigEndian,
    UInt8.lt_iff_toNat_lt, bind, Except.bind, show l ≠ 0 from fun h => by simp [h] at h0,
    show l.toNat < 56 from h56, show ¬ stop - (pos + 1) < 1 by omega]

/-- `f8 l`, with `0 < l < 56`: a short list-payload length in the long form. -/
theorem decodeItem_longFormForShortLength_list (l : UInt8) (h0 : 0 < l) (h56 : l < 56)
    {input : ByteArray} {pos stop : Nat} {rest : List UInt8} (hStop : stop ≤ input.size)
    (h : (input.extract pos stop).data.toList = 0xf8 :: l :: rest) :
    decodeItem input pos stop = .error (.longFormForShortLength l.toNat) := by
  obtain ⟨hPos, hFirst, hTail⟩ := extract_toList_eq_cons hStop h
  obtain ⟨hPos', hSecond, -⟩ := extract_toList_eq_cons hStop hTail
  rw [decodeItem.eq_def]
  simp only [UInt8.lt_iff_toNat_lt] at h0 h56
  simp [byteArray_getElem_eq_get!, hPos, hFirst, hSecond, readPrefix, readPrefix.readLongLength,
    readBigEndian,
    UInt8.lt_iff_toNat_lt, bind, Except.bind, show l ≠ 0 from fun h => by simp [h] at h0,
    show l.toNat < 56 from h56, show ¬ stop - (pos + 1) < 1 by omega]

end EthLib.Serialization.Rlp
