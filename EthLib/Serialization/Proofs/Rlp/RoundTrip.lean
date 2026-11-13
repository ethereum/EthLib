module

import EthLib.Base.Proofs.Bytes
public import EthLib.Serialization.Proofs.Rlp.Bytes
public import EthLib.Serialization.Proofs.Rlp.Loops
public import EthLib.Serialization.Rlp.Decode
public import EthLib.Serialization.Proofs.Rlp.Item

/-!
# `Serialization.Proofs.Rlp.RoundTrip`

Decoding undoes encoding: for every item `x`, if `encode x = .ok b`, then `decode b = .ok x`.

So the encoding is injective: two items never share an encoding.

No encoding is a proper prefix of another.

The proof follows the shape of an encoding.

1. The first byte and the length bytes of a prefix read back as the kind and the length.
2. A byte string reads back from its prefix and its bytes.
3. A list reads back from its prefix and the encodings of its items.
4. Items read back one after another, by induction on the tree.

Each step holds with any bytes after the encoding, since a list holds more items after each one.

Each step also holds wherever the encoding sits in the array that the decoder reads.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

open EthLib.Base (byteArray_get_eq_get!)

/-- The short prefix `offset + length` reads back as its kind and its length. -/
theorem readPrefix_short (kind : PayloadKind) (length : Nat) (h : length < 56) (input : ByteArray)
    (pos stop : Nat) (bounded : stop ≤ input.size := by omega) :
    readPrefix input (UInt8.ofNat (kind.offset + length)) pos stop = .ok (kind, 0, length) := by
  cases kind
  · have hMod : (128 + length) % 256 = 128 + length := Nat.mod_eq_of_lt (by omega)
    simp only [readPrefix, PayloadKind.offset, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', hMod]
    simp [show 128 + length < 184 by omega]
  · have hMod : (192 + length) % 256 = 192 + length := Nat.mod_eq_of_lt (by omega)
    simp only [readPrefix, PayloadKind.offset, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', hMod]
    simp [show ¬ 192 + length < 184 by omega, show ¬ 192 + length < 192 by omega,
      show 192 + length < 248 by omega]

/-- The bytes of `BE(length)` number its size, which is between 1 and 8 for a long length. -/
theorem bigEndian_length_bounds (length : Nat) (h1 : 56 ≤ length) (h2 : length < 2 ^ 64) :
    (bigEndian length).data.toList.length = (bigEndian length).size ∧
      1 ≤ (bigEndian length).size ∧ (bigEndian length).size ≤ 8 := by
  have hSize : (bigEndian length).data.toList.length = (bigEndian length).size :=
    Array.length_toList
  refine ⟨hSize, ?_, bigEndian_size_le length 8 (by simpa using h2)⟩
  -- No bytes would read back as 0, not as a length of at least 56.
  have hValue := bigEndian_value length
  rcases hNil : (bigEndian length).data.toList with _ | ⟨b, bs⟩
  · rw [hNil] at hValue
    simp [ofBigEndian] at hValue
    omega
  · rw [hNil] at hSize
    simp at hSize
    omega

/-- The long prefix reads back as its kind and its length.

That prefix is `offset + 55 + k`, then `BE(length)` on `k` bytes at the start of the bytes read. -/
theorem readPrefix_long (kind : PayloadKind) (length : Nat) (h1 : 56 ≤ length) (h2 : length < 2 ^ 64)
    {input : ByteArray} {pos stop : Nat} {rest : List UInt8} (hPos : pos ≤ stop)
    (hStop : stop ≤ input.size)
    (h : (input.extract pos stop).data.toList = (bigEndian length).data.toList ++ rest) :
    readPrefix input (UInt8.ofNat (kind.offset + 55 + (bigEndian length).size)) pos stop
      = .ok (kind, (bigEndian length).size, length) := by
  obtain ⟨hLen, hk1, hk8⟩ := bigEndian_length_bounds length h1 h2
  obtain ⟨hMid, hBytes, -⟩ := extract_toList_eq_append hPos hStop h
  rw [hLen] at hMid hBytes
  -- The `k` bytes of the length read back as `BE(length)`, whose first byte is not zero.
  have hHead : input.get! pos ≠ 0 := by
    rw [extract_toList_cons input pos _ (by omega) (by omega)] at hBytes
    intro h0
    exact bigEndian_head_ne_zero length (input.get! pos) (by rw [← hBytes]; rfl) h0
  have hLong : readPrefix.readLongLength input pos stop (by omega) kind (bigEndian length).size
      = .ok (kind, (bigEndian length).size, length) := by
    simp only [readPrefix.readLongLength,
      readBigEndian_zero input pos (bigEndian length).size (by omega), hBytes, bigEndian_value]
    simp [byteArray_get_eq_get!, hHead, show (bigEndian length).size ≠ 0 by omega,
      show ¬ stop - pos < (bigEndian length).size by omega,
      show ¬ length < 56 by omega]
  cases kind
  · have hMod : (128 + 55 + (bigEndian length).size) % 256 = 183 + (bigEndian length).size :=
      Nat.mod_eq_of_lt (by omega)
    simp only [readPrefix, PayloadKind.offset, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', hMod]
    simp [show ¬ 183 + (bigEndian length).size < 184 by omega,
      show 183 + (bigEndian length).size < 192 by omega, hLong]
  · have hMod : (192 + 55 + (bigEndian length).size) % 256 = 247 + (bigEndian length).size :=
      Nat.mod_eq_of_lt (by omega)
    simp only [readPrefix, PayloadKind.offset, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat', hMod]
    simp [show ¬ 247 + (bigEndian length).size < 184 by omega,
      show ¬ 247 + (bigEndian length).size < 192 by omega,
      show ¬ 247 + (bigEndian length).size < 248 by omega, hLong]

/-- A prefix is a first byte of at least `0x80`, then bytes that read back as kind and length. -/
theorem lengthPrefix_readPrefix (kind : PayloadKind) (length : Nat) (pre : ByteArray)
    (h : lengthPrefix kind length = .ok pre) :
    ∃ first lengthBytes, pre.data.toList = first :: lengthBytes ∧ 0x80 ≤ first ∧
      ∀ (input : ByteArray) (pos stop : Nat) (rest : List UInt8), pos ≤ stop →
        ∀ hBound : stop ≤ input.size,
        (input.extract pos stop).data.toList = lengthBytes ++ rest →
        readPrefix input first pos stop = .ok (kind, lengthBytes.length, length) := by
  unfold lengthPrefix at h
  by_cases hShort : length < 56
  · -- Short form: the one byte `offset + length`.
    rw [ite_eq_left hShort] at h
    cases h
    refine ⟨UInt8.ofNat (kind.offset + length), [], by simp, ?_, ?_⟩
    · cases kind <;> simp [PayloadKind.offset, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat'] <;> omega
    · intro input pos stop rest _ _ _
      simpa using readPrefix_short kind length hShort input pos stop
  · rw [ite_eq_right hShort] at h
    by_cases hLong : length < 2 ^ 64
    · -- Long form: the byte `offset + 55 + k`, then `BE(length)` on `k` bytes.
      rw [ite_eq_left hLong] at h
      cases h
      obtain ⟨hLen, hk1, hk8⟩ := bigEndian_length_bounds length (by omega) hLong
      refine ⟨UInt8.ofNat (kind.offset + 55 + (bigEndian length).size),
        (bigEndian length).data.toList, by simp, ?_, ?_⟩
      · cases kind <;> simp [PayloadKind.offset, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat'] <;> omega
      · intro input pos stop rest hPos hStop hInput
        rw [hLen]
        exact readPrefix_long kind length (by omega) hLong hPos hStop hInput
    · rw [ite_eq_right hLong] at h
      cases h

/-- The item read from the bytes of `input` from `pos` to `stop`, and the position after it. -/
def readItem (input : ByteArray) (pos stop : Nat)
    (bounded : stop ≤ input.size := by omega) : Except RlpError (Item × Nat) :=
  (decodeItem input pos stop).map fun (item, next) => (item, next.val)

/-- When the parser succeeds, the decoder of one item succeeds with the same item and position. -/
theorem decodeItem_of_readItem {input : ByteArray} {pos stop next : Nat} {item : Item}
    {bounded : stop ≤ input.size}
    (h : readItem input pos stop = .ok (item, next)) :
    ∃ hNext, decodeItem input pos stop = .ok (item, ⟨next, hNext⟩) := by
  unfold readItem at h
  cases hDecode : decodeItem input pos stop with
  | error err => simp [hDecode, Except.map] at h
  | ok result =>
    obtain ⟨item', ⟨next', hNext'⟩⟩ := result
    simp [hDecode, Except.map] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hNext', rfl⟩

/-- What the decoder learns from a prefix, then a payload, then more bytes.

The first byte is at least `0x80`, and the length bytes read back as the kind and the length. -/
theorem readItem_prefix {input : ByteArray} {pos stop : Nat} {first : UInt8}
    {lengthBytes payload rest : List UInt8} {kind : PayloadKind} (hStop : stop ≤ input.size)
    (hFirst : 0x80 ≤ first)
    (hRead : ∀ (input : ByteArray) (pos stop : Nat) (rest : List UInt8), pos ≤ stop →
      ∀ hBound : stop ≤ input.size, (input.extract pos stop).data.toList = lengthBytes ++ rest →
      readPrefix input first pos stop = .ok (kind, lengthBytes.length, payload.length))
    (hInput : (input.extract pos stop).data.toList = first :: (lengthBytes ++ payload ++ rest)) :
    pos < stop ∧ input.get! pos = first ∧ ¬ first < 0x80 ∧
      readPrefix input first (pos + 1) stop = .ok (kind, lengthBytes.length, payload.length) ∧
      pos + 1 + lengthBytes.length + payload.length ≤ stop ∧
      (input.extract (pos + 1 + lengthBytes.length)
        (pos + 1 + lengthBytes.length + payload.length)).data.toList = payload := by
  obtain ⟨hPos, hGet, hTail⟩ := extract_toList_eq_cons hStop hInput
  rw [List.append_assoc] at hTail
  obtain ⟨hMid, -, hBody⟩ := extract_toList_eq_append (by omega) hStop hTail
  obtain ⟨hEnd, hPayload, -⟩ := extract_toList_eq_append hMid hStop hBody
  have hHigh : ¬ first < 0x80 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at hFirst ⊢
    omega
  exact ⟨hPos, hGet, hHigh, hRead input (pos + 1) stop _ (by omega) hStop hTail, hEnd, hPayload⟩

/-- A list reads back from its prefix and the encodings of its items, with any bytes after them. -/
theorem readItem_list {input : ByteArray} {pos stop : Nat} {payload rest : List UInt8}
    {items : List Item} {pre : ByteArray} (hStop : stop ≤ input.size)
    (h : lengthPrefix .list payload.length = .ok pre)
    (hInput : (input.extract pos stop).data.toList = pre.data.toList ++ payload ++ rest)
    (hItems : ∀ start, ∀ hBound : start + payload.length ≤ input.size,
      (input.extract start (start + payload.length)).data.toList = payload →
      decodeItems input start (start + payload.length) = .ok items) :
    readItem input pos stop = .ok (.list items, pos + pre.size + payload.length) := by
  obtain ⟨first, lengthBytes, hPre, hFirst, hRead⟩ :=
    lengthPrefix_readPrefix .list payload.length pre h
  rw [hPre, List.cons_append, List.cons_append] at hInput
  obtain ⟨hPos, hGet, hHigh, hRP, hFit, hPayload⟩ := readItem_prefix hStop hFirst hRead hInput
  have hSize : pre.size = lengthBytes.length + 1 := by
    simp [← ByteArray.size_data, ← Array.length_toList, hPre]
  unfold readItem
  rw [decodeItem.eq_def]
  simp only [byteArray_get_eq_get!, hPos, hGet, hHigh, hRP, dite_true, ite_false,
    bind, Except.bind, hFit,
    hItems _ (by omega) hPayload, Except.map, Except.ok.injEq, Prod.mk.injEq, true_and]
  omega

/-- A byte string reads back from its prefix and its bytes, with any bytes after them. -/
theorem readItem_bytes {input : ByteArray} {pos stop : Nat} (data : ByteArray) {rest : List UInt8}
    {pre : ByteArray} (hStop : stop ≤ input.size) (h : lengthPrefix .bytes data.size = .ok pre)
    (hNotSingle : isSingleLowByte data = false)
    (hInput : (input.extract pos stop).data.toList = pre.data.toList ++ data.data.toList ++ rest) :
    readItem input pos stop = .ok (.bytes data, pos + pre.size + data.size) := by
  have hLen : data.data.toList.length = data.size := Array.length_toList
  obtain ⟨first, lengthBytes, hPre, hFirst, hRead⟩ := lengthPrefix_readPrefix .bytes data.size pre h
  rw [hPre, List.cons_append, List.cons_append] at hInput
  rw [← hLen] at hRead
  obtain ⟨hPos, hGet, hHigh, hRP, hFit, hPayload⟩ := readItem_prefix hStop hFirst hRead hInput
  rw [hLen] at hRP hFit hPayload
  have hSize : pre.size = lengthBytes.length + 1 := by
    simp [← ByteArray.size_data, ← Array.length_toList, hPre]
  -- The bytes read are the bytes of the byte string.
  have hData : input.extract (pos + 1 + lengthBytes.length)
      (pos + 1 + lengthBytes.length + data.size) = data :=
    byteArray_eq_of_toList _ _ hPayload
  -- One byte below `0x80` would be its own encoding, which the byte string is not.
  have hOne : ¬ (data.size = 1 ∧ input.get! (pos + 1 + lengthBytes.length) < 0x80) := by
    rintro ⟨hOne, hLow⟩
    rw [hOne, extract_toList_cons input _ _ (by omega) (by omega),
      extract_toList_of_le input _ _ (by omega)] at hPayload
    obtain ⟨⟨l⟩⟩ := data
    simp only [ByteArray.size] at hOne
    simp only [isSingleLowByte, ByteArray.size, hOne, dite_true, decide_eq_false_iff_not]
      at hNotSingle
    apply hNotSingle
    have hl : l = [input.get! (pos + 1 + lengthBytes.length)] := hPayload.symm
    subst hl
    exact hLow
  unfold readItem
  rw [decodeItem.eq_def]
  simp only [byteArray_get_eq_get!, hPos, hGet, hHigh, hRP, dite_true, ite_false,
    bind, Except.bind, hFit]
  by_cases hLength : data.size = 1
  · have hLow : ¬ input.get! (pos + 1 + lengthBytes.length) < 0x80 :=
      fun hLow => hOne ⟨hLength, hLow⟩
    simp only [hLength] at hData
    simp only [hLength, dite_true, hLow, ite_false, hData,
      Except.map, Except.ok.injEq, Prod.mk.injEq, true_and]
    omega
  · simp only [hLength, dite_false, hData,
      Except.map, Except.ok.injEq, Prod.mk.injEq, true_and]
    omega

/-- A single byte below `0x80` reads back as itself. -/
theorem readItem_single {input : ByteArray} {pos stop : Nat} (data : ByteArray) {rest : List UInt8}
    (hStop : stop ≤ input.size) (h : isSingleLowByte data = true)
    (hInput : (input.extract pos stop).data.toList = data.data.toList ++ rest) :
    readItem input pos stop = .ok (.bytes data, pos + data.size) := by
  obtain ⟨⟨l⟩⟩ := data
  simp only [isSingleLowByte] at h
  split at h
  · rename_i hSize
    -- The byte string is one byte below `0x80`, which is its own encoding.
    match l, hSize, h with
    | [byte], _, hLow =>
      have hLow' : byte < 0x80 := of_decide_eq_true hLow
      obtain ⟨hPos, hGet, -⟩ := extract_toList_eq_cons hStop hInput
      unfold readItem
      rw [decodeItem.eq_def]
      simp only [byteArray_get_eq_get!, hPos, dite_true, hGet, hLow', ite_true, Except.map]
      rfl
  · cases h

/-- What a successful encoding of a list is made of. -/
theorem encode_list_ok (items : List Item) (e : ByteArray) (h : encode (.list items) = .ok e) :
    ∃ payload pre, joinEncodings items = .ok payload ∧ lengthPrefix .list payload.size = .ok pre ∧
      e = pre ++ payload := by
  rw [encode] at h
  cases hJoin : joinEncodings items with
  | error err => simp [hJoin, bind, Except.bind] at h
  | ok payload =>
    cases hPre : lengthPrefix .list payload.size with
    | error err => simp [hJoin, hPre, bind, Except.bind] at h
    | ok pre =>
      simp [hJoin, hPre, bind, Except.bind, pure, Except.pure] at h
      exact ⟨payload, pre, by simp, hPre, h.symm⟩

/-- The encoding of a list starts with a byte of at least `0xc0`.

So it never starts like a byte string, whose first byte is below `0xc0`. -/
theorem encode_list_head (items : List Item) (e : ByteArray) (h : encode (.list items) = .ok e) :
    ∃ first rest, e.data.toList = first :: rest ∧ 0xc0 ≤ first := by
  obtain ⟨payload, pre, -, hPre, rfl⟩ := encode_list_ok items e h
  obtain ⟨first, lengthBytes, hList, -, hRead⟩ :=
    lengthPrefix_readPrefix .list payload.size pre hPre
  refine ⟨first, lengthBytes ++ payload.data.toList, by simp [hList], ?_⟩
  -- Below `0xc0`, the prefix reads as the prefix of a byte string, not of a list.
  have hList := hRead ⟨lengthBytes.toArray⟩ 0 lengthBytes.length [] (Nat.zero_le _)
    (by simp [ByteArray.size]) (by simp)
  refine Decidable.byContradiction fun hLow => ?_
  unfold readPrefix readPrefix.readLongLength at hList
  simp only [UInt8.not_le] at hLow
  repeat' split at hList
  all_goals (try simp only at hList) <;> (repeat' split at hList) <;> simp at hList

/-- What a successful encoding of a byte string is made of. -/
theorem encodeBytes_ok (data e : ByteArray) (h : encodeBytes data = .ok e) :
    (isSingleLowByte data = true ∧ e = data) ∨
      (isSingleLowByte data = false ∧ ∃ pre, lengthPrefix .bytes data.size = .ok pre ∧ e = pre ++ data) := by
  unfold encodeBytes at h
  cases hSingle : isSingleLowByte data
  · cases hPre : lengthPrefix .bytes data.size with
    | error err => simp [hSingle, hPre, bind, Except.bind] at h
    | ok pre =>
      simp [hSingle, hPre, bind, Except.bind, pure, Except.pure] at h
      exact .inr ⟨rfl, pre, by simp, h.symm⟩
  · simp [hSingle] at h
    exact .inl ⟨rfl, h.symm⟩

/-- What a successful encoding of a nonempty list of items is made of. -/
theorem joinEncodings_cons_ok (item : Item) (rest : List Item) (e : ByteArray)
    (h : joinEncodings (item :: rest) = .ok e) :
    ∃ head tail, encode item = .ok head ∧ joinEncodings rest = .ok tail ∧ e = head ++ tail := by
  rw [joinEncodings_cons] at h
  cases hHead : encode item with
  | error err => simp [hHead, bind, Except.bind] at h
  | ok head =>
    cases hTail : joinEncodings rest with
    | error err => simp [hHead, hTail, bind, Except.bind] at h
    | ok tail =>
      simp [hHead, hTail, bind, Except.bind, pure, Except.pure] at h
      exact ⟨head, tail, by simp, by simp, h.symm⟩

mutual

/-- An encoding, then more bytes, reads back as the item and the position after the encoding. -/
theorem readItem_encode : (x : Item) → (e : ByteArray) → encode x = .ok e →
    ∀ {input : ByteArray} {pos stop : Nat} {rest : List UInt8}, ∀ hBound : stop ≤ input.size,
      (input.extract pos stop).data.toList = e.data.toList ++ rest →
      readItem input pos stop = .ok (x, pos + e.size)
  | .bytes data, e, h, input, pos, stop, rest, hStop, hInput => by
    rw [encode] at h
    rcases encodeBytes_ok data e h with ⟨hSingle, rfl⟩ | ⟨hSingle, pre, hPre, rfl⟩
    · exact readItem_single e hStop hSingle hInput
    · rw [ByteArray.toList_data_append] at hInput
      rw [readItem_bytes data hStop hPre hSingle hInput, ByteArray.size_append, Nat.add_assoc]
  | .list items, e, h, input, pos, stop, rest, hStop, hInput => by
    obtain ⟨payload, pre, hJoin, hPre, rfl⟩ := encode_list_ok items e h
    have hSize : payload.size = payload.data.toList.length := Array.length_toList.symm
    rw [hSize] at hPre
    rw [ByteArray.toList_data_append] at hInput
    have hItems : ∀ start, ∀ hBound : start + payload.data.toList.length ≤ input.size,
        (input.extract start (start + payload.data.toList.length)).data.toList =
          payload.data.toList →
        decodeItems input start (start + payload.data.toList.length) = .ok items := by
      intro start hEnd hBytes
      simp only [← hSize] at *
      exact decodeItems_joinEncodings items payload hJoin hEnd hBytes
    rw [readItem_list hStop hPre hInput hItems, ByteArray.size_append, ← hSize, Nat.add_assoc]
termination_by structural x => x

/-- Decoding the encodings of items, one after another, gives back the items. -/
theorem decodeItems_joinEncodings : (xs : List Item) → (e : ByteArray) → joinEncodings xs = .ok e →
    ∀ {input : ByteArray} {pos : Nat}, ∀ hBound : pos + e.size ≤ input.size,
      (input.extract pos (pos + e.size)).data.toList = e.data.toList →
      decodeItems input pos (pos + e.size) = .ok xs
  | [], e, h, input, pos, _, _ => by
    simp [joinEncodings] at h
    subst h
    change decodeItems input pos pos (by omega) = .ok []
    rw [decodeItems_eq input pos pos (by omega)]
    simp
  | x :: xs, e, h, input, pos, hEnd, hBytes => by
    obtain ⟨head, tail, hHead, hTail, rfl⟩ := joinEncodings_cons_ok x xs e h
    rw [ByteArray.toList_data_append] at hBytes
    simp only [ByteArray.size_append] at *
    have hEnd' : pos + (head.size + tail.size) ≤ input.size := by
      simpa only [ByteArray.size_append] using hEnd
    -- The first item reads back from the front, and the rest is the encodings of the others.
    obtain ⟨hNext, hDecode⟩ :=
      decodeItem_of_readItem (bounded := hEnd') (readItem_encode x head hHead hEnd' hBytes)
    have hHeadLen : head.data.toList.length = head.size := Array.length_toList
    obtain ⟨-, -, hRest⟩ := extract_toList_eq_append (by omega) hEnd' hBytes
    rw [hHeadLen] at hRest
    have hTailItems := decodeItems_joinEncodings xs tail hTail (input := input)
      (pos := pos + head.size)
      (by omega) (by rw [show pos + head.size + tail.size = pos + (head.size + tail.size) by omega]
                     exact hRest)
    rw [decodeItems_eq input pos (pos + (head.size + tail.size)) hEnd',
      ite_eq_left (by omega)]
    simp only [Nat.add_assoc] at hTailItems
    simp only [hDecode, bind, Except.bind, hTailItems]
termination_by structural xs => xs

end

/-- Decoding undoes encoding: the encoding of an item decodes to that item. -/
theorem decode_encode (x : Item) (b : ByteArray) (h : encode x = .ok b) : decode b = .ok x := by
  -- The item reads back from the whole encoding, with no byte left.
  have hRead := readItem_encode x b h (input := b) (pos := 0) (rest := []) (Nat.le_refl _)
    (by simp)
  obtain ⟨hNext, hDecode⟩ := decodeItem_of_readItem hRead
  simp [decode, hDecode, bind, Except.bind]

/-- Two items with the same encoding are the same item. -/
theorem encode_injective (x y : Item) (b : ByteArray) (hx : encode x = .ok b) (hy : encode y = .ok b) :
    x = y := by
  -- Both decode from `b`, and decoding is a function.
  have := (decode_encode x b hx).symm.trans (decode_encode y b hy)
  cases this
  rfl

/-- The parser reads an encoding from the front of the bytes it reads, and stops right after it.

The theorem is the left-inverse property of Coglio's parser, with any bytes after the encoding.

Coglio names it `rlp-parse-tree-of-rlp-encode-tree`. -/
theorem decodeItem_encode (x : Item) (e : ByteArray) (h : encode x = .ok e) {input : ByteArray}
    {pos stop : Nat} {rest : List UInt8} (hStop : stop ≤ input.size)
    (hInput : (input.extract pos stop).data.toList = e.data.toList ++ rest) :
    ∃ hNext, decodeItem input pos stop = .ok (x, ⟨pos + e.size, hNext⟩) :=
  decodeItem_of_readItem (readItem_encode x e h hStop hInput)

/-- No encoding is a proper prefix of another: `RLP` is prefix-free.

So a stream of encodings, one after another, splits in only one way, with no end marker.

The theorem is `rlp-encode-tree-unamb-prefix` in Figure 5 of Coglio, [the RLP paper][coglio].

That paper is "Ethereum's Recursive Length Prefix in ACL2".

[coglio]: https://doi.org/10.4204/EPTCS.327.11
-/
theorem encode_prefix_free (x y : Item) (ex ey : ByteArray) (hx : encode x = .ok ex) (hy : encode y = .ok ey)
    (more : List UInt8) (hPrefix : ey.data.toList = ex.data.toList ++ more) : more = [] := by
  -- Read `ey` from the front in two ways: as `y` with nothing after, and as `x` with `more` after.
  have hY := readItem_encode y ey hy (input := ey) (pos := 0) (rest := []) (Nat.le_refl _)
    (by simp)
  have hX := readItem_encode x ex hx (input := ey) (pos := 0) (rest := more) (Nat.le_refl _)
    (by simpa using hPrefix)
  rw [hX] at hY
  simp only [Except.ok.injEq, Prod.mk.injEq, Nat.zero_add] at hY
  have hLen := congrArg List.length hPrefix
  simp only [List.length_append, Array.length_toList, ByteArray.size_data] at hLen
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- An encoding followed by more bytes is not a whole encoding.

The decoder reports the bytes left over. -/
theorem decode_trailing (x : Item) (e : ByteArray) (h : encode x = .ok e) (more : ByteArray)
    (hMore : more.size ≠ 0) :
    decode (e ++ more) = .error (.trailingBytes more.size) := by
  -- The item is read from the front, and the bytes of `more` are left.
  obtain ⟨hNext, hDecode⟩ := decodeItem_encode x e h (input := e ++ more) (pos := 0)
    (rest := more.data.toList) (Nat.le_refl _)
    (by rw [ByteArray.extract_zero_size, ByteArray.toList_data_append])
  simp only [decode, hDecode, bind, Except.bind, ByteArray.size_append, Nat.zero_add]
  rw [ite_eq_right (by omega)]
  congr 2
  omega

end EthLib.Serialization.Rlp
