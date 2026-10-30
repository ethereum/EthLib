import EthLib.Serialization.Rlp.Decode
import EthLib.Serialization.Proofs.Rlp.Item

/-!
# `Serialization.Proofs.Rlp.RoundTrip`

Decoding undoes encoding: `decode_encode` proves `encode x = .ok b → decode b = .ok x`, for every item `x`.

So `encode` is injective: two items never share an encoding.

`encode_prefix_free` proves that no encoding is a proper prefix of another.

The proof follows the shape of an encoding.

1. The first byte and the length bytes of a prefix read back as the kind and the length of the payload.
2. A byte string reads back from its prefix and its bytes.
3. A list reads back from its prefix and the encodings of its items.
4. Items read back one after another, by induction on the tree.

Each step holds with any bytes after the encoding, since a list holds more items after each one.
-/

namespace EthLib.Serialization.Rlp

/-- The short prefix `offset + length` reads back as its kind and its length, with no length bytes. -/
theorem readPrefix_short (kind : PayloadKind) (length : Nat) (h : length < 56) (rest : List UInt8) :
    readPrefix (UInt8.ofNat (kind.offset + length)) rest = .ok (kind, 0, length) := by
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

/-- The long prefix `offset + 55 + k`, then `BE(length)` on `k` bytes, reads back as its kind and its length. -/
theorem readPrefix_long (kind : PayloadKind) (length : Nat) (h1 : 56 ≤ length) (h2 : length < 2 ^ 64)
    (rest : List UInt8) :
    readPrefix (UInt8.ofNat (kind.offset + 55 + (bigEndian length).size))
        ((bigEndian length).data.toList ++ rest)
      = .ok (kind, (bigEndian length).size, length) := by
  obtain ⟨hLen, hk1, hk8⟩ := bigEndian_length_bounds length h1 h2
  -- The `k` bytes of the length read back as `BE(length)`.
  have hLong : readPrefix.readLongLength ((bigEndian length).data.toList ++ rest) kind
      (bigEndian length).size = .ok (kind, (bigEndian length).size, length) := by
    have hTake : ((bigEndian length).data.toList ++ rest).take (bigEndian length).size
        = (bigEndian length).data.toList :=
      List.take_left' hLen
    have hHead : ((bigEndian length).data.toList).head? ≠ some 0 := by
      intro h0
      exact bigEndian_head_ne_zero length 0 h0 rfl
    simp only [readPrefix.readLongLength, hTake, bigEndian_value, List.length_append]
    simp [hHead, show ¬ length < 56 by omega]
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

/-- A prefix is a first byte of at least `0x80`, then the bytes that `readPrefix` reads back as the kind and the length. -/
theorem lengthPrefix_readPrefix (kind : PayloadKind) (length : Nat) (pre : ByteArray)
    (h : lengthPrefix kind length = .ok pre) :
    ∃ first lengthBytes, pre.data.toList = first :: lengthBytes ∧ 0x80 ≤ first ∧
      ∀ rest, readPrefix first (lengthBytes ++ rest) = .ok (kind, lengthBytes.length, length) := by
  unfold lengthPrefix at h
  by_cases hShort : length < 56
  · -- Short form: the one byte `offset + length`.
    rw [ite_eq_left hShort] at h
    cases h
    refine ⟨UInt8.ofNat (kind.offset + length), [], by simp, ?_, ?_⟩
    · cases kind <;> simp [PayloadKind.offset, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat'] <;> omega
    · intro rest
      simpa using readPrefix_short kind length hShort rest
  · rw [ite_eq_right hShort] at h
    by_cases hLong : length < 2 ^ 64
    · -- Long form: the byte `offset + 55 + k`, then `BE(length)` on `k` bytes.
      rw [ite_eq_left hLong] at h
      cases h
      obtain ⟨hLen, hk1, hk8⟩ := bigEndian_length_bounds length (by omega) hLong
      refine ⟨UInt8.ofNat (kind.offset + 55 + (bigEndian length).size),
        (bigEndian length).data.toList, by simp, ?_, ?_⟩
      · cases kind <;> simp [PayloadKind.offset, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat'] <;> omega
      · intro rest
        rw [hLen]
        exact readPrefix_long kind length (by omega) hLong rest
    · rw [ite_eq_right hLong] at h
      cases h

/-- The item read from `input`, and the bytes after it, without the bound on their length. -/
def readItem (input : List UInt8) : Except RlpError (Item × List UInt8) :=
  (decodeItem input).map fun (item, rest) => (item, rest.val)

/-- A list reads back from its prefix and the encodings of its items, with any bytes after them. -/
theorem readItem_list (payload rest : List UInt8) (items : List Item) (pre : ByteArray)
    (h : lengthPrefix .list payload.length = .ok pre) (hItems : decodeItems payload = .ok items) :
    readItem (pre.data.toList ++ payload ++ rest) = .ok (.list items, rest) := by
  obtain ⟨first, lengthBytes, hPre, hFirst, hRead⟩ := lengthPrefix_readPrefix .list payload.length pre h
  rw [hPre]
  have hHigh : ¬ first < 0x80 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at hFirst ⊢
    omega
  unfold readItem
  rw [List.cons_append, List.cons_append, List.append_assoc, decodeItem.eq_def]
  simp only [hHigh, ite_false]
  rw [hRead (payload ++ rest)]
  simp [bind, Except.bind, hItems, Except.map]

/-- A byte string with a prefix reads back from that prefix and its bytes, with any bytes after them. -/
theorem readItem_bytes (data : ByteArray) (rest : List UInt8) (pre : ByteArray)
    (h : lengthPrefix .bytes data.size = .ok pre) (hNotSingle : isSingleLowByte data = false) :
    readItem (pre.data.toList ++ data.data.toList ++ rest) = .ok (.bytes data, rest) := by
  obtain ⟨first, lengthBytes, hPre, hFirst, hRead⟩ := lengthPrefix_readPrefix .bytes data.size pre h
  rw [hPre]
  have hHigh : ¬ first < 0x80 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le] at hFirst ⊢
    omega
  have hSize : data.data.toList.length = data.size := Array.length_toList
  unfold readItem
  rw [List.cons_append, List.cons_append, List.append_assoc, decodeItem.eq_def]
  simp only [hHigh, ite_false]
  rw [hRead (data.data.toList ++ rest), ← hSize]
  simp only [bind, Except.bind, List.drop_left, List.take_left, List.length_append]
  rw [ite_eq_left (Nat.le_add_right _ _)]
  split
  · -- One byte: it is at least `0x80`, or the byte string would be its own encoding.
    rename_i byte hOne
    have hByte : ¬ byte < 128 := by
      intro hLow
      have hData : data = ⟨#[byte]⟩ := by
        cases data with
        | mk arr => cases arr with
          | mk l => simp at hOne; simp [hOne]
      subst hData
      simp only [isSingleLowByte, dite_eq_right_iff, decide_eq_false_iff_not] at hNotSingle
      exact (hNotSingle rfl) hLow
    have hData : data = ⟨#[byte]⟩ := by
      cases data with
      | mk arr => cases arr with
        | mk l => simp at hOne; simp [hOne]
    simp [hByte, Except.map, hData]
  · simp [Except.map]

/-- A single byte below `0x80` reads back as itself. -/
theorem readItem_single (data : ByteArray) (rest : List UInt8) (h : isSingleLowByte data = true) :
    readItem (data.data.toList ++ rest) = .ok (.bytes data, rest) := by
  obtain ⟨⟨l⟩⟩ := data
  simp only [isSingleLowByte] at h
  split at h
  · rename_i hSize
    -- The byte string is one byte below `0x80`, which is its own encoding.
    match l, hSize, h with
    | [byte], _, hLow =>
      have hLow' : byte < 0x80 := of_decide_eq_true hLow
      unfold readItem
      rw [decodeItem.eq_def]
      simp [hLow', Except.map]
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
  rw [joinEncodings] at h
  cases hHead : encode item with
  | error err => simp [hHead, bind, Except.bind] at h
  | ok head =>
    cases hTail : joinEncodings rest with
    | error err => simp [hHead, hTail, bind, Except.bind] at h
    | ok tail =>
      simp [hHead, hTail, bind, Except.bind, pure, Except.pure] at h
      exact ⟨head, tail, by simp, by simp, h.symm⟩

/-- When `readItem` succeeds, `decodeItem` succeeds with the same item and the same rest. -/
theorem decodeItem_of_readItem (input rest : List UInt8) (item : Item)
    (h : readItem input = .ok (item, rest)) :
    ∃ hRest, decodeItem input = .ok (item, ⟨rest, hRest⟩) := by
  unfold readItem at h
  cases hDecode : decodeItem input with
  | error err => simp [hDecode, Except.map] at h
  | ok result =>
    obtain ⟨item', ⟨rest', hRest'⟩⟩ := result
    simp [hDecode, Except.map] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hRest', rfl⟩

mutual

/-- Decoding the front of an encoding, then more bytes, gives back the item and the bytes after it. -/
theorem readItem_encode : (x : Item) → (e : ByteArray) → encode x = .ok e → (rest : List UInt8) →
    readItem (e.data.toList ++ rest) = .ok (x, rest)
  | .bytes data, e, h, rest => by
    rw [encode] at h
    rcases encodeBytes_ok data e h with ⟨hSingle, hE⟩ | ⟨hSingle, pre, hPre, rfl⟩
    · rw [hE]
      exact readItem_single data rest hSingle
    · have := readItem_bytes data rest pre hPre hSingle
      simpa [List.append_assoc] using this
  | .list items, e, h, rest => by
    obtain ⟨payload, pre, hJoin, hPre, rfl⟩ := encode_list_ok items e h
    have hSize : payload.size = payload.data.toList.length := Array.length_toList.symm
    rw [hSize] at hPre
    have := readItem_list payload.data.toList rest items pre hPre (decodeItems_joinEncodings items payload hJoin)
    simpa [List.append_assoc] using this
termination_by structural x => x

/-- Decoding the encodings of items, one after another, gives back the items. -/
theorem decodeItems_joinEncodings : (xs : List Item) → (e : ByteArray) → joinEncodings xs = .ok e →
    decodeItems e.data.toList = .ok xs
  | [], e, h => by
    simp [joinEncodings] at h
    subst h
    rw [decodeItems]
    simp
  | x :: xs, e, h => by
    obtain ⟨head, tail, hHead, hTail, rfl⟩ := joinEncodings_cons_ok x xs e h
    -- The first item reads back from the front, and the rest is the encodings of the others.
    have hRead := readItem_encode x head hHead tail.data.toList
    obtain ⟨hRest, hDecode⟩ := decodeItem_of_readItem _ _ _ (by simpa using hRead)
    have hTailItems := decodeItems_joinEncodings xs tail hTail
    -- The first item takes at least one byte, so the input is not empty.
    have hNe : (head.data.toList ++ tail.data.toList).isEmpty = false := by
      have hHeadNe : head.data.toList ≠ [] := by
        intro h0
        simp [h0] at hRest
      simp [hHeadNe]
    have hAppend : (head ++ tail).data.toList = head.data.toList ++ tail.data.toList := by simp
    rw [hAppend, decodeItems]
    simp [hNe, hDecode, bind, Except.bind, hTailItems]
termination_by structural xs => xs

end

/-- Decoding undoes encoding: the encoding of an item decodes to that item. -/
theorem decode_encode (x : Item) (b : ByteArray) (h : encode x = .ok b) : decode b = .ok x := by
  -- The item reads back from the whole encoding, with no byte left.
  have hRead := readItem_encode x b h []
  rw [List.append_nil] at hRead
  obtain ⟨hRest, hDecode⟩ := decodeItem_of_readItem _ _ _ hRead
  simp [decode, hDecode, bind, Except.bind]

/-- Two items with the same encoding are the same item. -/
theorem encode_injective (x y : Item) (b : ByteArray) (hx : encode x = .ok b) (hy : encode y = .ok b) :
    x = y := by
  -- Both decode from `b`, and decoding is a function.
  have := (decode_encode x b hx).symm.trans (decode_encode y b hy)
  cases this
  rfl

/-- The parser reads an encoding from the front of any input, and leaves exactly the bytes after it.

This is the left-inverse property of Coglio's parser, `rlp-parse-tree-of-rlp-encode-tree`, with any bytes after the encoding. -/
theorem decodeItem_encode (x : Item) (e : ByteArray) (h : encode x = .ok e) (rest : List UInt8) :
    ∃ hRest, decodeItem (e.data.toList ++ rest) = .ok (x, ⟨rest, hRest⟩) :=
  decodeItem_of_readItem _ _ _ (readItem_encode x e h rest)

/-- No encoding is a proper prefix of another: `RLP` is prefix-free.

So a stream of encodings, one after another, splits in only one way, with no end marker.

This is `rlp-encode-tree-unamb-prefix` of Coglio, [Ethereum's Recursive Length Prefix in ACL2](https://doi.org/10.4204/EPTCS.327.11), Figure 5. -/
theorem encode_prefix_free (x y : Item) (ex ey : ByteArray) (hx : encode x = .ok ex) (hy : encode y = .ok ey)
    (more : List UInt8) (hPrefix : ey.data.toList = ex.data.toList ++ more) : more = [] := by
  -- Read `ey` from the front in two ways: as `y` with nothing after, and as `x` with `more` after.
  have hY := readItem_encode y ey hy []
  have hX := readItem_encode x ex hx more
  rw [List.append_nil, hPrefix, hX] at hY
  cases hY
  rfl

/-- An encoding followed by more bytes is not a whole encoding: `decode` reports the bytes left over. -/
theorem decode_trailing (x : Item) (e : ByteArray) (h : encode x = .ok e) (more : ByteArray)
    (hMore : more.size ≠ 0) :
    decode (e ++ more) = .error (.trailingBytes more.size) := by
  -- The item is read from the front, and the bytes of `more` are left.
  have hAppend : (e ++ more).data.toList = e.data.toList ++ more.data.toList := by simp
  obtain ⟨hRest, hDecode⟩ : ∃ hRest, decodeItem (e ++ more).data.toList = .ok (x, ⟨more.data.toList, hRest⟩) := by
    rw [hAppend]
    exact decodeItem_encode x e h more.data.toList
  have hLen : more.data.toList.length = more.size := Array.length_toList
  have hNe : more.data.toList.isEmpty = false := by
    cases hm : more.data.toList with
    | nil =>
      rw [hm] at hLen
      exact absurd hLen.symm hMore
    | cons _ _ => rfl
  simp only [decode, hDecode, bind, Except.bind, hNe, hLen]
  rfl

end EthLib.Serialization.Rlp
