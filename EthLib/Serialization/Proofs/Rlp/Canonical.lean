module

import EthLib.Base.Proofs.Bytes
public import EthLib.Serialization.Proofs.Rlp.RoundTrip

/-!
# `Serialization.Proofs.Rlp.Canonical`

The decoder accepts only canonical input: if `decode b = .ok x`, then `encode x = .ok b`.

With the round trip, the encoding is a bijection between items and the accepted inputs.

So no item has two accepted encodings, and two decoders that follow this specification agree.

The decoder succeeds exactly on the encodings of items.

The parser reads the same item from a longer input, as a stream decoder needs.

The proof runs the decoder backwards:

1. A prefix that the decoder accepts is the prefix that the encoding writes.
   A length has no leading zero, and it is at least 56 in the long form.
2. A byte string that the decoder reads is not one byte below `0x80`.
   So the encoding writes it with that prefix.
3. A list payload is shorter than its item, so induction on the number of bytes covers its items.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

open EthLib.Base (byteArray_getElem_eq_get!)

/-- Bytes read in base 256 from a running value `acc` stay below `(acc + 1) * 256^count`. -/
theorem foldl_bigEndian_lt (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun acc byte => 256 * acc + byte.toNat) acc < (acc + 1) * 256 ^ bytes.length := by
  induction bytes generalizing acc with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hb := b.toNat_lt
    have step := ih (256 * acc + b.toNat)
    -- `256 * acc + b + 1 <= 256 * (acc + 1)`, then multiply both sides by `256^count`.
    have hle : (256 * acc + b.toNat + 1) * 256 ^ bs.length ≤ (acc + 1) * 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (acc + 1) (256 ^ bs.length),
        Nat.mul_comm ((256 ^ bs.length) * (acc + 1)) 256, ← Nat.mul_assoc,
        Nat.mul_comm 256 (256 ^ bs.length), Nat.mul_assoc]
      rw [Nat.mul_comm (256 * acc + b.toNat + 1)]
      exact Nat.mul_le_mul_left _ (by omega)
    omega

/-- Bytes read in base 256 are below `256^count`. -/
theorem ofBigEndian_lt (bytes : List UInt8) : ofBigEndian bytes < 256 ^ bytes.length := by
  have := foldl_bigEndian_lt bytes 0
  simpa [ofBigEndian] using this

/-- What an accepted length in the long form is made of. -/
theorem readLongLength_ok {input : ByteArray} {pos stop : Nat} {kind kind' : PayloadKind}
    {k k' length : Nat} (hStop : stop ≤ input.size)
    (h : readPrefix.readLongLength input pos stop (by omega) kind k = .ok (kind', k', length)) :
    kind' = kind ∧ k' = k ∧ k ≤ stop - pos ∧ 56 ≤ length ∧ length < 256 ^ k ∧
      (bigEndian length).data.toList = (input.extract pos (pos + k)).data.toList := by
  unfold readPrefix.readLongLength at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hShort hk
      split at h
      · cases h
      · rename_i hHead
        have hEnd : pos + k ≤ input.size := by omega
        rw [readBigEndian_zero input pos k hEnd] at h
        by_cases hSmall : ofBigEndian (input.extract pos (pos + k)).data.toList < 56
        · rw [ite_eq_left hSmall] at h
          cases h
        · rw [ite_eq_right hSmall, Except.ok.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hLen := length_extract_toList input pos (pos + k) hEnd
          refine ⟨rfl, rfl, by omega, by omega, ?_, ?_⟩
          · have := ofBigEndian_lt (input.extract pos (pos + k)).data.toList
            rwa [hLen, show pos + k - pos = k by omega] at this
          · -- The length bytes have no leading zero, so they are `BE` of the length.
            apply bigEndian_unique
            intro b hb hb0
            subst hb0
            rw [extract_toList_cons input pos (pos + k) (by omega) hEnd] at hb
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
            exact hHead (by simpa only [byteArray_getElem_eq_get!] using hb)

/-- The long prefix of a length, from its first byte and its `k` length bytes. -/
theorem lengthPrefix_long_toList (kind : PayloadKind) (length k : Nat) (lengthBytes : List UInt8)
    (h56 : 56 ≤ length) (hk : k ≤ 8) (hLt : length < 256 ^ k)
    (hBytes : (bigEndian length).data.toList = lengthBytes) (hLen : lengthBytes.length = k) :
    (lengthPrefix kind length).map (·.data.toList)
      = .ok (UInt8.ofNat (kind.offset + 55 + k) :: lengthBytes) := by
  -- `length < 256^k <= 256^8 = 2^64`, so the length takes the long form.
  have h64 : length < 2 ^ 64 :=
    Nat.lt_of_lt_of_le hLt (by
      rw [show (2 : Nat) ^ 64 = 256 ^ 8 by decide]
      exact Nat.pow_le_pow_right (by omega) hk)
  have hSize : (bigEndian length).size = k :=
    (Array.length_toList (xs := (bigEndian length).data)).symm.trans ((congrArg List.length hBytes).trans hLen)
  unfold lengthPrefix
  simp [show ¬ length < 56 by omega, h64, hSize, Except.map, hBytes]

/-- An accepted prefix is the prefix that the encoding writes for its kind and length. -/
theorem readPrefix_ok {input : ByteArray} {first : UInt8} {pos stop : Nat} {kind : PayloadKind}
    {k length : Nat} (hStop : stop ≤ input.size) (hHigh : ¬ first < 0x80)
    (h : readPrefix input first pos stop = .ok (kind, k, length)) :
    k ≤ stop - pos ∧ (lengthPrefix kind length).map (·.data.toList) =
      .ok (first :: (input.extract pos (pos + k)).data.toList) := by
  have hFirst : first.toNat < 256 := first.toNat_lt
  have hHigh' : 128 ≤ first.toNat := by
    have h128 : UInt8.toNat 128 = 128 := rfl
    simp only [UInt8.lt_iff_toNat_lt, h128] at hHigh
    omega
  unfold readPrefix at h
  simp only [UInt8.lt_iff_toNat_lt] at h
  by_cases h1 : first.toNat < 0xb8
  · -- A short byte string: the first byte is `0x80 + length`.
    simp only [show (0xb8 : UInt8).toNat = 0xb8 from rfl, h1, ite_true, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨Nat.zero_le _, ?_⟩
    unfold lengthPrefix
    rw [ite_eq_left (show first.toNat - 0x80 < 56 by omega)]
    simp only [Except.map, PayloadKind.offset, show 0x80 + (first.toNat - 0x80) = first.toNat by omega,
      UInt8.ofNat_toNat, Nat.add_zero, ByteArray.extract_same, ByteArray.data_empty]
  · simp only [show (0xb8 : UInt8).toNat = 0xb8 from rfl, h1, ite_false] at h
    by_cases h2 : first.toNat < 0xc0
    · -- A long byte string: the first byte is `0xb7 + k`.
      simp only [show (0xc0 : UInt8).toNat = 0xc0 from rfl, h2, ite_true] at h
      obtain ⟨hKind, hk, hTail, h56, hLt, hBytes⟩ := readLongLength_ok hStop h
      clear h
      subst hKind
      rw [hk]
      refine ⟨hTail, ?_⟩
      have := lengthPrefix_long_toList .bytes length (first.toNat - 0xb7)
        (input.extract pos (pos + (first.toNat - 0xb7))).data.toList h56 (by omega) hLt hBytes
        (by rw [length_extract_toList _ _ _ (by omega)]; omega)
      rw [this]
      simp only [PayloadKind.offset, show 0x80 + 55 + (first.toNat - 0xb7) = first.toNat by omega,
        UInt8.ofNat_toNat]
    · simp only [show (0xc0 : UInt8).toNat = 0xc0 from rfl, h2, ite_false] at h
      by_cases h3 : first.toNat < 0xf8
      · -- A short list: the first byte is `0xc0 + length`.
        simp only [show (0xf8 : UInt8).toNat = 0xf8 from rfl, h3, ite_true, Except.ok.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨Nat.zero_le _, ?_⟩
        unfold lengthPrefix
        rw [ite_eq_left (show first.toNat - 0xc0 < 56 by omega)]
        simp only [Except.map, PayloadKind.offset, show 0xc0 + (first.toNat - 0xc0) = first.toNat by omega,
          UInt8.ofNat_toNat, Nat.add_zero, ByteArray.extract_same, ByteArray.data_empty]
      · -- A long list: the first byte is `0xf7 + k`.
        simp only [show (0xf8 : UInt8).toNat = 0xf8 from rfl, h3, ite_false] at h
        obtain ⟨hKind, hk, hTail, h56, hLt, hBytes⟩ := readLongLength_ok hStop h
        clear h
        subst hKind
        rw [hk]
        refine ⟨hTail, ?_⟩
        have := lengthPrefix_long_toList .list length (first.toNat - 0xf7)
          (input.extract pos (pos + (first.toNat - 0xf7))).data.toList h56 (by omega) hLt hBytes
          (by rw [length_extract_toList _ _ _ (by omega)]; omega)
        rw [this]
        simp only [PayloadKind.offset, show 0xc0 + 55 + (first.toNat - 0xf7) = first.toNat by omega,
          UInt8.ofNat_toNat]

/-- A mapped success comes from a success. -/
theorem except_map_ok {α β : Type} (f : α → β) (r : Except RlpError α) (b : β) (h : r.map f = .ok b) :
    ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | error e => simp [Except.map] at h
  | ok a => exact ⟨a, rfl, by simpa [Except.map] using h⟩

/-- The encoding of a byte string whose bytes are `payload`, after a prefix the decoder accepted. -/
theorem encode_bytes_of_prefix (data : ByteArray) (pre : ByteArray) (hNotSingle : isSingleLowByte data = false)
    (hPre : lengthPrefix .bytes data.size = .ok pre) :
    encode (.bytes data) = .ok (pre ++ data) := by
  simp [encode, encodeBytes, hNotSingle, hPre, bind, Except.bind, pure, Except.pure]

/-- A byte string whose only byte, if it has one, is at least `0x80` is not its own encoding. -/
theorem isSingleLowByte_eq_false (data : ByteArray)
    (h : ∀ b, data.data.toList = [b] → ¬ b < 0x80) : isSingleLowByte data = false := by
  obtain ⟨⟨l⟩⟩ := data
  unfold isSingleLowByte
  split
  · rename_i hSize
    match l, hSize, h with
    | [b], _, h => exact decide_eq_false (h b rfl)
  · rfl

/-- One step of canonicity: an item that the parser reads is encoded as exactly the bytes it read.

The step assumes the same of every list payload shorter than the bytes read. -/
theorem readItem_canonical {input : ByteArray} {pos stop : Nat} (hStop : stop ≤ input.size)
    (hItems : ∀ a b, ∀ hBound : b ≤ input.size, b - a < stop - pos →
      ∀ xs, decodeItems input a b = .ok xs →
      ∃ e, joinEncodings xs = .ok e ∧ e.data.toList = (input.extract a b).data.toList)
    {x : Item} {next : Nat} (h : readItem input pos stop = .ok (x, next)) :
    ∃ e, encode x = .ok e ∧ (input.extract pos next).data.toList = e.data.toList := by
  unfold readItem at h
  rw [decodeItem.eq_def] at h
  by_cases hPos : pos < stop
  case neg =>
    -- No byte is left, so there is no item.
    simp [hPos, Except.map] at h
  simp only [byteArray_getElem_eq_get!, hPos, dite_true] at h
  have hCons := extract_toList_cons input pos stop hPos hStop
  by_cases hLow : input.get! pos < 0x80
  · -- A single byte below `0x80` is its own encoding.
    simp only [hLow, ite_true, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨⟨#[input.get! pos]⟩, ?_, ?_⟩
    · have hSingle : isSingleLowByte ⟨#[input.get! pos]⟩ = true := by
        show (if h : 1 = 1 then decide (input.get! pos < 0x80) else false) = true
        simp [hLow]
      simp [encode, encodeBytes, hSingle]
    · rw [extract_toList_cons input pos (pos + 1) (by omega) (by omega),
        extract_toList_of_le input (pos + 1) (pos + 1) (Nat.le_refl _)]
  simp only [hLow, ite_false] at h
  cases hRP : readPrefix input (input.get! pos) (pos + 1) stop with
  | error err =>
    rw [hRP] at h
    simp [bind, Except.bind, Except.map] at h
  | ok res =>
    obtain ⟨kind, k, length⟩ := res
    rw [hRP] at h
    simp only [bind, Except.bind] at h
    -- The prefix the decoder read is the one the encoding writes.
    obtain ⟨hk, hPreMap⟩ := readPrefix_ok hStop hLow hRP
    obtain ⟨pre, hPre, hPreBytes⟩ := except_map_ok _ _ _ hPreMap
    have hPreSize : pre.size = k + 1 := by
      rw [← ByteArray.size_data, ← Array.length_toList, hPreBytes, List.length_cons,
        length_extract_toList _ _ _ (by omega)]
      omega
    by_cases hFit : pos + 1 + k + length ≤ stop
    case neg => simp [hFit, Except.map] at h
    simp only [hFit, dite_true] at h
    -- The bytes read are the prefix, then the payload.
    have hSplit : (input.extract pos (pos + 1 + k + length)).data.toList =
        pre.data.toList ++ (input.extract (pos + 1 + k) (pos + 1 + k + length)).data.toList := by
      rw [extract_toList_split input pos (pos + 1 + k) _ (by omega) (by omega),
        extract_toList_cons input pos (pos + 1 + k) (by omega) (by omega), hPreBytes,
        List.cons_append]
    have hPayloadLen := length_extract_toList input (pos + 1 + k) (pos + 1 + k + length)
      (by omega)
    cases kind with
    | bytes =>
      dsimp only at h
      by_cases hOne : length = 1 ∧ input.get! (pos + 1 + k) < 0x80
      · obtain ⟨hLength, hLow⟩ := hOne
        simp [hLength, hLow, Except.map] at h
      have hPair :
          (.bytes (input.extract (pos + 1 + k) (pos + 1 + k + length)),
            pos + 1 + k + length) = (x, next) := by
        by_cases hLength : length = 1
        · have hLow : ¬ input.get! (pos + 1 + k) < 0x80 :=
            fun hLow => hOne ⟨hLength, hLow⟩
          simpa only [hLength, dite_true, hLow, ite_false, Except.map, Except.ok.injEq] using h
        · simpa only [hLength, dite_false, Except.map, Except.ok.injEq] using h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair
      -- A payload that is not one low byte encodes as the bytes read.
      have hSize : (input.extract (pos + 1 + k) (pos + 1 + k + length)).size = length := by
        rw [← ByteArray.size_data, ← Array.length_toList, hPayloadLen]
        omega
      have hNotSingle : isSingleLowByte (input.extract (pos + 1 + k) (pos + 1 + k + length)) =
          false := by
        apply isSingleLowByte_eq_false
        intro b hb hbLow
        have hLen1 : length = 1 := by
          have := congrArg List.length hb
          simp only [List.length_singleton] at this
          omega
        subst hLen1
        rw [extract_toList_cons input _ _ (by omega) (by omega),
          extract_toList_of_le input _ _ (by omega)] at hb
        simp only [List.cons.injEq, and_true] at hb
        exact hOne ⟨rfl, hb ▸ hbLow⟩
      refine ⟨pre ++ input.extract (pos + 1 + k) (pos + 1 + k + length),
        encode_bytes_of_prefix _ pre hNotSingle (by rw [hSize]; exact hPre), ?_⟩
      rw [hSplit, ByteArray.toList_data_append]
    | list =>
      dsimp only at h
      -- The payload is the encodings of the items, by the step for shorter payloads.
      cases hD : decodeItems input (pos + 1 + k) (pos + 1 + k + length) with
      | error err =>
        rw [hD] at h
        simp [Except.map] at h
      | ok items =>
        rw [hD] at h
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨e, hJoin, hE⟩ := hItems _ _ (by omega) (by omega) items hD
        have hSize : e.size = length := by
          rw [← ByteArray.size_data, ← Array.length_toList, hE, hPayloadLen]
          omega
        refine ⟨pre ++ e, ?_, ?_⟩
        · simp [encode, hJoin, hSize, hPre, bind, Except.bind, pure, Except.pure]
        · rw [hSplit, ByteArray.toList_data_append, hE]

/-- Canonicity up to `n` bytes.

What the decoder reads from at most `n` bytes is encoded as exactly those bytes.

- An item read from the front of the bytes is encoded as the bytes before the position after it.
- The items of a list payload are encoded, one after another, as the whole payload. -/
theorem canonical_upTo (n : Nat) :
    (∀ (input : ByteArray) (pos stop : Nat), ∀ hBound : stop ≤ input.size, stop - pos ≤ n →
      ∀ x next, readItem input pos stop = .ok (x, next) →
      ∃ e, encode x = .ok e ∧ (input.extract pos next).data.toList = e.data.toList) ∧
    (∀ (input : ByteArray) (pos stop : Nat), ∀ hBound : stop ≤ input.size, stop - pos ≤ n →
      ∀ xs, decodeItems input pos stop = .ok xs →
      ∃ e, joinEncodings xs = .ok e ∧ e.data.toList = (input.extract pos stop).data.toList) := by
  induction n with
  | zero =>
    refine ⟨fun input pos stop hStop hLen x next h =>
      readItem_canonical hStop (fun a b _ hab => by omega) h, ?_⟩
    -- No byte is left, and no bytes hold no item.
    intro input pos stop hStop hLen xs h
    rw [decodeItems_eq (bounded := by assumption), ite_eq_right (by omega)] at h
    cases h
    exact ⟨.empty, rfl, by rw [extract_toList_of_le input pos stop (by omega)]; rfl⟩
  | succ m ih =>
    -- Items first: a list payload is shorter than its item, so induction applies.
    have hItem : ∀ (input : ByteArray) (pos stop : Nat),
        ∀ hBound : stop ≤ input.size, stop - pos ≤ m + 1 →
        ∀ x next, readItem input pos stop = .ok (x, next) →
        ∃ e, encode x = .ok e ∧ (input.extract pos next).data.toList = e.data.toList :=
      fun input pos stop hStop hLen x next h =>
        readItem_canonical hStop (fun a b hb hab => ih.2 input a b hb (by omega)) h
    refine ⟨hItem, ?_⟩
    intro input pos stop hStop hLen xs h
    rw [decodeItems_eq (bounded := by assumption)] at h
    by_cases hPos : pos < stop
    case neg =>
      -- No byte is left, so there is no item.
      rw [ite_eq_right hPos] at h
      cases h
      exact ⟨.empty, rfl, by rw [extract_toList_of_le input pos stop (by omega)]; rfl⟩
    -- The first item, then the items of the rest, which is shorter.
    rw [ite_eq_left hPos] at h
    cases hFirst : decodeItem input pos stop with
    | error err =>
      rw [hFirst] at h
      simp [bind, Except.bind] at h
    | ok res =>
      obtain ⟨item, ⟨next, hNext⟩⟩ := res
      rw [hFirst] at h
      cases hRest : decodeItems input next stop with
      | error err =>
        simp [hRest, bind, Except.bind] at h
      | ok items =>
        simp [hRest, bind, Except.bind] at h
        subst h
        have hRead : readItem input pos stop = .ok (item, next) := by
          simp [readItem, hFirst, Except.map]
        obtain ⟨head, hHead, hHeadBytes⟩ := hItem input pos stop hStop hLen item next hRead
        obtain ⟨tail, hTail, hTailBytes⟩ := ih.2 input next stop hStop (by omega) items hRest
        refine ⟨head ++ tail, ?_, ?_⟩
        · simp [joinEncodings_cons, hHead, hTail, bind, Except.bind, pure, Except.pure]
        · rw [extract_toList_split input pos next stop (by omega) hNext.2, hHeadBytes,
            ← hTailBytes, ByteArray.toList_data_append]

/-- The decoder accepts only canonical input: what it decodes from `b` is encoded as exactly `b`. -/
theorem encode_decode (b : ByteArray) (x : Item) (h : decode b = .ok x) : encode x = .ok b := by
  unfold decode at h
  cases hItem : decodeItem b 0 b.size with
  | error err =>
    simp [hItem, bind, Except.bind] at h
  | ok res =>
    obtain ⟨item, ⟨next, hNext⟩⟩ := res
    simp only [hItem, bind, Except.bind] at h
    by_cases hEnd : next = b.size
    · -- The item is the whole input, with no byte left.
      simp only [hEnd, ite_true, Except.ok.injEq] at h
      subst h hEnd
      have hRead : readItem b 0 b.size = .ok (item, b.size) := by
        simp [readItem, hItem, Except.map]
      obtain ⟨e, hEncode, hBytes⟩ :=
        (canonical_upTo b.size).1 b 0 b.size (Nat.le_refl _) (by omega) _ _ hRead
      rw [hEncode, byteArray_eq_of_toList e b (by simpa using hBytes.symm)]
    · simp [hEnd] at h

/-- `encode` is a bijection between items and the byte strings that `decode` accepts.

- Every item that has an encoding decodes back from it.
- Every input that decodes is the encoding of what it decodes to. -/
theorem decode_eq_ok_iff (b : ByteArray) (x : Item) : decode b = .ok x ↔ encode x = .ok b :=
  ⟨encode_decode b x, decode_encode x b⟩

/-- What the parser reads from the front of the bytes is encoded as exactly the bytes it consumed.

This is the right-inverse property of Coglio's parser, `rlp-encode-tree-of-rlp-parse-tree`. -/
theorem encode_of_decodeItem {input : ByteArray} {pos stop next : Nat} {x : Item}
    {hNext : pos < next ∧ next ≤ stop} (hStop : stop ≤ input.size)
    (h : decodeItem input pos stop = .ok (x, ⟨next, hNext⟩)) :
    ∃ e, encode x = .ok e ∧ (input.extract pos next).data.toList = e.data.toList :=
  (canonical_upTo (stop - pos)).1 input pos stop hStop (Nat.le_refl _) x next
    (by simp [readItem, h, Except.map])

/-- The parser reads the same item when more bytes follow, and stops at the same position.

So a decoder that reads a stream needs no end marker. -/
theorem decodeItem_append {input : ByteArray} {pos stop stop' next : Nat} {x : Item}
    {hNext : pos < next ∧ next ≤ stop} (hLe : stop ≤ stop') (hStop : stop' ≤ input.size)
    (h : decodeItem input pos stop = .ok (x, ⟨next, hNext⟩)) :
    ∃ hNext', decodeItem input pos stop' = .ok (x, ⟨next, hNext'⟩) := by
  -- The bytes read are an encoding of `x`, and more bytes follow it.
  obtain ⟨e, hEncode, hBytes⟩ := encode_of_decodeItem (by omega) h
  have hLen := congrArg List.length hBytes
  rw [length_extract_toList input pos next (by omega), Array.length_toList,
    ByteArray.size_data] at hLen
  obtain ⟨hNext', hDecode⟩ := decodeItem_encode x e hEncode hStop
    (by rw [extract_toList_split input pos next stop' (by omega) (by omega), hBytes])
  obtain rfl : pos + e.size = next := by omega
  exact ⟨_, hDecode⟩

/-- The byte strings that encode some item: the image of `encode`.

This is `rlp-tree-encoding-p` of Coglio, Figure 4. -/
def IsEncoding (b : ByteArray) : Prop :=
  ∃ x, encode x = .ok b

/-- `decode` succeeds exactly on the encodings of items.

With the bijection, it is the declarative decoder of Coglio, Figure 6.

That decoder is the inverse of the encoding on its image. -/
theorem decode_isOk_iff (b : ByteArray) : (∃ x, decode b = .ok x) ↔ IsEncoding b := by
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x, encode_decode b x h⟩
  · rintro ⟨x, h⟩
    exact ⟨x, decode_encode x b h⟩

end EthLib.Serialization.Rlp
