import EthLib.Serialization.Proofs.Rlp.RoundTrip

/-!
# `Serialization.Proofs.Rlp.Canonical`

The decoder accepts only canonical input: `encode_decode` proves `decode b = .ok x → encode x = .ok b`.

With the round trip, `decode_eq_ok_iff` makes `encode` a bijection between items and the inputs that `decode` accepts.

So no item has two accepted encodings, and two decoders that follow this specification agree on every input.

`decode_isOk_iff` proves that `decode` succeeds exactly on the encodings of items.

`decodeItem_append` proves that the parser reads the same item from a longer input, as a stream decoder needs.

The proof runs the decoder backwards.

1. A prefix the decoder accepts is the prefix the encoding writes, because a length has no leading zero and is at least 56 in the long form.
2. A byte string the decoder reads is not one byte below `0x80`, so the encoding writes it with that prefix.
3. A list payload is shorter than its item, so induction on the number of bytes covers its items.
-/

namespace EthLib.Serialization.Rlp

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

/-- Two byte arrays with the same bytes are equal. -/
theorem byteArray_eq_of_toList (a b : ByteArray) (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b
  simp only [Array.toList_inj] at h
  rw [h]

/-- What a long length that `readLongLength` accepts is made of. -/
theorem readLongLength_ok (rest : List UInt8) (kind kind' : PayloadKind) (k k' length : Nat)
    (h : readPrefix.readLongLength rest kind k = .ok (kind', k', length)) :
    kind' = kind ∧ k' = k ∧ k ≤ rest.length ∧ 56 ≤ length ∧ length < 256 ^ k ∧
      (bigEndian length).data.toList = rest.take k := by
  unfold readPrefix.readLongLength at h
  by_cases hShort : rest.length < k
  · simp [hShort] at h
  · simp only [hShort, ite_false] at h
    by_cases hZero : (rest.take k).head? = some 0
    · simp [hZero] at h
    · simp only [hZero, ite_false] at h
      by_cases hSmall : ofBigEndian (rest.take k) < 56
      · simp [hSmall] at h
      · simp only [hSmall, ite_false, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hTakeLen : (rest.take k).length = k := by simp; omega
        refine ⟨rfl, rfl, by omega, by omega, ?_, ?_⟩
        · have := ofBigEndian_lt (rest.take k)
          rwa [hTakeLen] at this
        · -- The length bytes have no leading zero, so they are `BE` of the length.
          apply bigEndian_unique
          intro b hb hb0
          subst hb0
          exact hZero hb

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

/-- A prefix that `readPrefix` accepts is the prefix that the encoding writes for its kind and length. -/
theorem readPrefix_ok (first : UInt8) (tail : List UInt8) (kind : PayloadKind) (k length : Nat)
    (hHigh : ¬ first < 0x80) (h : readPrefix first tail = .ok (kind, k, length)) :
    k ≤ tail.length ∧ (lengthPrefix kind length).map (·.data.toList) = .ok (first :: tail.take k) := by
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
      UInt8.ofNat_toNat, List.take_zero]
  · simp only [show (0xb8 : UInt8).toNat = 0xb8 from rfl, h1, ite_false] at h
    by_cases h2 : first.toNat < 0xc0
    · -- A long byte string: the first byte is `0xb7 + k`.
      simp only [show (0xc0 : UInt8).toNat = 0xc0 from rfl, h2, ite_true] at h
      obtain ⟨hKind, hk, hTail, h56, hLt, hBytes⟩ :=
        readLongLength_ok tail .bytes kind (first.toNat - 0xb7) k length h
      clear h
      subst hKind
      rw [hk]
      refine ⟨hTail, ?_⟩
      have := lengthPrefix_long_toList .bytes length (first.toNat - 0xb7) (tail.take (first.toNat - 0xb7))
        h56 (by omega) hLt hBytes (by rw [List.length_take]; omega)
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
          UInt8.ofNat_toNat, List.take_zero]
      · -- A long list: the first byte is `0xf7 + k`.
        simp only [show (0xf8 : UInt8).toNat = 0xf8 from rfl, h3, ite_false] at h
        obtain ⟨hKind, hk, hTail, h56, hLt, hBytes⟩ :=
          readLongLength_ok tail .list kind (first.toNat - 0xf7) k length h
        clear h
        subst hKind
        rw [hk]
        refine ⟨hTail, ?_⟩
        have := lengthPrefix_long_toList .list length (first.toNat - 0xf7) (tail.take (first.toNat - 0xf7))
          h56 (by omega) hLt hBytes (by rw [List.length_take]; omega)
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

/-- One step of canonicity: an item that `readItem` reads is encoded as exactly the bytes it read.

The step assumes the same of every list payload shorter than the input. -/
theorem readItem_canonical (input : List UInt8)
    (hItems : ∀ payload : List UInt8, payload.length < input.length → ∀ xs, decodeItems payload = .ok xs →
      ∃ e, joinEncodings xs = .ok e ∧ e.data.toList = payload)
    (x : Item) (rest : List UInt8) (h : readItem input = .ok (x, rest)) :
    ∃ e, encode x = .ok e ∧ input = e.data.toList ++ rest := by
  match input, hItems, h with
  | [], _, h =>
    -- An empty input holds no item.
    unfold readItem at h
    rw [decodeItem.eq_def] at h
    simp [Except.map] at h
  | first :: tail, hItems, h =>
    unfold readItem at h
    rw [decodeItem.eq_def] at h
    simp only at h
    by_cases hLow : first < 0x80
    · -- A single byte below `0x80` is its own encoding.
      simp only [hLow, ite_true, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨#[first]⟩, ?_, by simp⟩
      have hSingle : isSingleLowByte ⟨#[first]⟩ = true := by
        show (if h : 1 = 1 then decide (first < 0x80) else false) = true
        simp [hLow]
      simp [encode, encodeBytes, hSingle]
    · simp only [hLow, ite_false] at h
      cases hRP : readPrefix first tail with
      | error err =>
        rw [hRP] at h
        simp [bind, Except.bind, Except.map] at h
      | ok res =>
        obtain ⟨kind, k, length⟩ := res
        rw [hRP] at h
        simp only [bind, Except.bind] at h
        -- The prefix the decoder read is the one the encoding writes.
        obtain ⟨hk, hPreMap⟩ := readPrefix_ok first tail kind k length hLow hRP
        obtain ⟨pre, hPre, hPreBytes⟩ := except_map_ok _ _ _ hPreMap
        -- The input is the prefix, the payload, then the rest.
        have hSplit : first :: tail
            = (first :: tail.take k) ++ (tail.drop k).take length ++ (tail.drop k).drop length := by
          rw [List.append_assoc, List.take_append_drop, List.cons_append, List.take_append_drop]
        by_cases hFit : length ≤ (tail.drop k).length
        · rw [ite_eq_left hFit] at h
          have hPayloadLen : ((tail.drop k).take length).length = length := by
            rw [List.length_take]
            omega
          cases kind with
          | bytes =>
            dsimp only at h
            -- The bytes of the payload, named, with their count.
            generalize hp : (tail.drop k).take length = payload at h hPayloadLen hSplit
            -- A byte string whose bytes are the payload, and which is not one low byte, encodes as the input read.
            have finish : ∀ data : ByteArray, data.data.toList = payload → isSingleLowByte data = false →
                ∃ e, encode (.bytes data) = .ok e ∧
                  first :: tail = e.data.toList ++ (tail.drop k).drop length := by
              intro data hData hNotSingle
              have hSize : data.size = length := by
                rw [← hPayloadLen, ← hData]
                exact Array.length_toList.symm
              refine ⟨pre ++ data, encode_bytes_of_prefix data pre hNotSingle (by rw [hSize]; exact hPre), ?_⟩
              rw [hSplit]
              simp [hPreBytes, hData]
            rcases payload with _ | ⟨byte, _ | ⟨byte2, more⟩⟩
            · -- No byte: the empty byte string.
              simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact finish _ (by simp) rfl
            · -- One byte, which must be at least `0x80`.
              by_cases hb : byte < 128
              · simp [hb, Except.map] at h
              · simp only [hb, ite_false, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine finish _ (by simp) ?_
                show (if h : 1 = 1 then decide (byte < 0x80) else false) = false
                simp [hb]
            · -- Two bytes or more.
              simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine finish _ (by simp) ?_
              unfold isSingleLowByte
              rw [dite_eq_right (by simp [ByteArray.size])]
          | list =>
            dsimp only at h
            generalize hp : (tail.drop k).take length = payload at h hPayloadLen hSplit
            -- The payload is the encodings of the items, by the step for shorter payloads.
            cases hD : decodeItems payload with
            | error err =>
              rw [hD] at h
              simp [Except.map] at h
            | ok items =>
              rw [hD] at h
              simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hShorter : payload.length < (first :: tail).length := by
                rw [hPayloadLen]
                simp at hFit ⊢
                omega
              obtain ⟨e, hJoin, hE⟩ := hItems payload hShorter items hD
              have hSize : e.size = length := by
                rw [← hPayloadLen, ← hE]
                exact Array.length_toList.symm
              refine ⟨pre ++ e, ?_, ?_⟩
              · simp [encode, hJoin, hSize, hPre, bind, Except.bind, pure, Except.pure]
              · rw [hSplit]
                simp [hPreBytes, hE]
        · rw [ite_eq_right hFit] at h
          simp [Except.map] at h
/-- Canonicity up to `n` bytes: what the decoder reads from at most `n` bytes is encoded as exactly those bytes.

- An item read from the front of an input is encoded as the bytes before the rest.
- The items of a list payload are encoded, one after another, as the whole payload. -/
theorem canonical_upTo (n : Nat) :
    (∀ input : List UInt8, input.length ≤ n → ∀ x rest, readItem input = .ok (x, rest) →
      ∃ e, encode x = .ok e ∧ input = e.data.toList ++ rest) ∧
    (∀ payload : List UInt8, payload.length ≤ n → ∀ xs, decodeItems payload = .ok xs →
      ∃ e, joinEncodings xs = .ok e ∧ e.data.toList = payload) := by
  induction n with
  | zero =>
    refine ⟨fun input hLen x rest h => readItem_canonical input (fun p hp => by omega) x rest h, ?_⟩
    -- The only payload of 0 bytes is empty, and it holds no item.
    intro payload hLen xs h
    have hNil : payload = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hNil
    rw [decodeItems] at h
    simp at h
    subst h
    exact ⟨.empty, rfl, rfl⟩
  | succ m ih =>
    -- Items first: a list payload is shorter than its item, so the step for shorter payloads applies.
    have hItem : ∀ input : List UInt8, input.length ≤ m + 1 → ∀ x rest, readItem input = .ok (x, rest) →
        ∃ e, encode x = .ok e ∧ input = e.data.toList ++ rest :=
      fun input hLen x rest h =>
        readItem_canonical input (fun p hp => ih.2 p (by omega)) x rest h
    refine ⟨hItem, ?_⟩
    intro payload hLen xs h
    rw [decodeItems] at h
    by_cases hEmpty : payload.isEmpty
    · -- An empty payload holds no item.
      simp only [hEmpty, ite_true, Except.ok.injEq] at h
      subst h
      exact ⟨.empty, rfl, by simpa using hEmpty⟩
    · -- The first item, then the items of the rest, which is shorter.
      simp only [hEmpty] at h
      cases hFirst : decodeItem payload with
      | error err =>
        rw [hFirst] at h
        simp [bind, Except.bind] at h
      | ok res =>
        obtain ⟨item, ⟨rest, hRest⟩⟩ := res
        rw [hFirst] at h
        cases hNext : decodeItems rest with
        | error err =>
          simp [hNext, bind, Except.bind] at h
        | ok items =>
          simp [hNext, bind, Except.bind] at h
          subst h
          have hRead : readItem payload = .ok (item, rest) := by
            simp [readItem, hFirst, Except.map]
          obtain ⟨head, hHead, hPayload⟩ := hItem payload hLen item rest hRead
          obtain ⟨tail, hTail, hRestBytes⟩ := ih.2 rest (by omega) items hNext
          refine ⟨head ++ tail, ?_, ?_⟩
          · simp [joinEncodings, hHead, hTail, bind, Except.bind, pure, Except.pure]
          · simp [hPayload, hRestBytes]

/-- The decoder accepts only canonical input: what it decodes from `b` is encoded as exactly `b`. -/
theorem encode_decode (b : ByteArray) (x : Item) (h : decode b = .ok x) : encode x = .ok b := by
  unfold decode at h
  cases hItem : decodeItem b.data.toList with
  | error err =>
    simp [hItem, bind, Except.bind] at h
  | ok res =>
    obtain ⟨item, ⟨rest, hRest⟩⟩ := res
    simp only [hItem, bind, Except.bind] at h
    by_cases hEmpty : rest.isEmpty
    · -- The item is the whole input, with no byte left.
      simp only [hEmpty, ite_true, Except.ok.injEq] at h
      subst h
      have hNil : rest = [] := by simpa using hEmpty
      subst hNil
      have hRead : readItem b.data.toList = .ok (item, []) := by
        simp [readItem, hItem, Except.map]
      obtain ⟨e, hEncode, hBytes⟩ := (canonical_upTo b.data.toList.length).1 _ (Nat.le_refl _) _ _ hRead
      rw [hEncode, byteArray_eq_of_toList e b (by simpa using hBytes.symm)]
    · simp [hEmpty] at h

/-- `encode` is a bijection between items and the byte strings that `decode` accepts.

- Every item that has an encoding decodes back from it.
- Every input that decodes is the encoding of what it decodes to. -/
theorem decode_eq_ok_iff (b : ByteArray) (x : Item) : decode b = .ok x ↔ encode x = .ok b :=
  ⟨encode_decode b x, decode_encode x b⟩

/-- What the parser reads from the front of an input is encoded as exactly the bytes it consumed.

This is the right-inverse property of Coglio's parser, `rlp-encode-tree-of-rlp-parse-tree`. -/
theorem encode_of_decodeItem (input rest : List UInt8) (x : Item) (hRest : rest.length < input.length)
    (h : decodeItem input = .ok (x, ⟨rest, hRest⟩)) :
    ∃ e, encode x = .ok e ∧ input = e.data.toList ++ rest :=
  (canonical_upTo input.length).1 input (Nat.le_refl _) x rest (by simp [readItem, h, Except.map])

/-- The parser reads the same item from a longer input, and leaves the extra bytes after the rest.

So a decoder that reads a stream needs no end marker. -/
theorem decodeItem_append (input rest more : List UInt8) (x : Item) (hRest : rest.length < input.length)
    (h : decodeItem input = .ok (x, ⟨rest, hRest⟩)) :
    ∃ hMore, decodeItem (input ++ more) = .ok (x, ⟨rest ++ more, hMore⟩) := by
  -- The input is an encoding of `x`, then the rest, so the longer input is that encoding, then `rest ++ more`.
  obtain ⟨e, hEncode, hInput⟩ := encode_of_decodeItem input rest x hRest h
  rw [hInput, List.append_assoc]
  exact decodeItem_encode x e hEncode (rest ++ more)

/-- The byte strings that encode some item: the image of `encode`.

This is `rlp-tree-encoding-p` of Coglio, Figure 4. -/
def IsEncoding (b : ByteArray) : Prop :=
  ∃ x, encode x = .ok b

/-- `decode` succeeds exactly on the encodings of items.

With `decode_eq_ok_iff`, it is the declarative decoder of Coglio, Figure 6: the inverse of `encode` on its image. -/
theorem decode_isOk_iff (b : ByteArray) : (∃ x, decode b = .ok x) ↔ IsEncoding b := by
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x, encode_decode b x h⟩
  · rintro ⟨x, h⟩
    exact ⟨x, decode_encode x b h⟩

end EthLib.Serialization.Rlp
