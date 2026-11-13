module

public import EthLib.Serialization.Proofs.Rlp.Encode

/-!
# `Serialization.Proofs.Rlp.Bound`

Exactly when the encoding fails.

The Yellow Paper gives no encoding to a payload of `2^64` bytes or more.

A byte string encodes exactly when it has fewer than `2^64` bytes.

A list whose items encode, encodes exactly when their encodings total fewer than `2^64` bytes.

A list fails when one of its items fails.

So the encoding fails exactly where the Yellow Paper gives no encoding, at some node of the tree.

An encoding is at most 9 bytes longer than its payload, and 1 byte longer below 56 bytes.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- Every length below `2^64` has a prefix. -/
theorem lengthPrefix_ok (kind : PayloadKind) (length : Nat) (h : length < 2 ^ 64) :
    ∃ pre, lengthPrefix kind length = .ok pre := by
  unfold lengthPrefix
  by_cases hShort : length < 56
  · exact ⟨_, by rw [ite_eq_left hShort]⟩
  · rw [ite_eq_right hShort, ite_eq_left h]
    exact ⟨_, rfl⟩

/-- A prefix that exists has at most 9 bytes, and 1 byte when the length is below 56. -/
theorem lengthPrefix_size_le (kind : PayloadKind) (length : Nat) (pre : ByteArray)
    (h : lengthPrefix kind length = .ok pre) :
    pre.size ≤ 9 ∧ (length < 56 → pre.size = 1) := by
  unfold lengthPrefix at h
  by_cases hShort : length < 56
  · rw [ite_eq_left hShort] at h
    cases h
    exact ⟨by simp [ByteArray.size], fun _ => by simp [ByteArray.size]⟩
  · rw [ite_eq_right hShort] at h
    by_cases hLong : length < 2 ^ 64
    · rw [ite_eq_left hLong] at h
      cases h
      have := bigEndian_size_le length 8 (by simpa using hLong)
      refine ⟨?_, fun hs => absurd hs hShort⟩
      simp only [ByteArray.size_append]
      have h1 : ∀ b : UInt8, (ByteArray.mk #[b]).size = 1 := fun _ => rfl
      rw [h1]
      omega
    · rw [ite_eq_right hLong] at h
      cases h

/-- A byte string encodes to at most 9 more bytes, and at most 1 more when it has under 56. -/
theorem encode_bytes_size_le (data e : ByteArray) (h : encode (.bytes data) = .ok e) :
    e.size ≤ data.size + 9 ∧ (data.size < 56 → e.size ≤ data.size + 1) := by
  rw [encode, encodeBytes] at h
  cases hSingle : isSingleLowByte data
  · cases hPre : lengthPrefix .bytes data.size with
    | error err => simp [hSingle, hPre, bind, Except.bind] at h
    | ok pre =>
      simp [hSingle, hPre, bind, Except.bind, pure, Except.pure] at h
      subst h
      obtain ⟨h9, h1⟩ := lengthPrefix_size_le _ _ _ hPre
      refine ⟨by simp only [ByteArray.size_append]; omega, fun hs => ?_⟩
      have := h1 hs
      simp only [ByteArray.size_append]; omega
  · simp [hSingle] at h
    subst h
    exact ⟨by omega, fun _ => by omega⟩

/-- The encodings of items that are each at most `c` bytes join to at most `c` bytes per item. -/
theorem joinEncodings_size_le (c : Nat) :
    (items : List Item) → (payload : ByteArray) →
    (∀ i ∈ items, ∀ e, encode i = .ok e → e.size ≤ c) →
    joinEncodings items = .ok payload → payload.size ≤ c * items.length
  | [], payload, _, h => by
    simp [joinEncodings] at h
    subst h
    simp [ByteArray.size]
  | x :: xs, payload, hc, h => by
    rw [joinEncodings_cons] at h
    cases hHead : encode x with
    | error e => simp [hHead, bind, Except.bind] at h
    | ok head =>
      cases hTail : joinEncodings xs with
      | error e => simp [hHead, hTail, bind, Except.bind] at h
      | ok tail =>
        simp [hHead, hTail, bind, Except.bind, pure, Except.pure] at h
        subst h
        have h1 := hc x (by simp) head hHead
        have h2 := joinEncodings_size_le c xs tail
          (fun i hi => hc i (List.mem_cons_of_mem _ hi)) hTail
        simp only [ByteArray.size_append, List.length_cons]
        rw [Nat.mul_succ]; omega

/-- When every item encodes, joining their encodings succeeds. -/
theorem joinEncodings_ok :
    (items : List Item) → (∀ i ∈ items, ∃ e, encode i = .ok e) →
    ∃ payload, joinEncodings items = .ok payload
  | [], _ => ⟨.empty, rfl⟩
  | x :: xs, hc => by
    obtain ⟨head, hHead⟩ := hc x (by simp)
    obtain ⟨tail, hTail⟩ := joinEncodings_ok xs (fun i hi => hc i (List.mem_cons_of_mem _ hi))
    exact ⟨head ++ tail, by
      rw [joinEncodings_cons]; simp [hHead, hTail, bind, Except.bind, pure, Except.pure]⟩

/-- The encoding of a list is at most 9 bytes longer than the joined encodings of its items. -/
theorem encode_list_size_le (items : List Item) (payload e : ByteArray)
    (hJoin : joinEncodings items = .ok payload) (h : encode (.list items) = .ok e) :
    e.size ≤ payload.size + 9 := by
  cases hPre : lengthPrefix .list payload.size with
  | error err => simp [encode, hJoin, hPre, bind, Except.bind] at h
  | ok pre =>
    simp [encode, hJoin, hPre, bind, Except.bind, pure, Except.pure] at h
    subst h
    have := (lengthPrefix_size_le _ _ _ hPre).1
    simp only [ByteArray.size_append]; omega

/-- The prefix of a length fails only on a length of `2^64` or more. -/
theorem lengthPrefix_error (kind : PayloadKind) (length : Nat) (err : RlpError)
    (h : lengthPrefix kind length = .error err) : err = .payloadTooLong length ∧ 2 ^ 64 ≤ length := by
  by_cases hLong : length < 2 ^ 64
  · obtain ⟨pre, hPre⟩ := lengthPrefix_ok kind length hLong
    rw [hPre] at h
    cases h
  · rw [lengthPrefix_too_long kind length (by omega)] at h
    cases h
    exact ⟨rfl, by omega⟩

/-- A byte string encodes exactly when it has fewer than `2^64` bytes. -/
theorem encode_bytes_succeeds_iff (data : ByteArray) :
    (∃ e, encode (.bytes data) = .ok e) ↔ data.size < 2 ^ 64 := by
  constructor
  · rintro ⟨e, h⟩
    apply Nat.lt_of_not_le
    intro hLong
    rw [encode_bytes_too_long data hLong] at h
    cases h
  · intro h
    rw [encode, encodeBytes]
    cases hSingle : isSingleLowByte data
    · -- A prefix exists below `2^64`, then the bytes follow it.
      obtain ⟨pre, hPre⟩ := lengthPrefix_ok .bytes data.size h
      exact ⟨pre ++ data, by simp [hPre, bind, Except.bind, pure, Except.pure]⟩
    · exact ⟨data, by simp⟩

/-- A list whose items encode to `payload` encodes exactly when `payload` has under `2^64` bytes. -/
theorem encode_list_succeeds_iff (items : List Item) (payload : ByteArray)
    (hJoin : joinEncodings items = .ok payload) :
    (∃ e, encode (.list items) = .ok e) ↔ payload.size < 2 ^ 64 := by
  constructor
  · rintro ⟨e, h⟩
    apply Nat.lt_of_not_le
    intro hLong
    rw [encode_list_too_long items payload hJoin hLong] at h
    cases h
  · intro h
    obtain ⟨pre, hPre⟩ := lengthPrefix_ok .list payload.size h
    exact ⟨pre ++ payload, by simp [encode, hJoin, hPre, bind, Except.bind, pure, Except.pure]⟩

/-- A list fails, with the same error, when one of its items fails. -/
theorem encode_list_of_joinEncodings_error (items : List Item) (err : RlpError)
    (h : joinEncodings items = .error err) : encode (.list items) = .error err := by
  simp [encode, h, bind, Except.bind]

mutual

/-- The only failure of `encode` is a payload of `2^64` bytes or more. -/
theorem encode_error : (x : Item) → (err : RlpError) → encode x = .error err →
    ∃ length, err = .payloadTooLong length ∧ 2 ^ 64 ≤ length
  | .bytes data, err, h => by
    rw [encode, encodeBytes] at h
    cases hSingle : isSingleLowByte data
    · -- Only the prefix can fail.
      cases hPre : lengthPrefix .bytes data.size with
      | error e =>
        simp [hSingle, hPre, bind, Except.bind] at h
        subst h
        exact ⟨_, lengthPrefix_error _ _ _ hPre⟩
      | ok pre => simp [hSingle, hPre, bind, Except.bind, pure, Except.pure] at h
    · simp [hSingle] at h
  | .list items, err, h => by
    cases hJoin : joinEncodings items with
    | error e =>
      -- An item failed first.
      rw [encode_list_of_joinEncodings_error items e hJoin] at h
      injection h with hErr
      subst hErr
      exact joinEncodings_error items e hJoin
    | ok payload =>
      -- The items encoded, so only the prefix of the list can fail.
      cases hPre : lengthPrefix .list payload.size with
      | error e =>
        simp [encode, hJoin, hPre, bind, Except.bind] at h
        subst h
        exact ⟨_, lengthPrefix_error _ _ _ hPre⟩
      | ok pre => simp [encode, hJoin, hPre, bind, Except.bind, pure, Except.pure] at h
termination_by structural x => x

/-- Joining the encodings of items fails only on a payload of `2^64` bytes or more in one item. -/
theorem joinEncodings_error : (xs : List Item) → (err : RlpError) → joinEncodings xs = .error err →
    ∃ length, err = .payloadTooLong length ∧ 2 ^ 64 ≤ length
  | [], err, h => by simp [joinEncodings] at h
  | x :: xs, err, h => by
    rw [joinEncodings_cons] at h
    cases hHead : encode x with
    | error e =>
      simp [hHead, bind, Except.bind] at h
      subst h
      exact encode_error x e hHead
    | ok head =>
      cases hTail : joinEncodings xs with
      | error e =>
        simp [hHead, hTail, bind, Except.bind] at h
        subst h
        exact joinEncodings_error xs e hTail
      | ok tail => simp [hHead, hTail, bind, Except.bind, pure, Except.pure] at h
termination_by structural xs => xs

end

end EthLib.Serialization.Rlp
