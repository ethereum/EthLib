import EthLib.Serialization.Proofs.Rlp.Encode

/-!
# `Serialization.Proofs.Rlp.Bound`

Exactly when the encoding fails.

The Yellow Paper gives no encoding to a payload of `2^64` bytes or more, and every other payload has one:

- `encode_bytes_succeeds_iff`: a byte string encodes exactly when it has fewer than `2^64` bytes;
- `encode_list_succeeds_iff`: a list whose items encode, encodes exactly when their encodings total fewer than `2^64` bytes;
- `encode_list_of_joinEncodings_error`: a list fails when one of its items fails;
- `encode_error`: the only failure is a payload of `2^64` bytes or more.

So `encode` fails exactly where the Yellow Paper gives no encoding, at some byte string or list of the tree.
-/

namespace EthLib.Serialization.Rlp

/-- Every length below `2^64` has a prefix. -/
theorem lengthPrefix_ok (kind : PayloadKind) (length : Nat) (h : length < 2 ^ 64) :
    ∃ pre, lengthPrefix kind length = .ok pre := by
  unfold lengthPrefix
  by_cases hShort : length < 56
  · exact ⟨_, by rw [ite_eq_left hShort]⟩
  · rw [ite_eq_right hShort, ite_eq_left h]
    exact ⟨_, rfl⟩

/-- Every failure of `lengthPrefix` is a length of `2^64` or more. -/
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

/-- A list whose items encode to `payload` encodes exactly when `payload` has fewer than `2^64` bytes. -/
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

/-- The only failure of `joinEncodings` is a payload of `2^64` bytes or more, in one of the items. -/
theorem joinEncodings_error : (xs : List Item) → (err : RlpError) → joinEncodings xs = .error err →
    ∃ length, err = .payloadTooLong length ∧ 2 ^ 64 ≤ length
  | [], err, h => by simp [joinEncodings] at h
  | x :: xs, err, h => by
    rw [joinEncodings] at h
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
