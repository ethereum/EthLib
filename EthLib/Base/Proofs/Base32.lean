module

public import EthLib.Base.Base32
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: base32 is a bijection between byte strings and accepted texts

The decoder undoes the encoder, so every byte string reads back from its text.

The encoder writes back every text that the decoder accepts, so each byte string has one text.

Both hold group by group.

A group and the number that its characters write determine each other.
-/

@[expose] public section

namespace EthLib.Base.Base32

/-! ## Characters and numbers -/

/-- Every five-bit value reads back from its character. -/
theorem decodeQuint_encodeQuint : ∀ v : Fin 32, decodeQuint (encodeQuint v) = some v.val := by
  decide

/-- A character that reads as a value is the character of that value. -/
theorem encodeQuint_of_decodeQuint {c : Char} {v : Nat} (h : decodeQuint c = some v) :
    v < 32 ∧ encodeQuint v = c := by
  unfold decodeQuint at h
  have hc : Char.ofNat c.toNat = c := Char.ofNat_toNat c
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeQuint, show c.toNat - 65 < 26 by omega, ↓reduceIte]
    rw [show 65 + (c.toNat - 65) = c.toNat by omega, hc]
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeQuint, show ¬ c.toNat - 50 + 26 < 26 by omega, ↓reduceIte]
    rw [show 50 + (c.toNat - 50 + 26 - 26) = c.toNat by omega, hc]
  · cases h

/-- A number has `count` characters. -/
theorem length_digits : (count n : Nat) → (digits count n).length = count
  | 0, _ => rfl
  | count + 1, n => by simp [digits, length_digits count n]

/-- The characters of a number read back as its remainder by `32 ^ count`, after `acc`. -/
theorem value_digits {start acc : Nat} :
    (count n : Nat) → value start acc (digits count n) = .ok (acc * 32 ^ count + n % 32 ^ count)
  | 0, n => by simp [digits, value, pure, Except.pure, Nat.mod_one]
  | count + 1, n => by
    have hv : n / 32 ^ count % 32 < 32 := Nat.mod_lt _ (by decide)
    simp only [digits, value, decodeQuint_encodeQuint ⟨_, hv⟩, value_digits count n]
    congr 1
    rw [Nat.mod_pow_succ, Nat.pow_succ]
    grind

/-- The characters that read as a number are the characters of that number.

The number divided by `32 ^ length` is what came before them. -/
theorem digits_of_value {start acc n : Nat} :
    (cs : List Char) → value start acc cs = .ok n →
      digits cs.length n = cs ∧ n / 32 ^ cs.length = acc
  | [], h => by
    simp only [value, pure, Except.pure, Except.ok.injEq] at h
    simp [digits, h]
  | c :: rest, h => by
    simp only [value] at h
    split at h
    · rename_i v hv
      obtain ⟨small, char⟩ := encodeQuint_of_decodeQuint hv
      obtain ⟨rest_digits, high⟩ := digits_of_value rest h
      refine ⟨?_, ?_⟩
      · -- The first character is the digit that follows the earlier ones.
        simp only [List.length_cons, digits, high, rest_digits]
        rw [show (acc * 32 + v) % 32 = v by omega, char]
      · simp only [List.length_cons, Nat.pow_succ, ← Nat.div_div_eq_div_mul, high]
        omega
    · cases h

/-! ## One group -/

/-- The sizes of a group that the decoder accepts, by its number of characters. -/
theorem byteCount_charCount {size : Nat} (h : size ≤ 5) :
    byteCount (charCount size) = some size := by
  have : size = 0 ∨ size = 1 ∨ size = 2 ∨ size = 3 ∨ size = 4 ∨ size = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A count of characters that the decoder accepts is the count of a group of at most five bytes. -/
theorem charCount_of_byteCount {count size : Nat} (h : byteCount count = some size) :
    charCount size = count ∧ size ≤ 5 := by
  unfold byteCount at h
  split at h <;> cases h <;> decide

/-- The bits of a group, with the zero bits after them, fit its characters. -/
theorem pow_charCount (size : Nat) (h : size ≤ 5) :
    256 ^ size * 2 ^ (5 * charCount size - 8 * size) = 32 ^ charCount size := by
  have : size = 0 ∨ size = 1 ∨ size = 2 ∨ size = 3 ∨ size = 4 ∨ size = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The decoder undoes the encoder on a group of at most five bytes. -/
theorem decodeGroup_encodeGroup (start : Nat) {group : List UInt8} (h : group.length ≤ 5) :
    decodeGroup start (encodeGroup group) = .ok group := by
  have bound := bytesToNat_lt group
  have fits := pow_charCount group.length h
  generalize hpad : 5 * charCount group.length - 8 * group.length = pad at fits
  have positive : 0 < 2 ^ pad := Nat.two_pow_pos pad
  -- The number of the group is below `32 ^ count`, so its characters read it back whole.
  have below : bytesToNat group * 2 ^ pad < 32 ^ charCount group.length := by
    rw [← fits]
    exact Nat.mul_lt_mul_of_pos_right bound positive
  simp only [decodeGroup, encodeGroup, length_digits, byteCount_charCount h, hpad,
    value_digits, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt below, Nat.mul_mod_left,
    Nat.mul_div_cancel _ positive, natToBytes_bytesToNat, bind, Except.bind, pure, Except.pure]
  rfl

/-- The encoder writes back a group that the decoder accepts. -/
theorem encodeGroup_of_decodeGroup {start : Nat} {cs : List Char} {group : List UInt8}
    (h : decodeGroup start cs = .ok group) : encodeGroup group = cs := by
  unfold decodeGroup at h
  cases hsize : byteCount cs.length with
  | none => simp [hsize, throw, throwThe, MonadExceptOf.throw] at h
  | some size =>
  cases hv : value start 0 cs with
  | error e => simp [hsize, hv, bind, Except.bind] at h
  | ok n =>
  -- Nonzero unused bits are rejected.
  have zero : n % 2 ^ (5 * cs.length - 8 * size) = 0 := Decidable.byContradiction fun z => by
    simp [hsize, hv, z, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hsize, hv, zero, bind, Except.bind, ↓reduceIte, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  obtain ⟨count, small⟩ := charCount_of_byteCount hsize
  obtain ⟨chars, high⟩ := digits_of_value cs hv
  have fits := pow_charCount size small
  rw [count] at fits
  generalize hpad : 5 * cs.length - 8 * size = pad at fits zero
  have positive : 0 < 2 ^ pad := Nat.two_pow_pos pad
  -- The number is below `32 ^ count`, so the bytes of its high bits hold all of it.
  have below : n < 32 ^ cs.length := by
    have := Nat.div_add_mod n (32 ^ cs.length)
    rw [high] at this
    have := Nat.mod_lt n (Nat.pow_pos (n := cs.length) (by decide : 0 < 32))
    omega
  have quotient : n / 2 ^ pad < 256 ^ size := by
    rw [Nat.div_lt_iff_lt_mul positive, fits]
    exact below
  have whole : n / 2 ^ pad * 2 ^ pad = n := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero zero)
  simp only [encodeGroup, natToBytes_length, count, hpad, bytesToNat_natToBytes_of_lt quotient,
    whole, chars]

/-- A group that the decoder accepts has the size that its number of characters gives. -/
theorem byteCount_of_decodeGroup {start : Nat} {cs : List Char} {group : List UInt8}
    (h : decodeGroup start cs = .ok group) : byteCount cs.length = some group.length := by
  unfold decodeGroup at h
  cases hsize : byteCount cs.length with
  | none => simp [hsize, throw, throwThe, MonadExceptOf.throw] at h
  | some size =>
  cases hv : value start 0 cs with
  | error e => simp [hsize, hv, bind, Except.bind] at h
  | ok n =>
  have zero : n % 2 ^ (5 * cs.length - 8 * size) = 0 := Decidable.byContradiction fun z => by
    simp [hsize, hv, z, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hsize, hv, zero, bind, Except.bind, ↓reduceIte, pure, Except.pure,
    Except.ok.injEq] at h
  rw [← h, natToBytes_length]

/-! ## Whole texts -/

/-- A group has as many characters as its size gives. -/
theorem length_encodeGroup (group : List UInt8) :
    (encodeGroup group).length = charCount group.length := by
  simp [encodeGroup, length_digits]

/-- A list of at most five bytes is one group. -/
theorem encodeList_of_length_le {bytes : List UInt8} (h : bytes.length ≤ 5) :
    encodeList bytes = encodeGroup bytes := by
  unfold encodeList
  split
  · rename_i b0 b1 b2 b3 b4 rest
    -- Five bytes and nothing after them: the empty rest has no characters.
    cases rest with
    | nil => simp [encodeList, encodeGroup, charCount, digits]
    | cons _ _ => simp at h
  · rfl

/-- A byte string has its bits in characters, five bits each, rounded up. -/
theorem length_encodeList :
    (bytes : List UInt8) → (encodeList bytes).length = charCount bytes.length
  | _ :: _ :: _ :: _ :: _ :: rest => by
    simp only [encodeList, List.length_append, length_encodeGroup, length_encodeList rest,
      List.length_cons, List.length_nil, charCount]
    omega
  | [] => by rw [encodeList_of_length_le (by simp), length_encodeGroup]
  | [_] => by rw [encodeList_of_length_le (by simp), length_encodeGroup]
  | [_, _] => by rw [encodeList_of_length_le (by simp), length_encodeGroup]
  | [_, _, _] => by rw [encodeList_of_length_le (by simp), length_encodeGroup]
  | [_, _, _, _] => by rw [encodeList_of_length_le (by simp), length_encodeGroup]

/-- A list of fewer than eight characters is one group. -/
theorem decodeList_of_length_lt {start : Nat} {cs : List Char} (h : cs.length < 8) :
    decodeList start cs = decodeGroup start cs := by
  unfold decodeList
  split
  · simp at h
    omega
  · rfl

/-- The decoder undoes the encoder, five bytes at a time. -/
theorem decodeList_encodeList : (start : Nat) → (bytes : List UInt8) →
    decodeList start (encodeList bytes) = .ok bytes
  | start, b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    -- The group of five bytes is eight characters, written out.
    have group := decodeGroup_encodeGroup start (group := [b0, b1, b2, b3, b4]) (by simp)
    have tail := decodeList_encodeList (start + 8) rest
    simp only [encodeGroup, List.length_cons, List.length_nil, charCount, digits] at group
    simp only [encodeList, encodeGroup, List.length_cons, List.length_nil, charCount, digits,
      List.cons_append, List.nil_append, decodeList, group, tail, bind, Except.bind, pure,
      Except.pure]
  | start, [] => by
    rw [encodeList_of_length_le (by simp), decodeList_of_length_lt (by simp [length_encodeGroup,
      charCount]), decodeGroup_encodeGroup _ (by simp)]
  | start, [b0] => by
    rw [encodeList_of_length_le (by simp), decodeList_of_length_lt (by simp [length_encodeGroup,
      charCount]), decodeGroup_encodeGroup _ (by simp)]
  | start, [b0, b1] => by
    rw [encodeList_of_length_le (by simp), decodeList_of_length_lt (by simp [length_encodeGroup,
      charCount]), decodeGroup_encodeGroup _ (by simp)]
  | start, [b0, b1, b2] => by
    rw [encodeList_of_length_le (by simp), decodeList_of_length_lt (by simp [length_encodeGroup,
      charCount]), decodeGroup_encodeGroup _ (by simp)]
  | start, [b0, b1, b2, b3] => by
    rw [encodeList_of_length_le (by simp), decodeList_of_length_lt (by simp [length_encodeGroup,
      charCount]), decodeGroup_encodeGroup _ (by simp)]

/-- The decoder undoes the encoder: every byte string reads back from its text. -/
theorem decode_encode (bytes : ByteArray) : decode (encode bytes) = .ok bytes := by
  simp only [decode, encode, String.toList_ofList, decodeList_encodeList, bind, Except.bind,
    pure, Except.pure]

/-- The encoder writes back every list of characters that the decoder accepts. -/
theorem encodeList_of_decodeList {start : Nat} {cs : List Char} {bytes : List UInt8}
    (h : decodeList start cs = .ok bytes) : encodeList bytes = cs := by
  unfold decodeList at h
  split at h
  · rename_i c0 c1 c2 c3 c4 c5 c6 c7 rest
    cases hg : decodeGroup start [c0, c1, c2, c3, c4, c5, c6, c7] with
    | error e => simp [hg, bind, Except.bind] at h
    | ok group =>
    cases hr : decodeList (start + 8) rest with
    | error e => simp [hg, hr, bind, Except.bind] at h
    | ok tail =>
    simp only [hg, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    -- Eight characters are a group of five bytes.
    have five := byteCount_of_decodeGroup hg
    have back := encodeGroup_of_decodeGroup hg
    have tail := encodeList_of_decodeList hr
    rcases group with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, more⟩⟩⟩⟩⟩⟩ <;>
      simp [byteCount] at five
    simp only [List.cons_append, List.nil_append, encodeList, back, tail]
  · obtain ⟨_, small⟩ := charCount_of_byteCount (byteCount_of_decodeGroup h)
    rw [encodeList_of_length_le small, encodeGroup_of_decodeGroup h]
termination_by cs.length

/-- The encoder writes back every text that the decoder accepts, so each byte string has one text.
-/
theorem encode_of_decode {text : String} {bytes : ByteArray} (h : decode text = .ok bytes) :
    encode bytes = text := by
  simp only [decode, bind, Except.bind] at h
  cases hl : decodeList 0 text.toList with
  | error e => simp [hl] at h
  | ok list =>
    simp only [hl, pure, Except.pure, Except.ok.injEq] at h
    subst h
    apply String.toList_injective
    simp [encode, encodeList_of_decodeList hl]

end EthLib.Base.Base32
