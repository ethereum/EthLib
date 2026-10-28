import EthLib.Networking.Encoding.Varint

/-!
# `Networking.Proofs.Encoding.Varint`

Properties of the unsigned protobuf varint codec, proved for every 64-bit value.

- Decoding undoes encoding.
- An encoding never exceeds the ten bytes the specification allows.
- An encoding is always minimal.

The kernel checks everything here, so no `native_decide` or `bv_decide` axiom appears.
-/

namespace EthLib.Networking.Proofs.Encoding.Varint

open EthLib.Networking.Encoding.Varint

/-! ## The constants as numerals

`omega` handles `%` and `/` only by numerals, so the radix and the continuation bit are restated as 128.
-/

/-- The radix is 128. -/
theorem groupSize_eq : groupSize = 128 := rfl

/-- The continuation bit is worth 128, the same number as the radix. -/
theorem continuation_eq : continuation = 128 := rfl

/-! ## Reading a byte back

A continued byte holds its group plus 128, which stays below 256.

So the byte does not wrap, and the group survives.
-/

/-- A continued byte reads back as its group plus 128. -/
theorem toNat_continued_byte (n : Nat) :
    (UInt8.ofNat (n % groupSize + continuation)).toNat = n % groupSize + continuation := by
  -- The group is below 128, so the byte value is below 256.
  have h : n % groupSize < groupSize := Nat.mod_lt _ (by decide)
  rw [UInt8.toNat_ofNat']
  rw [groupSize_eq, continuation_eq] at *
  omega

/-- A last byte reads back as itself. -/
theorem toNat_terminator_byte {n : Nat} (h : n < groupSize) :
    (UInt8.ofNat n).toNat = n := by
  -- The value is below 128, so it fits in a byte unchanged.
  rw [UInt8.toNat_ofNat']
  rw [groupSize_eq] at *
  omega

/-! ## Length -/

/-- An encoding writes at most one byte per unit of budget. -/
theorem length_encodeAux_le (n fuel : Nat) : (encodeAux n fuel).length ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [encodeAux]
  | succ fuel ih =>
      rw [encodeAux]
      split
      -- A last byte: one byte.
      · simp
      -- A continued byte, then at most the remaining budget.
      · simpa using ih (n / groupSize)

/-- Every varint fits in the ten bytes the specification allows. -/
theorem encode_length_le (v : UInt64) : (encode v).length ≤ maxLength :=
  length_encodeAux_le _ _

/-! ## Non-emptiness -/

/-- A positive budget writes at least one byte. -/
theorem encodeAux_ne_nil {n fuel : Nat} (hf : 0 < fuel) : encodeAux n fuel ≠ [] := by
  cases fuel with
  | zero => omega
  -- Both branches start with a byte.
  | succ fuel => rw [encodeAux]; split <;> simp

/-! ## The value the groups denote -/

/-- Reading the groups of `n` back gives `n`, when `n` fits in the budget.

A budget of k bytes holds values below 128^k.
-/
theorem valueOf_encodeAux {n fuel : Nat} (h : n < groupSize ^ fuel) :
    valueOf (encodeAux n fuel) = n := by
  induction fuel generalizing n with
  -- No budget: only n = 0 fits, and it denotes the empty list.
  | zero => simp [Nat.pow_zero] at h; simp [encodeAux, valueOf, h]
  | succ fuel ih =>
      rw [encodeAux]
      split
      -- A last byte holds n itself.
      · rename_i hlt
        rw [valueOf, valueOf, toNat_terminator_byte hlt]
        have : n % groupSize = n := Nat.mod_eq_of_lt hlt
        omega
      -- A continued byte holds n mod 128, and the rest holds n / 128.
      --
      --     n = (n mod 128) + 128 * (n / 128)
      · rename_i hge
        -- The quotient fits in one byte less of budget.
        have hdiv : n / groupSize < groupSize ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm] at h
          exact Nat.div_lt_of_lt_mul h
        rw [valueOf, toNat_continued_byte, ih hdiv]
        rw [groupSize_eq, continuation_eq]
        omega

/-! ## Shape -/

/-- An encoding passes the shape check unchanged, read with the same budget it was written with. -/
theorem groups_encodeAux {n fuel : Nat} (hfuel : 0 < fuel) (hf : n < groupSize ^ fuel) :
    groups fuel (encodeAux n fuel) = .ok (encodeAux n fuel) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      rw [encodeAux]
      split
      -- A last byte with nothing after it is accepted as it is.
      · rename_i hlt
        rw [groups, ite_eq_left]
        rw [toNat_terminator_byte hlt, continuation_eq]
        rw [groupSize_eq] at hlt
        omega
      · rename_i hge
        -- The quotient fits in one byte less of budget.
        have hdiv : n / groupSize < groupSize ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm] at hf
          exact Nat.div_lt_of_lt_mul hf
        -- n is at least 128, so it needs a second byte, and the budget has one.
        have hfuel' : 0 < fuel := by
          rcases Nat.eq_zero_or_pos fuel with h | h
          · subst h; rw [Nat.pow_one] at hf; omega
          · exact h
        -- The first byte carries the continuation bit.
        have hbit : ¬ (UInt8.ofNat (n % groupSize + continuation)).toNat < continuation := by
          rw [toNat_continued_byte, continuation_eq]; omega
        -- So it is kept, and the rest passes by induction.
        simp only [groups, ite_eq_right hbit, ih hfuel' hdiv]
        rfl

/-! ## Minimality

The shortest encoding never ends in a zero group.

The last byte is what remained once the value fell below 128.

Each earlier step divided by 128 only because the value was at least 128.

So what remains is at least 1.
-/

/-- The encoding of a positive value does not end in a zero group. -/
theorem getLast?_encodeAux_ne_zero {n fuel : Nat} (hn : 0 < n) (hf : n < groupSize ^ fuel) :
    (encodeAux n fuel).getLast? ≠ some 0 := by
  induction fuel generalizing n with
  | zero => rw [Nat.pow_zero] at hf; omega
  | succ fuel ih =>
      rw [encodeAux]
      split
      -- A single last byte holds n, which is positive.
      · rename_i hlt
        simp only [List.getLast?_singleton, ne_eq, Option.some.injEq]
        intro h
        have := toNat_terminator_byte hlt
        rw [h] at this
        simp only [UInt8.toNat_zero] at this
        omega
      -- A continued byte: the last byte is the last byte of the rest.
      · rename_i hge
        have hdiv : n / groupSize < groupSize ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm] at hf
          exact Nat.div_lt_of_lt_mul hf
        -- n is at least 128, so n / 128 is at least 1.
        have hpos : 0 < n / groupSize := Nat.div_pos (Nat.le_of_not_lt hge) (by decide)
        have hfuel' : 0 < fuel := by
          rcases Nat.eq_zero_or_pos fuel with h | h
          · subst h; rw [Nat.pow_one] at hf; omega
          · exact h
        cases hcons : encodeAux (n / groupSize) fuel with
        | nil => exact absurd hcons (encodeAux_ne_nil hfuel')
        | cons c cs =>
            rw [List.getLast?_cons_cons, ← hcons]
            exact ih hpos hdiv

/-- No varint this codec writes is padded. -/
theorem nonMinimal_encode (v : UInt64) : nonMinimal (encode v) = false := by
  rcases Nat.eq_zero_or_pos v.toNat with h | h
  -- Zero takes a single byte, and one byte is always minimal.
  · rw [encode, h]
    rfl
  -- A positive value: its encoding does not end in a zero group.
  · have hlt : v.toNat < groupSize ^ maxLength := by
      have := v.toNat_lt_size
      simp only [UInt64.size, groupSize, payloadBits, maxLength] at *
      omega
    simp only [nonMinimal, Bool.and_eq_false_iff]
    exact Or.inr (by
      have := getLast?_encodeAux_ne_zero h hlt
      simpa [encode] using this)

/-! ## The round trip -/

/-- Decoding an encoded value returns it, for every 64-bit value. -/
theorem decode_encode (v : UInt64) : decode (encode v) = .ok v := by
  -- Every 64-bit value is below 2^64 < 128^10, so it fits in the ten-byte budget.
  have hlt : v.toNat < groupSize ^ maxLength := by
    have := v.toNat_lt_size
    simp only [UInt64.size, groupSize, payloadBits, maxLength] at *
    omega
  -- The shape check accepts the encoding.
  have hg : groups maxLength (encode v) = .ok (encode v) :=
    groups_encodeAux (by decide) hlt
  -- The encoding denotes the value.
  have hv : valueOf (encode v) = v.toNat := valueOf_encodeAux hlt
  rw [decode, hg]
  dsimp only
  -- Minimal, and inside the 64-bit range.
  rw [ite_eq_right (by simp [nonMinimal_encode]),
    ite_eq_right (by rw [hv]; have := v.toNat_lt_size; simp only [UInt64.size] at *; omega), hv]
  rw [UInt64.ofNat_toNat]

/-! ## Known answers

Each one reduces in the kernel, so `rfl` closes it.
-/

/-- The worked example of the protobuf encoding guide: 150 is `96 01`. -/
example : encode 150 = [0x96, 0x01] := rfl

/-- The same example, decoded. -/
example : decode [0x96, 0x01] = .ok 150 := rfl

/-- The edges of one and two bytes: 0, 1, 127 = 2^7 - 1, and 128 = 2^7. -/
example : encode 0 = [0x00] := rfl
example : encode 1 = [0x01] := rfl
example : encode 127 = [0x7f] := rfl
example : encode 128 = [0x80, 0x01] := rfl

/-- One two-byte value, 300, traced in the module header. -/
example : encode 300 = [0xac, 0x02] := rfl

/-- The largest 64-bit value needs all ten bytes. -/
example : encode 18446744073709551615 =
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01] := rfl

example : decode [0x00] = .ok 0 := rfl
example : decode [0x01] = .ok 1 := rfl
example : decode [0x7f] = .ok 127 := rfl
example : decode [0x80, 0x01] = .ok 128 := rfl
example : decode [0xac, 0x02] = .ok 300 := rfl
example : decode [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01] =
    .ok 18446744073709551615 := rfl

/-! ## Rejected inputs -/

/-- Eleven bytes exceed the cap. -/
example : decode [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01] =
    .error .tooLong := rfl

/-- A megabyte of continuation bytes is rejected at byte eleven, without reading the rest. -/
example : decode (List.replicate 1048576 0x80 ++ [0x01]) = .error .tooLong := rfl

/-- 2^64 is one past the range, and still fits in ten bytes. -/
example : decode [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02] =
    .error .overflow := rfl

/-- `80 00` is zero padded with an extra zero group. -/
example : decode [0x80, 0x00] = .error .nonMinimal := rfl

/-- A continuation bit with nothing after it. -/
example : decode [0x80] = .error .unterminated := rfl

/-- No bytes at all. -/
example : decode [] = .error .unterminated := rfl

/-- A last byte followed by more bytes. -/
example : decode [0x00, 0x00] = .error .trailingBytes := rfl

end EthLib.Networking.Proofs.Encoding.Varint
