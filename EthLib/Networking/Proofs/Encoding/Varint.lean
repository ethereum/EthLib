import EthLib.Networking.Encoding.Varint

/-!
# `Networking.Proofs.Encoding.Varint`

Properties of the unsigned protobuf varint codec.

The two a reader cares about are that decoding undoes encoding for every
`UInt64`, and that an encoding never exceeds the ten bytes the
specification allows. Both are proved for every value rather than sampled.

Everything here is checked by the kernel: the known answers reduce by
`rfl`, so no `native_decide` or `bv_decide` axiom appears.
-/

namespace EthLib.Networking.Proofs.Encoding.Varint

open EthLib.Networking.Encoding.Varint

/-! ## The constants as literals

`omega` reasons about `%` and `/` by numerals, so the three constants are
restated as the numbers they are. -/

/-- The radix is `128`. -/
theorem groupSize_eq : groupSize = 128 := rfl

/-- The continuation bit's value is `128`, the same number. -/
theorem continuation_eq : continuation = 128 := rfl

/-- A byte holds `256` values. -/
theorem uint8_size : (2 : Nat) ^ 8 = 256 := rfl

/-! ## Reading a byte back

A continued byte holds its group plus `continuation`, which stays below
`256`, so `UInt8.ofNat` does not wrap and the group survives `% groupSize`.
-/

/-- A continued byte reads back as the group it was built from. -/
theorem toNat_continued_byte (n : Nat) :
    (UInt8.ofNat (n % groupSize + continuation)).toNat = n % groupSize + continuation := by
  have h : n % groupSize < groupSize := Nat.mod_lt _ (by decide)
  rw [UInt8.toNat_ofNat']
  rw [groupSize_eq, continuation_eq] at *
  omega

/-- A terminator byte reads back as itself. -/
theorem toNat_terminator_byte {n : Nat} (h : n < groupSize) :
    (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat']
  rw [groupSize_eq] at *
  omega

/-! ## Length -/

/-- An encoding uses at most one byte per unit of fuel. -/
theorem length_encodeAux_le (n fuel : Nat) : (encodeAux n fuel).length ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [encodeAux]
  | succ fuel ih =>
      rw [encodeAux]
      split
      · simp
      · simpa using ih (n / groupSize)

/-- Every varint fits in the ten bytes the specification allows. -/
theorem encode_length_le (v : UInt64) : (encode v).length ≤ maxLength :=
  length_encodeAux_le _ _

/-! ## Non-emptiness -/

/-- Any fuel at all writes at least one byte: both branches emit one. -/
theorem encodeAux_ne_nil {n fuel : Nat} (hf : 0 < fuel) : encodeAux n fuel ≠ [] := by
  cases fuel with
  | zero => omega
  | succ fuel => rw [encodeAux]; split <;> simp

/-! ## The value the groups denote -/

/-- Decoding the groups of `n` recovers `n`, as long as they fit in `fuel`
bytes. -/
theorem valueOf_encodeAux {n fuel : Nat} (h : n < groupSize ^ fuel) :
    valueOf (encodeAux n fuel) = n := by
  induction fuel generalizing n with
  | zero => simp [Nat.pow_zero] at h; simp [encodeAux, valueOf, h]
  | succ fuel ih =>
      rw [encodeAux]
      split
      · rename_i hlt
        rw [valueOf, valueOf, toNat_terminator_byte hlt]
        have : n % groupSize = n := Nat.mod_eq_of_lt hlt
        omega
      · rename_i hge
        have hdiv : n / groupSize < groupSize ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm] at h
          exact Nat.div_lt_of_lt_mul h
        rw [valueOf, toNat_continued_byte, ih hdiv]
        rw [groupSize_eq, continuation_eq]
        omega

/-! ## Shape -/

/-- The bytes of an encoding pass the shape check unchanged: every byte but
the last carries its continuation bit, and the last does not. -/
theorem groups_encodeAux {n fuel : Nat} (hfuel : 0 < fuel) (hf : n < groupSize ^ fuel) :
    groups (encodeAux n fuel) = .ok (encodeAux n fuel) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      rw [encodeAux]
      split
      · rename_i hlt
        rw [groups]
        rw [if_pos]
        rw [toNat_terminator_byte hlt, continuation_eq]
        rw [groupSize_eq] at hlt
        omega
      · rename_i hge
        have hdiv : n / groupSize < groupSize ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm] at hf
          exact Nat.div_lt_of_lt_mul hf
        -- Ten groups span more than one byte's worth, so there is fuel left.
        have hfuel' : 0 < fuel := by
          rcases Nat.eq_zero_or_pos fuel with h | h
          · subst h; rw [Nat.pow_one] at hf; omega
          · exact h
        have hne : encodeAux (n / groupSize) fuel ≠ [] := encodeAux_ne_nil hfuel'
        have hbit : ¬ (UInt8.ofNat (n % groupSize + continuation)).toNat < continuation := by
          rw [toNat_continued_byte, continuation_eq]; omega
        cases hcons : encodeAux (n / groupSize) fuel with
        | nil => exact absurd hcons hne
        | cons c cs =>
            have hih : groups (c :: cs) = .ok (c :: cs) := by
              rw [← hcons]; exact ih hfuel' hdiv
            rw [groups, if_neg hbit, hih]
            · rfl
            · simp

/-! ## Minimality

The canonical encoding never ends in a group of zero. The last byte is the
value that remained when it had fallen below `groupSize`, and each
continued step divided by `groupSize` only because the value was at least
that, so what remains is never zero.
-/

/-- A non-zero value's encoding does not end in a zero group. -/
theorem getLast?_encodeAux_ne_zero {n fuel : Nat} (hn : 0 < n) (hf : n < groupSize ^ fuel) :
    (encodeAux n fuel).getLast? ≠ some 0 := by
  induction fuel generalizing n with
  | zero => rw [Nat.pow_zero] at hf; omega
  | succ fuel ih =>
      rw [encodeAux]
      split
      · rename_i hlt
        simp only [List.getLast?_singleton, ne_eq, Option.some.injEq]
        intro h
        have := toNat_terminator_byte hlt
        rw [h] at this
        simp only [UInt8.toNat_zero] at this
        omega
      · rename_i hge
        have hdiv : n / groupSize < groupSize ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm] at hf
          exact Nat.div_lt_of_lt_mul hf
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

/-- No varint this codec produces is a padded encoding. -/
theorem nonMinimal_encode (v : UInt64) : nonMinimal (encode v) = false := by
  rcases Nat.eq_zero_or_pos v.toNat with h | h
  · -- Zero takes a single byte, and one byte is always minimal.
    rw [encode, h]
    rfl
  · have hlt : v.toNat < groupSize ^ maxLength := by
      have := v.toNat_lt_size
      simp only [UInt64.size, groupSize, payloadBits, maxLength] at *
      omega
    simp only [nonMinimal, Bool.and_eq_false_iff]
    exact Or.inr (by
      have := getLast?_encodeAux_ne_zero h hlt
      simpa [encode] using this)

/-! ## The round trip -/

/-- Decoding an encoded value returns it. Proved for every `UInt64`. -/
theorem decode_encode (v : UInt64) : decode (encode v) = .ok v := by
  have hlt : v.toNat < groupSize ^ maxLength := by
    have := v.toNat_lt_size
    simp only [UInt64.size, groupSize, payloadBits, maxLength] at *
    omega
  have hg : groups (encode v) = .ok (encode v) :=
    groups_encodeAux (by decide) hlt
  have hv : valueOf (encode v) = v.toNat := valueOf_encodeAux hlt
  have hlen : ¬ maxLength < (encode v).length := Nat.not_lt.mpr (encode_length_le v)
  rw [decode, hg]
  dsimp only
  rw [if_neg hlen, if_neg (by simp [nonMinimal_encode]),
    if_neg (by rw [hv]; have := v.toNat_lt_size; simp only [UInt64.size] at *; omega), hv]
  rw [UInt64.ofNat_toNat]

/-! ## Known answers

The values the issue and the specification name. Each reduces in the
kernel, so `rfl` closes it and no generated axiom appears.
-/

/-- The specification's own example. -/
example : encode 300 = [0xac, 0x02] := rfl

example : encode 0 = [0x00] := rfl
example : encode 1 = [0x01] := rfl
example : encode 127 = [0x7f] := rfl
example : encode 128 = [0x80, 0x01] := rfl

/-- The largest `UInt64` needs all ten bytes. -/
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
    .error (.tooLong 11) := rfl

/-- `2 ^ 64` is one past the range, and still inside ten bytes. -/
example : decode [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02] =
    .error .overflow := rfl

/-- `80 00` is a padded encoding of zero. -/
example : decode [0x80, 0x00] = .error .nonMinimal := rfl

/-- A continuation bit with nothing after it. -/
example : decode [0x80] = .error .unterminated := rfl

/-- No bytes at all. -/
example : decode [] = .error .unterminated := rfl

/-- A terminator followed by more bytes is not a whole-input varint. -/
example : decode [0x00, 0x00] = .error .trailingBytes := rfl

end EthLib.Networking.Proofs.Encoding.Varint
