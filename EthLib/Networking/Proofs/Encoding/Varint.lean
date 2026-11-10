module

public import EthLib.Networking.Encoding.Varint

/-!
# `Networking.Proofs.Encoding.Varint`

Properties of the unsigned protobuf varint codec, proved for every 64-bit value and every input.

- Decoding undoes encoding.
- An encoding never exceeds the ten bytes the specification allows.
- An encoding is always minimal.
- The decoder accepts only these encodings, so exactly one byte string decodes to each value.
- An input is too long exactly when it has over ten bytes and the first ten are continued.
- Splitting an encoding from any bytes after it returns the encoding and those bytes.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Encoding.Varint

open EthLib.Networking.Encoding.Varint

/-! ## The constants as numerals

`omega` handles `%` and `/` only by numerals.

So the radix and the continuation bit are restated as 128.
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

/-! ## The canonical encoding -/

/-- The shape check passes a last byte only at the end of the input.

It passes a continued byte only when the rest passes. -/
private theorem of_groups_cons_eq_ok {fuel : Nat} {b : UInt8} {bs gs : List UInt8}
    (h : groups (fuel + 1) (b :: bs) = .ok gs) :
    (b.toNat < continuation ∧ bs = [] ∧ gs = [b]) ∨
      (continuation ≤ b.toNat ∧ ∃ rs, groups fuel bs = .ok rs ∧ gs = b :: rs) := by
  simp only [groups] at h
  split at h
  · rename_i hb
    cases bs with
    | nil => exact Or.inl ⟨hb, rfl, (Except.ok.inj h).symm⟩
    | cons _ _ => simp at h
  · rename_i hb
    cases hr : groups fuel bs with
    | error e => simp [hr, Except.map] at h
    | ok rs =>
        simp only [hr, Except.map, Except.ok.injEq] at h
        exact Or.inr ⟨Nat.le_of_not_lt hb, rs, rfl, h.symm⟩

/-- The shape check returns its whole input when it passes. -/
private theorem eq_of_groups_eq_ok {fuel : Nat} {bs gs : List UInt8}
    (h : groups fuel bs = .ok gs) : gs = bs := by
  induction fuel generalizing bs gs with
  | zero => cases bs <;> simp [groups] at h
  | succ fuel ih =>
      cases bs with
      | nil => simp [groups] at h
      | cons b bs =>
          rcases of_groups_cons_eq_ok h with ⟨-, rfl, rfl⟩ | ⟨-, rs, hr, rfl⟩
          · rfl
          · rw [ih hr]

/-- An input that passes the shape check and is minimal encodes its value back to itself. -/
private theorem encodeAux_valueOf_of_groups_eq_ok {fuel : Nat} {bs gs : List UInt8}
    (h : groups fuel bs = .ok gs) (hm : nonMinimal bs = false) :
    encodeAux (valueOf bs) fuel = bs := by
  induction fuel generalizing bs gs with
  | zero => cases bs <;> simp [groups] at h
  | succ fuel ih =>
      cases bs with
      | nil => simp [groups] at h
      | cons b bs =>
          rcases of_groups_cons_eq_ok h with ⟨hb, rfl, -⟩ | ⟨hb, rs, hr, -⟩
          · -- A byte below 128 is its own value, and it encodes as itself.
            have hlt : b.toNat < groupSize := hb
            have hv : valueOf [b] = b.toNat := by simp [valueOf, Nat.mod_eq_of_lt hlt]
            rw [hv, encodeAux, ite_eq_left hlt, UInt8.ofNat_toNat]
          · cases bs with
            -- The shape check rejects an empty input.
            | nil => simp [groups] at hr
            | cons c cs =>
                -- Minimality excludes a zero byte at the end, so the rest is minimal too.
                have hl : (c :: cs).getLast? ≠ some 0 := by simpa [nonMinimal] using hm
                have hrest : nonMinimal (c :: cs) = false := by simp [nonMinimal, hl]
                have hrec := ih hr hrest
                -- Zero encodes as one zero byte, so the rest denotes a positive number.
                have hpos : 0 < valueOf (c :: cs) := by
                  refine Nat.pos_of_ne_zero fun h0 => hl ?_
                  cases fuel with
                  | zero => simp [groups] at hr
                  | succ fuel =>
                      rw [h0, encodeAux, ite_eq_left (by decide : 0 < groupSize)] at hrec
                      rw [← hrec]
                      rfl
                -- So the value is at least 128, and dividing it by 128 gives the rest back.
                have hv : valueOf (b :: c :: cs) = b.toNat % 128 + 128 * valueOf (c :: cs) := rfl
                have hge : ¬ valueOf (b :: c :: cs) < groupSize := by rw [groupSize_eq]; omega
                have hq : valueOf (b :: c :: cs) / groupSize = valueOf (c :: cs) := by
                  rw [groupSize_eq]; omega
                -- The low group with the continuation bit is the byte itself.
                have hbyte :
                    UInt8.ofNat (valueOf (b :: c :: cs) % groupSize + continuation) = b := by
                  apply UInt8.toNat_inj.mp
                  have hsize := UInt8.toNat_lt b
                  rw [toNat_continued_byte, groupSize_eq, continuation_eq]
                  rw [continuation_eq] at hb
                  omega
                rw [encodeAux, ite_eq_right hge, hq, hbyte, hrec]

/-- Every input that decodes is the encoding of the value it decodes to. -/
theorem encode_decode {bs : List UInt8} {v : UInt64} (h : decode bs = .ok v) : encode v = bs := by
  -- An input that decodes passed the shape check and both later checks.
  cases hg : groups maxLength bs with
  | error e => simp [decode, hg] at h
  | ok gs =>
      obtain rfl := eq_of_groups_eq_ok hg
      rw [decode, hg] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hm
        split at h
        · cases h
        · rename_i hlt
          obtain rfl := Except.ok.inj h
          -- The value is below 2^64, so the 64-bit integer keeps it.
          have hv : (UInt64.ofNat (valueOf gs)).toNat = valueOf gs :=
            UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
          rw [encode, hv]
          exact encodeAux_valueOf_of_groups_eq_ok hg (by simpa using hm)

/-- Encoding is a bijection from 64-bit values onto the byte strings that the decoder accepts.

- Every value decodes back from its encoding.
- Every input that decodes is the encoding of what it decodes to.
-/
theorem decode_eq_ok_iff {bs : List UInt8} {v : UInt64} : decode bs = .ok v ↔ encode v = bs :=
  ⟨encode_decode, fun h => h ▸ decode_encode v⟩

/-! ## Inputs that are too long -/

/-- The shape check runs out of budget exactly when bytes remain after continued bytes fill it. -/
private theorem groups_eq_tooLong_iff {fuel : Nat} {bs : List UInt8} :
    groups fuel bs = .error .tooLong ↔
      fuel < bs.length ∧ ∀ c ∈ bs.take fuel, continuation ≤ c.toNat := by
  induction fuel generalizing bs with
  | zero => cases bs <;> simp [groups]
  | succ fuel ih =>
      cases bs with
      | nil => simp [groups]
      | cons b bs =>
          by_cases hb : b.toNat < continuation
          · -- A last byte ends the check with success or with trailing bytes.
            have hle : ¬ continuation ≤ b.toNat := Nat.not_le.mpr hb
            cases bs <;> simp [groups, hb, hle]
          · -- A continued byte keeps the result of the rest, whichever error it is.
            have hmap : (groups fuel bs).map (b :: ·) = .error .tooLong ↔
                groups fuel bs = .error .tooLong := by
              cases groups fuel bs <;> simp [Except.map]
            simp [groups, hb, hmap, ih, Nat.le_of_not_lt hb]

/-- An input is too long exactly when it has over ten bytes and the first ten are continued. -/
theorem decode_eq_tooLong_iff {bs : List UInt8} :
    decode bs = .error .tooLong ↔
      10 < bs.length ∧ ∀ c ∈ bs.take 10, continuation ≤ c.toNat := by
  have hg : groups maxLength bs = .error .tooLong ↔
      10 < bs.length ∧ ∀ c ∈ bs.take 10, continuation ≤ c.toNat :=
    groups_eq_tooLong_iff
  rw [← hg]
  -- The two checks after the shape check give other errors.
  cases hr : groups maxLength bs with
  | error e => simp [decode, hr]
  | ok gs =>
      simp only [decode, hr]
      split
      · simp
      · split <;> simp

/-! ## Splitting a varint from the bytes after it -/

/-- The split finds the last byte of an encoding, whatever follows it. -/
theorem findIdx_encodeAux {n fuel m : Nat} (rest : List UInt8) (hf : 0 < fuel)
    (hn : n < groupSize ^ fuel) (hm : (encodeAux n fuel).length ≤ m) :
    ((encodeAux n fuel ++ rest).take m).findIdx (·.toNat < continuation) + 1 =
      (encodeAux n fuel).length := by
  induction fuel generalizing n m with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by
      have := encodeAux_ne_nil (n := n) hf
      cases h : encodeAux n (fuel + 1) <;> simp_all; omega⟩
    by_cases hlt : n < groupSize
    · -- One byte, below 128.
      simp [encodeAux, hlt, toNat_terminator_byte hlt, List.findIdx_cons]
      rw [groupSize_eq, continuation_eq] at *
      omega
    · -- A continued byte, then the encoding of the rest.
      have hf' : 0 < fuel := by
        rcases fuel with _ | _
        · simp at hn; omega
        · omega
      have hn' : n / groupSize < groupSize ^ fuel := by
        rw [Nat.pow_succ] at hn
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      simp only [encodeAux, hlt, ite_false, List.cons_append, List.take_succ_cons,
        List.length_cons] at hm ⊢
      rw [List.findIdx_cons]
      have hc : ¬ (UInt8.ofNat (n % groupSize + continuation)).toNat < continuation := by
        rw [toNat_continued_byte]; omega
      have := ih hf' hn' (m := m) (by omega)
      simp only [hc, decide_false, Bool.false_eq_true, ite_false]
      omega

/-- The split of an encoding followed by any bytes returns the encoding and those bytes. -/
theorem split_encode (v : UInt64) (rest : List UInt8) :
    split (encode v ++ rest) = (encode v, rest) := by
  have hlt : v.toNat < groupSize ^ maxLength := by
    have := v.toNat_lt_size
    simp only [UInt64.size, groupSize, payloadBits, maxLength] at *
    omega
  have h := findIdx_encodeAux rest (by decide) hlt (encode_length_le v)
  simp only [split]
  rw [show encodeAux v.toNat maxLength = encode v from rfl] at h
  rw [h]
  simp

/-- The split cuts the input in two, so its two parts join back to the input. -/
theorem split_append (bs : List UInt8) : (split bs).1 ++ (split bs).2 = bs :=
  List.take_append_drop _ _

/-! ## Error codes -/

section

open EthLib.Networking.Encoding.Varint

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Encoding.Varint.VarintError.code_injective
    (e₁ e₂ : VarintError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [VarintError.code] at h; exact absurd h (by decide))

end

end EthLib.Networking.Proofs.Encoding.Varint
