module

public import EthLib.Engine.Jwt.Json

/-!
# Proofs: `Jwt.Json`

The Unicode escape of RFC 8259 §7 reads four hexadecimal digits, and pairs a surrogate.

A code point that the escape returns is the one its digits name, so the reader substitutes none.

A lone surrogate names no code point, and the escape refuses one from either half of the range.

A character below `0x20` closes no string, so the reader refuses it unescaped.
-/

@[expose] public section

namespace EthLib.Engine.Jwt.Json

/-! ## The four digits of an escape

The reader accepts a digit in three ranges, and each one carries a value below 16.
-/

/-- A decimal digit has a code point from 48 through 57. -/
private theorem toNat_of_digit {c : Char} (h : digit c = true) :
    48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [digit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def] at h
  have h1 := UInt32.le_iff_toNat_le.mp h.1
  have h2 := UInt32.le_iff_toNat_le.mp h.2
  rw [show ('0' : Char).val.toNat = 48 from by decide] at h1
  rw [show ('9' : Char).val.toNat = 57 from by decide] at h2
  simp only [Char.toNat]
  omega

/-- A character between two others has a code point between theirs. -/
private theorem toNat_of_between {c lo hi : Char} (h : (lo ≤ c && c ≤ hi) = true) :
    lo.toNat ≤ c.toNat ∧ c.toNat ≤ hi.toNat := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def] at h
  simp only [Char.toNat]
  exact ⟨UInt32.le_iff_toNat_le.mp h.1, UInt32.le_iff_toNat_le.mp h.2⟩

/-- A digit that the escape reads carries a value below 16. -/
private theorem readHex_lt {c : Char} {v : Nat}
    (h : (if digit c then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none) = some v) : v < 16 := by
  split at h
  · rename_i hc
    have := toNat_of_digit hc
    rw [show ('0' : Char).toNat = 48 from by decide, Option.some.injEq] at h
    omega
  · split at h
    · rename_i hc
      have := toNat_of_between hc
      rw [show ('a' : Char).toNat = 97 from by decide, Option.some.injEq] at h
      rw [show ('a' : Char).toNat = 97 from by decide,
        show ('f' : Char).toNat = 102 from by decide] at this
      omega
    · split at h
      · rename_i hc
        have := toNat_of_between hc
        rw [show ('A' : Char).toNat = 65 from by decide, Option.some.injEq] at h
        rw [show ('A' : Char).toNat = 65 from by decide,
          show ('F' : Char).toNat = 70 from by decide] at this
        omega
      · exact absurd h (by simp)

/-- Fewer than four characters are no escape. -/
theorem hex4_eq_none_of_length_lt {chars : List Char} (h : chars.length < 4) :
    hex4 chars = none := by
  rcases chars with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp [hex4]
  · simp [hex4]
  · simp [hex4]
  · simp [hex4]
  · simp only [List.length_cons] at h
    omega

/-- Four digits name a code point below `0x10000`, and the escape reads the rest after them. -/
theorem hex4_lt_and_eq_drop {chars rest : List Char} {n : Nat} (h : hex4 chars = some (n, rest)) :
    n < 0x10000 ∧ rest = chars.drop 4 := by
  rcases chars with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp [hex4] at h
  · simp [hex4] at h
  · simp [hex4] at h
  · simp [hex4] at h
  · simp only [hex4, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨va, hva, vb, hvb, vc, hvc, vd, hvd, hn, hr⟩ := h
    have := readHex_lt hva
    have := readHex_lt hvb
    have := readHex_lt hvc
    have := readHex_lt hvd
    exact ⟨by omega, hr.symm⟩

/-- Four digits name a code point below `0x10000`. -/
theorem hex4_lt {chars rest : List Char} {n : Nat} (h : hex4 chars = some (n, rest)) :
    n < 0x10000 := (hex4_lt_and_eq_drop h).1

/-- An escape reads four characters and leaves the ones after them. -/
theorem hex4_eq_drop {chars rest : List Char} {n : Nat} (h : hex4 chars = some (n, rest)) :
    rest = chars.drop 4 := (hex4_lt_and_eq_drop h).2

/-! ## The code point an escape returns -/

/-- A code point that no surrogate names is returned as it stands.

So the reader of an escape substitutes no replacement character of its own. -/
theorem unicodeEscape_eq_of_not_surrogate {chars rest : List Char} {n : Nat}
    (hh : hex4 chars = some (n, rest)) (h : n < 0xd800 ∨ 0xe000 ≤ n) :
    ∃ c, unicodeEscape chars = some (c, rest) ∧ c.toNat = n := by
  have hlt := hex4_lt hh
  have hvalid : n.isValidChar := by
    simp only [Nat.isValidChar]
    omega
  refine ⟨Char.ofNat n, ?_, ?_⟩
  · rcases h with h | h
    · simp [unicodeEscape, hh, bind, Option.bind, Nat.not_le.mpr h] <;> omega
    · simp [unicodeEscape, hh, bind, Option.bind, Nat.not_lt.mpr h,
        show ¬ (0xd800 ≤ n ∧ n < 0xdc00) from by omega] <;> omega
  · have h32 : n < 2 ^ 32 := by omega
    simp [Char.ofNat, hvalid, Char.ofNatAux, Char.toNat]

/-- A lone low surrogate names no code point, so the escape refuses it. -/
theorem unicodeEscape_eq_none_of_low_surrogate {chars rest : List Char} {n : Nat}
    (hh : hex4 chars = some (n, rest)) (h1 : 0xdc00 ≤ n) (h2 : n < 0xe000) :
    unicodeEscape chars = none := by
  simp [unicodeEscape, hh, bind, Option.bind, h1, h2]
  exact fun _ h3 => absurd h3 (Nat.not_lt.mpr h1)

/-- A high surrogate that no second escape follows names no code point either. -/
theorem unicodeEscape_eq_none_of_unpaired {chars rest : List Char} {n : Nat}
    (hh : hex4 chars = some (n, rest)) (h1 : 0xd800 ≤ n) (h2 : n < 0xdc00)
    (hr : ∀ tail, rest ≠ '\\' :: 'u' :: tail) : unicodeEscape chars = none := by
  rcases rest with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp [unicodeEscape, hh, bind, Option.bind, h1, h2]
  · simp [unicodeEscape, hh, bind, Option.bind, h1, h2]
  · have hab : ¬ (a = '\\' ∧ b = 'u') := fun hv => hr t (by rw [hv.1, hv.2])
    -- The escape is stuck on a `rest` that is no second escape, in either character.
    rcases Decidable.not_and_iff_or_not.mp hab with h | h
    · simp [unicodeEscape, hh, bind, Option.bind, h1, h2]
    · simp [unicodeEscape, hh, bind, Option.bind, h1, h2]

/-! ## The characters a string refuses -/

/-- A run of characters with no closing quote is no string. -/
@[simp] theorem string_eq_none_nil (fuel : Nat) (acc : List Char) :
    string fuel [] acc = none := by
  cases fuel <;> simp [string]

/-- A control character below `0x20` closes no string, so the reader refuses it unescaped. -/
theorem string_eq_none_of_control {fuel : Nat} {c : Char} {rest acc : List Char}
    (h : c.toNat < 0x20) : string (fuel + 1) (c :: rest) acc = none := by
  have hq : c ≠ '"' := fun hc => by rw [hc] at h; revert h; decide
  have hb : c ≠ '\\' := fun hc => by rw [hc] at h; revert h; decide
  rw [string]
  simp [Nat.not_le.mpr h]
  · exact hq
  · exact fun _ hc _ => hb hc
  · exact fun _ _ hc _ => hb hc

end EthLib.Engine.Jwt.Json
