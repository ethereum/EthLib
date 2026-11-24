module

public import EthLib.Base.Proofs.Json.Text
public import EthLib.Base.Proofs.Hex

/-!
# Proofs: the Unicode escapes and control characters of a JSON string

The Unicode escape of [RFC 8259 §7][json] reads four hexadecimal digits, in either letter case.

The grammar admits a lone surrogate ([§8.2][lone]), but this reader refuses one.

The reader refuses a string whose first character that needs an escape is below `0x20`.

[json]: https://www.rfc-editor.org/rfc/rfc8259#section-7
[lone]: https://www.rfc-editor.org/rfc/rfc8259#section-8.2
-/

@[expose] public section

namespace EthLib.Base.Json

/-! ## The four digits of an escape

The reader accepts a digit from three ranges, and each digit carries a value below 16.
-/

/-- A hex digit has a value below 16. -/
private theorem toNat_lt_of_hexValue? {c : Char} {v : UInt8} (h : hexValue? c = some v) :
    v.toNat < 16 := by
  obtain ⟨digit, rfl, -⟩ := hexValue?_eq_some h
  have := digit.isLt
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
  omega

variable {text : String}

/-- One hex digit is read when it comes next, with the value that the hex digits give. -/
private theorem hexDigit_of_after {p : text.Pos} {c : Char} {cs : List Char}
    (h : after p = c :: cs) :
    ∃ q, after q = cs ∧ hexDigit p = (hexValue? c).map fun v => (v.toNat, q) := by
  obtain ⟨hp, hc, hn⟩ := after_eq_cons h
  exact ⟨p.next hp, hn, by simp [hexDigit, hp, hc]⟩

/-- No hex digit is read at the end of the text. -/
private theorem hexDigit_of_after_nil {p : text.Pos} (h : after p = []) : hexDigit p = none := by
  simp [hexDigit, (after_eq_nil_iff).1 h]

/-- Fewer than four characters are no escape. -/
theorem hex4_eq_none_of_length_lt {p : text.Pos} (h : (after p).length < 4) :
    hex4 p = none := by
  -- Each digit read moves one character on, and the end of the text comes before a fourth.
  match e : after p, h with
  | [], _ => simp [hex4, hexDigit_of_after_nil e]
  | [a], _ =>
    obtain ⟨q₁, e₁, d₁⟩ := hexDigit_of_after e
    cases ha : hexValue? a <;> simp [hex4, d₁, ha, hexDigit_of_after_nil e₁]
  | [a, b], _ =>
    obtain ⟨q₁, e₁, d₁⟩ := hexDigit_of_after e
    obtain ⟨q₂, e₂, d₂⟩ := hexDigit_of_after e₁
    cases ha : hexValue? a <;> cases hb : hexValue? b <;>
      simp [hex4, d₁, d₂, ha, hb, hexDigit_of_after_nil e₂]
  | [a, b, c], _ =>
    obtain ⟨q₁, e₁, d₁⟩ := hexDigit_of_after e
    obtain ⟨q₂, e₂, d₂⟩ := hexDigit_of_after e₁
    obtain ⟨q₃, e₃, d₃⟩ := hexDigit_of_after e₂
    cases ha : hexValue? a <;> cases hb : hexValue? b <;> cases hc : hexValue? c <;>
      simp [hex4, d₁, d₂, d₃, ha, hb, hc, hexDigit_of_after_nil e₃]

/-- Four hex digits, in either letter case, name the number they write in base 16. -/
theorem hex4_eq_some_iff {p q : text.Pos} {a b c d : Char} {t : List Char} {n : Nat}
    (h : after p = a :: b :: c :: d :: t) :
    hex4 p = some (n, q) ↔
      after q = t ∧ ∃ va vb vc vd, hexValue? a = some va ∧ hexValue? b = some vb ∧
        hexValue? c = some vc ∧ hexValue? d = some vd ∧
        n = 4096 * va.toNat + 256 * vb.toNat + 16 * vc.toNat + vd.toNat := by
  obtain ⟨q₁, e₁, d₁⟩ := hexDigit_of_after h
  obtain ⟨q₂, e₂, d₂⟩ := hexDigit_of_after e₁
  obtain ⟨q₃, e₃, d₃⟩ := hexDigit_of_after e₂
  obtain ⟨q₄, e₄, d₄⟩ := hexDigit_of_after e₃
  -- The position after the four digits is the one whose characters are the rest.
  have same : after q = t ↔ q₄ = q := ⟨fun e => eq_of_after_eq (e₄.trans e.symm), by
    rintro rfl
    exact e₄⟩
  rw [same]
  cases ha : hexValue? a <;> cases hb : hexValue? b <;> cases hc : hexValue? c <;>
    cases hd : hexValue? d <;> simp [hex4, d₁, d₂, d₃, d₄, ha, hb, hc, hd, eq_comm, and_comm]

/-- Four digits name a value below `0x10000`, and the escape leaves the characters after them. -/
private theorem hex4_lt_and_after {p q : text.Pos} {n : Nat} (h : hex4 p = some (n, q)) :
    n < 0x10000 ∧ after q = (after p).drop 4 := by
  match e : after p with
  | a :: b :: c :: d :: t =>
    obtain ⟨rest, va, vb, vc, vd, ha, hb, hc, hd, hn⟩ := (hex4_eq_some_iff e).1 h
    have := toNat_lt_of_hexValue? ha
    have := toNat_lt_of_hexValue? hb
    have := toNat_lt_of_hexValue? hc
    have := toNat_lt_of_hexValue? hd
    exact ⟨by omega, by simp [rest]⟩
  | [] | [_] | [_, _] | [_, _, _] =>
    rw [hex4_eq_none_of_length_lt (by simp [e])] at h
    cases h

/-- Four digits name a value below `0x10000`. -/
theorem hex4_lt {p q : text.Pos} {n : Nat} (h : hex4 p = some (n, q)) :
    n < 0x10000 := (hex4_lt_and_after h).1

/-- An escape reads four characters and leaves the ones after them. -/
theorem after_of_hex4 {p q : text.Pos} {n : Nat} (h : hex4 p = some (n, q)) :
    after q = (after p).drop 4 := (hex4_lt_and_after h).2

/-! ## The code point an escape returns -/

/-- An escape without four hex digits is refused. -/
theorem unicodeEscape_eq_none_of_hex4 {p : text.Pos} (h : hex4 p = none) :
    unicodeEscape p = none := by
  simp [unicodeEscape, h, bind, Option.bind]

/-- A value that is a Unicode scalar value is the code point of its character. -/
private theorem toNat_ofNat {n : Nat} (h : n < 0xd800 ∨ (0xe000 ≤ n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  have hvalid : n.isValidChar := by
    simp only [Nat.isValidChar]
    omega
  have h32 : n < 2 ^ 32 := by omega
  simp [Char.ofNat, hvalid, Char.ofNatAux, Char.toNat]

/-- A value outside the surrogate range is returned as the code point it names.

So the reader of an escape substitutes no replacement character of its own. -/
theorem unicodeEscape_eq_of_not_surrogate {p q : text.Pos} {n : Nat}
    (hh : hex4 p = some (n, q)) (h : n < 0xd800 ∨ 0xe000 ≤ n) :
    unicodeEscape p = some (Char.ofNat n, q) ∧ (Char.ofNat n).toNat = n := by
  have hlt := hex4_lt hh
  refine ⟨?_, toNat_ofNat (by omega)⟩
  rcases h with h | h
  · simp [unicodeEscape, hh, bind, Option.bind, Nat.not_le.mpr h] <;> omega
  · simp [unicodeEscape, hh, bind, Option.bind, Nat.not_lt.mpr h,
      show ¬ (0xd800 ≤ n ∧ n < 0xdc00) from by omega] <;> omega

/-- A high surrogate and an escaped low surrogate after it name one code point, RFC 8259 §7.

The returned character has that code point, so the reader substitutes none. -/
theorem unicodeEscape_eq_of_pair {p q r t : text.Pos} {hi lo : Nat}
    (hh : hex4 p = some (hi, q)) (hq : after q = '\\' :: 'u' :: after r)
    (hl : hex4 r = some (lo, t))
    (h1 : 0xd800 ≤ hi) (h2 : hi < 0xdc00) (h3 : 0xdc00 ≤ lo) (h4 : lo < 0xe000) :
    unicodeEscape p
        = some (Char.ofNat (0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00)), t) ∧
      (Char.ofNat (0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00))).toNat
        = 0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00) := by
  refine ⟨?_, toNat_ofNat (by omega)⟩
  -- The reverse solidus and the `u` of the second escape are read, which leaves the low half.
  obtain ⟨q₁, e₁, a₁⟩ := expect_of_after hq
  obtain ⟨q₂, e₂, a₂⟩ := expect_of_after a₁
  obtain rfl := eq_of_after_eq a₂
  -- The reader subtracts the low offset last, which the bound on the low half allows.
  have e : 0x10000 + 1024 * (hi - 0xd800) + lo - 0xdc00
      = 0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00) := by omega
  simp [unicodeEscape, hh, hl, e₁, e₂, bind, Option.bind, h1, h2, h3, h4, e]

/-- A surrogate that no escaped low surrogate completes is refused.

This covers a low surrogate that comes first, and a high surrogate with no low one after it. -/
theorem unicodeEscape_eq_none_of_surrogate {p q : text.Pos} {n : Nat}
    (hh : hex4 p = some (n, q)) (h1 : 0xd800 ≤ n) (h2 : n < 0xe000)
    (hlone : ∀ (r t : text.Pos) lo, n < 0xdc00 → after q = '\\' :: 'u' :: after r →
      hex4 r = some (lo, t) → lo < 0xdc00 ∨ 0xe000 ≤ lo) :
    unicodeEscape p = none := by
  by_cases hn : n < 0xdc00
  · -- A high surrogate: what follows it decides.
    by_cases slash : (after q).head? = some '\\'
    · obtain ⟨xs, ex⟩ := List.head?_eq_some_iff.1 slash
      obtain ⟨q₁, e₁, a₁⟩ := expect_of_after ex
      by_cases letter : (after q₁).head? = some 'u'
      · obtain ⟨ys, ey⟩ := List.head?_eq_some_iff.1 letter
        obtain ⟨r, e₂, a₂⟩ := expect_of_after ey
        have form : after q = '\\' :: 'u' :: after r := by rw [ex, ← a₁, ey, a₂]
        cases hr : hex4 r with
        | none => simp [unicodeEscape, hh, e₁, e₂, hr, bind, Option.bind, h1, hn]
        | some x =>
          obtain ⟨lo, t⟩ := x
          have := hlone r t lo hn form hr
          simp [unicodeEscape, hh, e₁, e₂, hr, bind, Option.bind, h1, hn]
          omega
      · simp [unicodeEscape, hh, e₁, expect_eq_none letter, bind, Option.bind, h1, hn]
    · simp [unicodeEscape, hh, expect_eq_none slash, bind, Option.bind, h1, hn]
  · -- A low surrogate first is refused at once.
    simp [unicodeEscape, hh, bind, Option.bind, h1, h2, Nat.not_lt.mp hn]
    exact fun h => absurd h hn

/-! ## The characters a string refuses -/

/-- The reader refuses a string whose first character that needs an escape is below `0x20`. -/
theorem string_eq_none_of_control {fuel : Nat} {p : text.Pos} {acc : String} {c : Char}
    (hc : ((after p).dropWhile plain).head? = some c) (h : c.toNat < 0x20) :
    string fuel p acc = none := by
  cases fuel with
  | zero => simp [string]
  | succ fuel =>
    -- The run without an escape ends just before that character.
    have stop : after (plainEnd p) = c :: ((after p).dropWhile plain).tail := by
      rw [after_plainEnd]
      cases e : (after p).dropWhile plain with
      | nil => simp [e] at hc
      | cons x xs => simp_all
    obtain ⟨hq, get, -⟩ := after_eq_cons stop
    have hq' : c ≠ '"' := fun e => by subst e; revert h; decide
    have hb : c ≠ '\\' := fun e => by subst e; revert h; decide
    simp [string, hq, get, hq', hb]

end EthLib.Base.Json
