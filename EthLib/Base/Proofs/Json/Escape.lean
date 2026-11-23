module

public import EthLib.Base.Json
public import EthLib.Base.Proofs.Hex

/-!
# Proofs: the Unicode escapes and control characters of a JSON string

The Unicode escape of [RFC 8259 §7][json] reads four hexadecimal digits, in either letter case.

Their value is the one that the hex digits of the library give.

A value outside the surrogate range is returned as the code point it names.

A high surrogate followed by an escaped low surrogate is returned as the code point of the pair.

Every other surrogate is refused, from either half of the range.

The grammar admits a lone surrogate ([§8.2][lone]), but this reader refuses one.

The reader refuses a character below `0x20` that comes next in a string unescaped.

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

/-- Four hex digits, in either letter case, name the number they write in base 16. -/
theorem hex4_cons_eq_some_iff {a b c d : Char} {t rest : List Char} {n : Nat} :
    hex4 (a :: b :: c :: d :: t) = some (n, rest) ↔
      rest = t ∧ ∃ va vb vc vd, hexValue? a = some va ∧ hexValue? b = some vb ∧
        hexValue? c = some vc ∧ hexValue? d = some vd ∧
        n = 4096 * va.toNat + 256 * vb.toNat + 16 * vc.toNat + vd.toNat := by
  simp only [hex4, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
    bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, ⟨va, ha, rfl⟩, _, ⟨vb, hb, rfl⟩, _, ⟨vc, hc, rfl⟩, _, ⟨vd, hd, rfl⟩, hn, hr⟩
    exact ⟨hr.symm, va, vb, vc, vd, ha, hb, hc, hd, hn.symm⟩
  · rintro ⟨hr, va, vb, vc, vd, ha, hb, hc, hd, hn⟩
    exact ⟨_, ⟨va, ha, rfl⟩, _, ⟨vb, hb, rfl⟩, _, ⟨vc, hc, rfl⟩, _, ⟨vd, hd, rfl⟩, hn.symm,
      hr.symm⟩

/-- Four digits name a value below `0x10000`, and the escape leaves the characters after them. -/
private theorem hex4_lt_and_eq_drop {chars rest : List Char} {n : Nat}
    (h : hex4 chars = some (n, rest)) : n < 0x10000 ∧ rest = chars.drop 4 := by
  rcases chars with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩⟩
  · simp [hex4] at h
  · simp [hex4] at h
  · simp [hex4] at h
  · simp [hex4] at h
  · obtain ⟨hr, va, vb, vc, vd, ha, hb, hc, hd, hn⟩ := hex4_cons_eq_some_iff.mp h
    have := toNat_lt_of_hexValue? ha
    have := toNat_lt_of_hexValue? hb
    have := toNat_lt_of_hexValue? hc
    have := toNat_lt_of_hexValue? hd
    exact ⟨by omega, by simp [hr]⟩

/-- Four digits name a value below `0x10000`. -/
theorem hex4_lt {chars rest : List Char} {n : Nat} (h : hex4 chars = some (n, rest)) :
    n < 0x10000 := (hex4_lt_and_eq_drop h).1

/-- An escape reads four characters and leaves the ones after them. -/
theorem hex4_eq_drop {chars rest : List Char} {n : Nat} (h : hex4 chars = some (n, rest)) :
    rest = chars.drop 4 := (hex4_lt_and_eq_drop h).2

/-! ## The code point an escape returns -/

/-- An escape without four hex digits is refused. -/
theorem unicodeEscape_eq_none_of_hex4 {chars : List Char} (h : hex4 chars = none) :
    unicodeEscape chars = none := by
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
theorem unicodeEscape_eq_of_not_surrogate {chars rest : List Char} {n : Nat}
    (hh : hex4 chars = some (n, rest)) (h : n < 0xd800 ∨ 0xe000 ≤ n) :
    unicodeEscape chars = some (Char.ofNat n, rest) ∧ (Char.ofNat n).toNat = n := by
  have hlt := hex4_lt hh
  refine ⟨?_, toNat_ofNat (by omega)⟩
  rcases h with h | h
  · simp [unicodeEscape, hh, bind, Option.bind, Nat.not_le.mpr h] <;> omega
  · simp [unicodeEscape, hh, bind, Option.bind, Nat.not_lt.mpr h,
      show ¬ (0xd800 ≤ n ∧ n < 0xdc00) from by omega] <;> omega

/-- A high surrogate and an escaped low surrogate after it name one code point, RFC 8259 §7.

The returned character has that code point, so the reader substitutes none. -/
theorem unicodeEscape_eq_of_pair {chars tail rest : List Char} {hi lo : Nat}
    (hh : hex4 chars = some (hi, '\\' :: 'u' :: tail)) (hl : hex4 tail = some (lo, rest))
    (h1 : 0xd800 ≤ hi) (h2 : hi < 0xdc00) (h3 : 0xdc00 ≤ lo) (h4 : lo < 0xe000) :
    unicodeEscape chars
        = some (Char.ofNat (0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00)), rest) ∧
      (Char.ofNat (0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00))).toNat
        = 0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00) := by
  refine ⟨?_, toNat_ofNat (by omega)⟩
  -- The reader subtracts the low offset last, which the bound on the low half allows.
  have e : 0x10000 + 1024 * (hi - 0xd800) + lo - 0xdc00
      = 0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00) := by omega
  simp [unicodeEscape, hh, hl, bind, Option.bind, h1, h2, h3, h4, e]

/-- A surrogate that no escaped low surrogate completes is refused.

This covers a low surrogate that comes first, and a high surrogate with no low one after it. -/
theorem unicodeEscape_eq_none_of_surrogate {chars rest : List Char} {n : Nat}
    (hh : hex4 chars = some (n, rest)) (h1 : 0xd800 ≤ n) (h2 : n < 0xe000)
    (hlone : ∀ tail lo rest', n < 0xdc00 → rest = '\\' :: 'u' :: tail →
      hex4 tail = some (lo, rest') → lo < 0xdc00 ∨ 0xe000 ≤ lo) :
    unicodeEscape chars = none := by
  by_cases hn : n < 0xdc00
  · rcases rest with _ | ⟨x, _ | ⟨y, tail⟩⟩
    · simp [unicodeEscape, hh, bind, Option.bind, h1, hn]
    · simp [unicodeEscape, hh, bind, Option.bind, h1, hn]
    · by_cases hxy : x = '\\' ∧ y = 'u'
      · obtain ⟨rfl, rfl⟩ := hxy
        cases hx : hex4 tail with
        | none => simp [unicodeEscape, hh, hx, bind, Option.bind, h1, hn]
        | some p =>
          obtain ⟨lo, r⟩ := p
          have := hlone tail lo r hn rfl hx
          simp [unicodeEscape, hh, hx, bind, Option.bind, h1, hn]
          omega
      · rcases Decidable.not_and_iff_or_not.mp hxy with h | h
        · simp [unicodeEscape, hh, bind, Option.bind, h1, hn, h]
        · simp [unicodeEscape, hh, bind, Option.bind, h1, hn, h]
  · simp [unicodeEscape, hh, bind, Option.bind, h1, h2, Nat.not_lt.mp hn]
    exact fun h => absurd h hn

/-! ## The characters a string refuses -/

/-- The reader refuses a character below `0x20` that comes next in a string unescaped. -/
theorem string_eq_none_of_control {fuel : Nat} {c : Char} {rest acc : List Char}
    (h : c.toNat < 0x20) : string fuel (c :: rest) acc = none := by
  have hq : c ≠ '"' := fun hc => by rw [hc] at h; revert h; decide
  have hb : c ≠ '\\' := fun hc => by rw [hc] at h; revert h; decide
  cases fuel with
  | zero => simp [string]
  | succ fuel =>
    rw [string]
    simp [Nat.not_le.mpr h]
    · exact hq
    · exact fun _ hc _ => hb hc
    · exact fun _ _ hc _ => hb hc

end EthLib.Base.Json
