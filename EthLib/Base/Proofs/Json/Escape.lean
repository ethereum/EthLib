module

public import EthLib.Base.Proofs.Json.Text
public import EthLib.Base.Proofs.Hex

/-!
# Proofs: the escapes and characters of a JSON string

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


/-! ## The characters a string stands for

A string reads as the characters that its text stands for, as RFC 8259 §7 writes them.

Each character of the text is unescaped, or starts one of the escapes of the grammar.
-/

/-- The escapes of RFC 8259 §7 that are two characters long.

Each pair is the character after the reverse solidus and the character the escape stands for. -/
def escapePairs : List (Char × Char) :=
  -- The quotation mark U+0022, the reverse solidus U+005C and the solidus U+002F.
  --
  -- The backspace U+0008, the form feed U+000C and the line feed U+000A.
  --
  -- The carriage return U+000D and the tab U+0009.
  [('"', '\x22'), ('\\', '\x5c'), ('/', '\x2f'), ('b', '\x08'), ('f', '\x0c'), ('n', '\x0a'),
    ('r', '\x0d'), ('t', '\x09')]

/-- Four characters are hex digits, in either letter case, that write a number in base 16. -/
def HexDigits (a b c d : Char) (n : Nat) : Prop :=
  ∃ va vb vc vd, hexValue? a = some va ∧ hexValue? b = some vb ∧ hexValue? c = some vc ∧
    hexValue? d = some vd ∧ n = 4096 * va.toNat + 256 * vb.toNat + 16 * vc.toNat + vd.toNat

/-- The characters of a string between its quotation marks, and the characters they stand for. -/
inductive Unescapes : List Char → List Char → Prop
  /-- No characters stand for no characters. -/
  | nil : Unescapes [] []
  /-- A character from U+0020 that is no quotation mark and no reverse solidus stands for itself.

  That is `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`. -/
  | unescaped {c : Char} {cs ds : List Char} (low : 0x20 ≤ c.toNat) (quote : c ≠ '"')
      (solidus : c ≠ '\\') (rest : Unescapes cs ds) : Unescapes (c :: cs) (c :: ds)
  /-- A reverse solidus and the first character of a two-character escape stand for its second. -/
  | short {e d : Char} {cs ds : List Char} (mem : (e, d) ∈ escapePairs)
      (rest : Unescapes cs ds) : Unescapes ('\\' :: e :: cs) (d :: ds)
  /-- `\u` and four hex digits stand for the code point they write, outside the surrogates. -/
  | unicode {a b c d : Char} {n : Nat} {cs ds : List Char} (digits : HexDigits a b c d n)
      (scalar : n < 0xd800 ∨ 0xe000 ≤ n) (rest : Unescapes cs ds) :
      Unescapes ('\\' :: 'u' :: a :: b :: c :: d :: cs) (Char.ofNat n :: ds)
  /-- An escaped high surrogate, then an escaped low surrogate, stand for the code point of both.

  Not in RFC 8259: the grammar admits a lone surrogate, but no constructor takes one. -/
  | pair {a b c d w x y z : Char} {hi lo : Nat} {cs ds : List Char}
      (high : HexDigits a b c d hi) (low : HexDigits w x y z lo) (h1 : 0xd800 ≤ hi)
      (h2 : hi < 0xdc00) (h3 : 0xdc00 ≤ lo) (h4 : lo < 0xe000) (rest : Unescapes cs ds) :
      Unescapes ('\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: w :: x :: y :: z :: cs)
        (Char.ofNat (0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00)) :: ds)

/-- A character holds without an escape exactly when it is from U+0020 and no quote or solidus. -/
private theorem plain_eq_true_iff {c : Char} :
    plain c = true ↔ 0x20 ≤ c.toNat ∧ c ≠ '"' ∧ c ≠ '\\' := by
  unfold plain
  by_cases h1 : c = '"' <;> by_cases h2 : c = '\\' <;> simp [h1, h2]

/-- A two-character escape is read as the character that the table of the grammar gives. -/
private theorem shortEscape_eq_some_iff {e d : Char} :
    shortEscape e = some d ↔ (e, d) ∈ escapePairs := by
  unfold shortEscape escapePairs
  split <;> simp_all [eq_comm]

/-- No two-character escape starts with `u`. -/
private theorem ne_u_of_mem {e d : Char} (mem : (e, d) ∈ escapePairs) : e ≠ 'u' := by
  simp only [escapePairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ <;> decide

/-- The text read so far, then a piece, whether or not the text is empty. -/
private theorem append_of_isEmpty (acc piece : String) :
    (if acc.isEmpty then piece else acc ++ piece) = acc ++ piece := by
  split
  · rename_i h
    rw [String.isEmpty_iff.1 h]
    simp
  · rfl

/-- A run without an escape ends where the run from the next character ends. -/
private theorem plainEnd_of_plain {p : text.Pos} (hp : p ≠ text.endPos)
    (hc : plain (p.get hp)) : plainEnd p = plainEnd (p.next hp) := by
  rw [plainEnd]
  simp [hp, hc]

/-- A run without an escape is empty at a character that needs one. -/
private theorem plainEnd_of_not_plain {p : text.Pos} (hp : p ≠ text.endPos)
    (hc : plain (p.get hp) = false) : plainEnd p = p := by
  rw [plainEnd]
  simp [hp, hc]

/-- A character without an escape is read as itself, and the reader goes on after it. -/
private theorem string_of_plain {fuel : Nat} {p : text.Pos} {acc : String}
    (hp : p ≠ text.endPos) (hc : plain (p.get hp)) :
    string fuel p acc = string fuel (p.next hp) (acc.push (p.get hp)) := by
  cases fuel with
  | zero => simp [string]
  | succ n =>
    -- Both runs end at one position, and the first holds one more character.
    have e1 := plainEnd_of_plain hp hc
    have run : after (p.next hp) =
        (after (p.next hp)).takeWhile plain ++ after (plainEnd (p.next hp)) := by
      rw [after_plainEnd, List.takeWhile_append_dropWhile]
    have x1 := (extract_of_after ((p.get hp) :: (after (p.next hp)).takeWhile plain) (p := p)
      (q := plainEnd (p.next hp)) (by rw [after_eq_get_cons hp, List.cons_append, ← run])).2
    have x2 := (extract_of_after _ run).2
    have e2 : acc ++ text.extract p (plainEnd p) =
        acc.push (p.get hp) ++ text.extract (p.next hp) (plainEnd (p.next hp)) := by
      rw [e1, x1, x2, ← String.toList_inj]
      simp
    simp only [string, append_of_isEmpty]
    rw [e2, e1]

/-- At a character that needs an escape, the reader ends the string or reads one escape. -/
private theorem string_of_not_plain {n : Nat} {p : text.Pos} {acc : String}
    (hp : p ≠ text.endPos) (hc : plain (p.get hp) = false) :
    string (n + 1) p acc =
      if p.get hp = '"' then some (acc, p.next hp)
      else if p.get hp = '\\' then
        if h : p.next hp = text.endPos then none
        else if (p.next hp).get h = 'u' then
          (unicodeEscape ((p.next hp).next h)).bind fun x => string n x.2 (acc.push x.1)
        else
          (shortEscape ((p.next hp).get h)).bind fun d =>
            string n ((p.next hp).next h) (acc.push d)
      else none := by
  have pe := plainEnd_of_not_plain hp hc
  have x := (extract_of_after [] (p := p) (q := p) (by simp)).2
  simp only [string, append_of_isEmpty, pe, x]
  simp [hp, bind, Option.bind]

/-- Four hex digits are read from the four characters that write their value. -/
private theorem hexDigits_of_hex4 {p r : text.Pos} {n : Nat} (h : hex4 p = some (n, r)) :
    ∃ a b c d, after p = a :: b :: c :: d :: after r ∧ HexDigits a b c d n := by
  match e : after p with
  | a :: b :: c :: d :: t =>
    obtain ⟨rest, digits⟩ := (hex4_eq_some_iff e).1 h
    exact ⟨a, b, c, d, by rw [rest], digits⟩
  | [] | [_] | [_, _] | [_, _, _] =>
    rw [hex4_eq_none_of_length_lt (by simp [e])] at h
    cases h

/-- Four characters that write a value in hex digits are read as that value. -/
private theorem hex4_of_hexDigits {p : text.Pos} {a b c d : Char} {t : List Char} {n : Nat}
    (h : after p = a :: b :: c :: d :: t) (digits : HexDigits a b c d n) :
    ∃ r, after r = t ∧ hex4 p = some (n, r) := by
  obtain ⟨_, -, e₁⟩ := after_eq_cons h
  obtain ⟨_, -, e₂⟩ := after_eq_cons e₁
  obtain ⟨_, -, e₃⟩ := after_eq_cons e₂
  obtain ⟨_, -, e₄⟩ := after_eq_cons e₃
  exact ⟨_, e₄, (hex4_eq_some_iff h).2 ⟨e₄, digits⟩⟩

/-- A Unicode escape that is read is four hex digits outside the surrogates, or a pair. -/
private theorem unicodeEscape_inv {p r : text.Pos} {ch : Char}
    (h : unicodeEscape p = some (ch, r)) :
    (∃ a b c d n, after p = a :: b :: c :: d :: after r ∧ HexDigits a b c d n ∧
        (n < 0xd800 ∨ 0xe000 ≤ n) ∧ ch = Char.ofNat n) ∨
      (∃ a b c d w x y z hi lo,
        after p = a :: b :: c :: d :: '\\' :: 'u' :: w :: x :: y :: z :: after r ∧
        HexDigits a b c d hi ∧ HexDigits w x y z lo ∧ 0xd800 ≤ hi ∧ hi < 0xdc00 ∧
        0xdc00 ≤ lo ∧ lo < 0xe000 ∧
        ch = Char.ofNat (0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00))) := by
  cases hh : hex4 p with
  | none => simp [unicodeEscape_eq_none_of_hex4 hh] at h
  | some v =>
    obtain ⟨n, q⟩ := v
    obtain ⟨a, b, c, d, ep, dn⟩ := hexDigits_of_hex4 hh
    by_cases hi : 0xd800 ≤ n ∧ n < 0xdc00
    · -- A high surrogate: the reverse solidus, the `u` and the low half follow.
      right
      cases e1 : expect q '\\' with
      | none => simp [unicodeEscape, hh, bind, Option.bind, hi, e1] at h
      | some q1 =>
        cases e2 : expect q1 'u' with
        | none => simp [unicodeEscape, hh, bind, Option.bind, hi, e1, e2] at h
        | some q2 =>
          cases hl : hex4 q2 with
          | none => simp [unicodeEscape, hh, bind, Option.bind, hi, e1, e2, hl] at h
          | some u =>
            obtain ⟨lo, t⟩ := u
            obtain ⟨w, x, y, z, eq2, dl⟩ := hexDigits_of_hex4 hl
            by_cases lb : 0xdc00 ≤ lo ∧ lo < 0xe000
            · simp [unicodeEscape, hh, bind, Option.bind, hi, e1, e2, hl, lb] at h
              obtain ⟨h1, h2⟩ := h
              subst h1 h2
              refine ⟨a, b, c, d, w, x, y, z, n, lo, ?_, dn, dl, hi.1, hi.2, lb.1, lb.2, ?_⟩
              · rw [ep, after_of_expect e1, after_of_expect e2, eq2]
              · rw [show 65536 + 1024 * (n - 55296) + lo - 56320 =
                  65536 + 1024 * (n - 55296) + (lo - 56320) by omega]
            · simp [unicodeEscape, hh, bind, Option.bind, hi, e1, e2, hl] at h
              omega
    · by_cases lo : 0xdc00 ≤ n ∧ n < 0xe000
      · -- A low surrogate first is refused.
        simp [unicodeEscape, hh, bind, Option.bind, lo] at h
        omega
      · left
        simp [unicodeEscape, hh, bind, Option.bind] at h
        simp only [hi, lo, ↓reduceIte] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        subst h1 h2
        exact ⟨a, b, c, d, n, ep, dn, by omega, rfl⟩

/-- A string that is read is the text of characters that stand for what it holds. -/
private theorem unescapes_of_string : ∀ (fuel : Nat) {p q : text.Pos} {acc s : String},
    string fuel p acc = some (s, q) →
      ∃ cs ds, after p = cs ++ '"' :: after q ∧ Unescapes cs ds ∧ s = acc ++ String.ofList ds
  | 0, _, _, _, _, h => by simp [string] at h
  | n + 1, p, q, acc, s, h => by
    induction p using WellFounded.induction (String.Pos.wellFounded_gt) generalizing acc with
    | h p ih =>
      by_cases hp : p = text.endPos
      · subst hp
        simp [string, plainEnd] at h
      cases hc : plain (p.get hp)
      · rw [string_of_not_plain hp hc] at h
        split at h
        · -- The closing quotation mark.
          rename_i hq
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
          subst h1 h2
          exact ⟨[], [], by rw [after_eq_get_cons hp, hq]; rfl, .nil, by simp⟩
        split at h
        · rename_i hs
          split at h
          · cases h
          rename_i hn
          split at h
          · -- A Unicode escape, of one code unit or of a surrogate pair.
            rename_i hu
            obtain ⟨⟨ch, r⟩, hx, hr⟩ := Option.bind_eq_some_iff.1 h
            obtain ⟨cs, ds, ea, un, es⟩ := unescapes_of_string n hr
            rcases unicodeEscape_inv hx with
              ⟨a, b, c, d, m, ep, dn, sc, rfl⟩ |
                ⟨a, b, c, d, w, x, y, z, hi, lo, ep, dh, dl, h1, h2, h3, h4, hch⟩
            · refine ⟨'\\' :: 'u' :: a :: b :: c :: d :: cs, Char.ofNat m :: ds, ?_,
                .unicode dn sc un, ?_⟩
              · rw [after_eq_get_cons hp, after_eq_get_cons hn, hs, hu, ep, ea]
                rfl
              · rw [es, ← String.toList_inj]
                simp
            · refine ⟨'\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: w :: x :: y :: z :: cs,
                ch :: ds, ?_, by rw [hch]; exact .pair dh dl h1 h2 h3 h4 un, ?_⟩
              · rw [after_eq_get_cons hp, after_eq_get_cons hn, hs, hu, ep, ea]
                rfl
              · rw [es, ← String.toList_inj]
                simp
          · -- A two-character escape.
            obtain ⟨d, hd, hr⟩ := Option.bind_eq_some_iff.1 h
            obtain ⟨cs, ds, ea, un, es⟩ := unescapes_of_string n hr
            refine ⟨'\\' :: (p.next hp).get hn :: cs, d :: ds, ?_,
              .short (shortEscape_eq_some_iff.1 hd) un, ?_⟩
            · rw [after_eq_get_cons hp, after_eq_get_cons hn, hs, ea]
              rfl
            · rw [es, ← String.toList_inj]
              simp
        · cases h
      · -- A character without an escape.
        rw [string_of_plain hp hc] at h
        obtain ⟨cs, ds, ea, un, es⟩ := ih (p.next hp) String.Pos.lt_next _ h
        obtain ⟨low, quote, solidus⟩ := plain_eq_true_iff.1 hc
        refine ⟨p.get hp :: cs, p.get hp :: ds, ?_, .unescaped low quote solidus un, ?_⟩
        · rw [after_eq_get_cons hp, ea]
          rfl
        · rw [es, ← String.toList_inj]
          simp

/-- The text of characters that stand for others is read as those, given one step per character. -/
private theorem string_of_unescapes {cs ds : List Char} (un : Unescapes cs ds) :
    ∀ {fuel : Nat} {p : text.Pos} {acc : String} {X : List Char}, cs.length < fuel →
      after p = cs ++ '"' :: X →
        ∃ q, after q = X ∧ string fuel p acc = some (acc ++ String.ofList ds, q) := by
  induction un with
  | nil =>
    intro fuel p acc X hl h
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at hl; omega⟩
    obtain ⟨hp, g, e⟩ := after_eq_cons (by simpa using h)
    refine ⟨_, e, ?_⟩
    rw [string_of_not_plain hp (by rw [g]; rfl)]
    simp [g]
  | @unescaped c cs ds low quote solidus rest ih =>
    intro fuel p acc X hl h
    obtain ⟨hp, g, e⟩ := after_eq_cons (by simpa using h)
    rw [string_of_plain hp (by rw [g]; exact plain_eq_true_iff.2 ⟨low, quote, solidus⟩)]
    obtain ⟨q, hq, hs⟩ :=
      ih (fuel := fuel) (acc := acc.push (p.get hp)) (by simp at hl; omega) e
    refine ⟨q, hq, ?_⟩
    rw [hs, g]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    rw [← String.toList_inj]
    simp
  | @short e d cs ds mem rest ih =>
    intro fuel p acc X hl h
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at hl; omega⟩
    obtain ⟨hp, g, e1⟩ := after_eq_cons (by simpa using h)
    obtain ⟨hn, g2, e2⟩ := after_eq_cons e1
    obtain ⟨q, hq, hs⟩ := ih (fuel := n) (acc := acc.push d) (by simp at hl; omega) e2
    refine ⟨q, hq, ?_⟩
    rw [string_of_not_plain hp (by rw [g]; rfl)]
    simp [g, hn, g2, ne_u_of_mem mem, shortEscape_eq_some_iff.2 mem]
    rw [hs]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    rw [← String.toList_inj]
    simp
  | @unicode a b c d m cs ds digits scalar rest ih =>
    intro fuel p acc X hl h
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at hl; omega⟩
    obtain ⟨hp, g, e1⟩ := after_eq_cons (by simpa using h)
    obtain ⟨hn, g2, e2⟩ := after_eq_cons e1
    obtain ⟨r, hr, hx⟩ := hex4_of_hexDigits e2 digits
    have hu := (unicodeEscape_eq_of_not_surrogate hx scalar).1
    obtain ⟨q, hq, hs⟩ :=
      ih (fuel := n) (acc := acc.push (Char.ofNat m)) (by simp at hl; omega) hr
    refine ⟨q, hq, ?_⟩
    rw [string_of_not_plain hp (by rw [g]; rfl)]
    simp [g, hn, g2, hu]
    rw [hs]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    rw [← String.toList_inj]
    simp
  | @pair a b c d w x y z hi lo cs ds high low h1 h2 h3 h4 rest ih =>
    intro fuel p acc X hl h
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at hl; omega⟩
    obtain ⟨hp, g, e1⟩ := after_eq_cons (by simpa using h)
    obtain ⟨hn, g2, e2⟩ := after_eq_cons e1
    obtain ⟨r1, hr1, hx1⟩ := hex4_of_hexDigits e2 high
    obtain ⟨_, -, e3⟩ := after_eq_cons hr1
    obtain ⟨_, -, e4⟩ := after_eq_cons e3
    obtain ⟨t, ht, hx2⟩ := hex4_of_hexDigits e4 low
    have hu := (unicodeEscape_eq_of_pair hx1 (by rw [hr1, e4]) hx2 h1 h2 h3 h4).1
    obtain ⟨q, hq, hs⟩ := ih (fuel := n)
      (acc := acc.push (Char.ofNat (0x10000 + 1024 * (hi - 0xd800) + (lo - 0xdc00))))
      (by simp at hl; omega) ht
    refine ⟨q, hq, ?_⟩
    rw [string_of_not_plain hp (by rw [g]; rfl)]
    simp [g, hn, g2, hu]
    rw [hs]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    rw [← String.toList_inj]
    simp

/-- A string reads as what the characters before its first unescaped quotation mark stand for.

Those characters are the text from the position, up to that quotation mark, RFC 8259 §7.

The fuel is more than the count of characters after the position. -/
theorem string_eq_some_iff {fuel : Nat} {p q : text.Pos} {acc s : String}
    (hfuel : (after p).length < fuel) :
    string fuel p acc = some (s, q) ↔
      ∃ cs ds, after p = cs ++ '"' :: after q ∧ Unescapes cs ds ∧ s = acc ++ String.ofList ds := by
  refine ⟨unescapes_of_string fuel, ?_⟩
  rintro ⟨cs, ds, h, un, rfl⟩
  -- The characters before the quotation mark are fewer than the characters after the position.
  obtain ⟨r, hr, hs⟩ := string_of_unescapes un (fuel := fuel) (acc := acc)
    (by have := congrArg List.length h; simp at this; omega) h
  rw [hs, eq_of_after_eq hr]

end EthLib.Base.Json
