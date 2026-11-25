module

public import EthLib.Base.Hex

/-!
# Proofs: hex decoding reads back hex encoding

Decoding the two digits of each byte gives the bytes back.

A digit in uppercase decodes to the same value, so the case of the digits never matters.
-/

@[expose] public section

namespace EthLib.Base

/-- The characters of a hex string: `0x`, then the two digits of each byte in turn. -/
theorem toList_hexString (bytes : List UInt8) :
    (hexString bytes).toList = '0' :: 'x' :: bytes.flatMap byteHexDigits := by
  -- The fold starts from the marker and pushes two characters per byte.
  have general : ∀ (bytes : List UInt8) (text : String),
      (bytes.foldl (fun text byte => (byteHexDigits byte).foldl String.push text)
        text).toList = text.toList ++ bytes.flatMap byteHexDigits := by
    intro bytes
    induction bytes with
    | nil => simp
    | cons byte rest ih =>
      intro text
      rw [List.foldl_cons, ih]
      simp [byteHexDigits]
  simpa [hexString] using general bytes "0x"

/-- The hex digits of a list of bytes number two per byte. -/
theorem length_flatMap_byteHexDigits (bytes : List UInt8) :
    (bytes.flatMap byteHexDigits).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [List.flatMap_cons, List.length_append, ih, byteHexDigits, List.length_cons,
      List.length_nil]
    omega

/-- Each lowercase digit decodes to its value. -/
theorem hexValue?_hexDigitChar (n : Fin 16) : hexValue? (hexDigitChar n) = some n.val.toUInt8 := by
  revert n
  decide

/-- Each lowercase digit decodes to its value when uppercase is not allowed. -/
theorem hexValue?_false_hexDigitChar (n : Fin 16) :
    hexValue? (hexDigitChar n) false = some n.val.toUInt8 := by
  revert n
  decide

/-- Each uppercase digit decodes to the same value. -/
theorem hexValue?_toUpper_hexDigitChar (n : Fin 16) :
    hexValue? (hexDigitChar n).toUpper = some n.val.toUInt8 := by
  revert n
  decide

/-- A lowercase letter is 32 below the code of its uppercase letter. -/
private theorem toUpper_val_of_lower {c : Char} (low : 'a'.val.toNat ≤ c.val.toNat)
    (high : c.val.toNat ≤ 'z'.val.toNat) : c.toUpper.val.toNat + 32 = c.val.toNat := by
  have h : 'a'.val ≤ c.val ∧ c.val ≤ 'z'.val := by
    simp only [UInt32.le_iff_toNat_le]
    exact ⟨low, high⟩
  simp only [Char.toUpper, h, and_self, ↓reduceDIte, UInt32.toNat_add, UInt32.toNat_sub]
  have ea : 'a'.val.toNat = 97 := rfl
  have eA : 'A'.val.toNat = 65 := rfl
  have ez : 'z'.val.toNat = 122 := rfl
  omega

/-- The code of any other character is kept in uppercase. -/
private theorem toUpper_of_not_lower {c : Char} (h : ¬ ('a'.val.toNat ≤ c.val.toNat ∧
    c.val.toNat ≤ 'z'.val.toNat)) : c.toUpper = c := by
  have h' : ¬ ('a'.val ≤ c.val ∧ c.val ≤ 'z'.val) := by
    simpa only [UInt32.le_iff_toNat_le] using h
  unfold Char.toUpper
  simp only [h', ↓reduceDIte]

/-- The code of each of the sixteen digits: `0` to `9`, then `a` to `f`. -/
private theorem hexDigitChar_val (digit : Fin 16) :
    (hexDigitChar digit).val.toNat = if digit.val < 10 then 48 + digit.val else 87 + digit.val := by
  revert digit
  decide

/-- The code of the uppercase form of each of the sixteen digits: `0` to `9`, then `A` to `F`. -/
private theorem hexDigitChar_toUpper_val (digit : Fin 16) :
    (hexDigitChar digit).toUpper.val.toNat =
      if digit.val < 10 then 48 + digit.val else 55 + digit.val := by
  revert digit
  decide

/-- A character that decodes is the lowercase digit of its value.

When uppercase is allowed, it may also be the uppercase form of that digit.

So the decoder accepts no character outside the digits of the letter case it is given. -/
theorem hexValue?_eq_some {c : Char} {upper : Bool} {n : UInt8}
    (read : hexValue? c upper = some n) :
    ∃ digit : Fin 16, digit.val.toUInt8 = n ∧
      (c = hexDigitChar digit ∨ upper = true ∧ c = (hexDigitChar digit).toUpper) := by
  have e0 : ('0' : Char).val.toNat = 48 := rfl
  have e9 : ('9' : Char).val.toNat = 57 := rfl
  have ea : ('a' : Char).val.toNat = 97 := rfl
  have ef : ('f' : Char).val.toNat = 102 := rfl
  have eA : ('A' : Char).val.toNat = 65 := rfl
  have eF : ('F' : Char).val.toNat = 70 := rfl
  have same : ∀ d : Char, d.val.toNat = c.val.toNat → c = d := fun d h =>
    Char.ext (UInt32.toNat_inj.mp h.symm)
  unfold hexValue? at read
  simp only [Char.le_def, Char.toNat, UInt32.le_iff_toNat_le, e0, e9, ea, ef, eA, eF] at read
  -- Each of the three ranges gives the digit of the value it reads.
  split at read
  · rename_i h
    cases read
    refine ⟨⟨c.val.toNat - 48, by omega⟩, rfl, .inl (same _ ?_)⟩
    rw [hexDigitChar_val]
    dsimp only
    split <;> omega
  · split at read
    · rename_i h
      cases read
      refine ⟨⟨c.val.toNat - 97 + 10, by omega⟩, rfl, .inl (same _ ?_)⟩
      rw [hexDigitChar_val]
      dsimp only
      split <;> omega
    · split at read
      · rename_i h
        cases read
        refine ⟨⟨c.val.toNat - 65 + 10, by omega⟩, rfl, .inr ⟨h.1, same _ ?_⟩⟩
        rw [hexDigitChar_toUpper_val]
        dsimp only
        split <;> omega
      · cases read

/-- A hex digit has the same value in uppercase, and a character that is not a digit stays one. -/
theorem hexValue?_toUpper (c : Char) : hexValue? c.toUpper = hexValue? c := by
  by_cases h : 'a'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'z'.val.toNat
  · have key := toUpper_val_of_lower h.1 h.2
    unfold hexValue?
    simp only [Char.le_def, Char.toNat, UInt32.le_iff_toNat_le, true_and]
    generalize c.toUpper = d at *
    have e0 : '0'.val.toNat = 48 := rfl
    have e9 : '9'.val.toNat = 57 := rfl
    have ea : 'a'.val.toNat = 97 := rfl
    have ef : 'f'.val.toNat = 102 := rfl
    have ez : 'z'.val.toNat = 122 := rfl
    have eA : 'A'.val.toNat = 65 := rfl
    have eF : 'F'.val.toNat = 70 := rfl
    simp only [e0, e9, ea, ef, ez, eA, eF] at *
    repeat' split
    all_goals first | rfl | (exfalso; omega) | (congr 2; omega)
  · rw [toUpper_of_not_lower h]

/-- Pairs of digits decode to the same bytes with every digit in uppercase. -/
theorem hexBytesFrom?_map_toUpper :
    ∀ (digits : List Char) (out : ByteArray),
      hexBytesFrom? (digits.map Char.toUpper) out = hexBytesFrom? digits out
  | [], _ => rfl
  | [_], _ => rfl
  | high :: low :: rest, out => by
    simp only [List.map_cons, hexBytesFrom?, hexValue?_toUpper, hexBytesFrom?_map_toUpper rest]

/-- Decoding succeeds exactly on pairs of hex digits, and appends the byte of each pair.

Byte `i` is sixteen times the digit at `2 i` plus the digit at `2 i + 1`. -/
theorem hexBytesFrom?_eq_some_iff :
    ∀ {cs : List Char} {out r : ByteArray},
      hexBytesFrom? cs out = some r ↔
        ∃ xs : List UInt8, cs.length = 2 * xs.length ∧ r = out ++ ⟨xs.toArray⟩ ∧
          ∀ (i : Nat) (hi : i < xs.length), ∃ u v : UInt8,
            cs[2 * i]?.bind (hexValue? ·) = some u ∧ cs[2 * i + 1]?.bind (hexValue? ·) = some v ∧
              xs[i] = 16 * u + v
  | [], out, r => by
    simp only [hexBytesFrom?, Option.some.injEq, List.length_nil]
    constructor
    · rintro rfl
      exact ⟨[], rfl, by apply ByteArray.ext; simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    · rintro ⟨xs, hl, rfl, -⟩
      obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      apply ByteArray.ext
      simp
  | [_], out, r => by
    simp only [hexBytesFrom?, reduceCtorEq, List.length_singleton, false_iff, not_exists]
    intro xs hl
    omega
  | high :: low :: rest, out, r => by
    simp only [hexBytesFrom?, Option.bind_eq_bind]
    constructor
    · intro h
      obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨xs, hl, hr, hidx⟩ := hexBytesFrom?_eq_some_iff.mp h
      refine ⟨(16 * u + v) :: xs, by simp [hl]; omega, ?_, fun i hi => ?_⟩
      · rw [hr]
        apply ByteArray.ext
        simp
      · cases i with
        | zero => exact ⟨u, v, by simpa using hu, by simpa using hv, rfl⟩
        | succ i =>
          obtain ⟨a, b, ha, hb, hx⟩ := hidx i (by simpa using hi)
          refine ⟨a, b, ?_, ?_, by simpa using hx⟩
          · rw [show 2 * (i + 1) = 2 * i + 2 by omega]
            simpa using ha
          · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by omega]
            simpa using hb
    · rintro ⟨xs, hl, rfl, hidx⟩
      cases xs with
      | nil => simp at hl
      | cons x xs =>
        obtain ⟨u, v, hu, hv, hx⟩ := hidx 0 (by simp)
        simp only [List.getElem?_cons_zero, Option.bind_some, Nat.mul_zero, Nat.zero_add,
          List.getElem?_cons_succ] at hu hv
        rw [hu, Option.bind_some, hv, Option.bind_some]
        apply hexBytesFrom?_eq_some_iff.mpr
        refine ⟨xs, by simp at hl; omega, ?_, fun i hi => ?_⟩
        · simp only [List.getElem_cons_zero] at hx
          rw [← hx]
          apply ByteArray.ext
          simp
        · obtain ⟨a, b, ha, hb, hxi⟩ := hidx (i + 1) (by simpa using hi)
          refine ⟨a, b, ?_, ?_, by simpa using hxi⟩
          · rw [show 2 * (i + 1) = 2 * i + 2 by omega] at ha
            simpa using ha
          · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by omega] at hb
            simpa using hb

/-- A byte is sixteen times its high digit plus its low digit. -/
theorem toUInt8_div_add_mod (byte : UInt8) :
    16 * (byte.toNat / 16).toUInt8 + (byte.toNat % 16).toUInt8 = byte := by
  apply UInt8.toNat_inj.mp
  have := byte.toNat_lt
  simp [UInt8.toNat_add, UInt8.toNat_mul, Nat.toUInt8_eq, UInt8.toNat_ofNat]
  omega

/-- Decoding appends the bytes that the digits encode to the bytes so far. -/
theorem hexBytesFrom?_flatMap (bytes : List UInt8) (out : ByteArray) :
    hexBytesFrom? (bytes.flatMap byteHexDigits) out = some (out ++ ⟨bytes.toArray⟩) := by
  induction bytes generalizing out with
  | nil =>
    simp only [List.flatMap_nil, hexBytesFrom?]
    exact congrArg some ByteArray.append_empty.symm
  | cons byte rest ih =>
    simp only [List.flatMap_cons, byteHexDigits, List.cons_append, List.nil_append,
      hexBytesFrom?, hexValue?_hexDigitChar, Option.bind_eq_bind, Option.bind_some]
    rw [toUInt8_div_add_mod, ih]
    congr 1
    apply ByteArray.ext
    simp

/-- Decoding the hex digits of some bytes gives the bytes. -/
theorem hexBytes?_flatMap (bytes : List UInt8) :
    hexBytes? (bytes.flatMap byteHexDigits) = some ⟨bytes.toArray⟩ := by
  simp [hexBytes?, hexBytesFrom?_flatMap]

end EthLib.Base
