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

/-- A hex digit has the same value in uppercase, and a character that is not a digit stays one. -/
theorem hexValue?_toUpper (c : Char) : hexValue? c.toUpper = hexValue? c := by
  by_cases h : 'a'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'z'.val.toNat
  · have key := toUpper_val_of_lower h.1 h.2
    unfold hexValue?
    simp only [Char.le_def, Char.toNat, UInt32.le_iff_toNat_le]
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
