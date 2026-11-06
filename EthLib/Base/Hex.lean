module

/-!
# `Base.Hex`

The sixteen hex digits, as the encodings that write bytes in hex use them.
-/

@[expose] public section

namespace EthLib.Base

/-- The sixteen hex digits in lowercase, in order of value. -/
def hexAlphabet : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

/-- The lowercase hex digit of a value below sixteen. -/
def hexDigitChar (n : Fin 16) : Char :=
  hexAlphabet[n]

/-- The two lowercase hex digits of a byte, high digit first. -/
def byteHexDigits (byte : UInt8) : List Char :=
  [hexDigitChar ⟨byte.toNat / 16, by have := byte.toNat_lt; omega⟩,
    hexDigitChar ⟨byte.toNat % 16, by omega⟩]

/-- Bytes as lowercase hex digits behind `0x`, two digits per byte. -/
def hexString (bytes : List UInt8) : String :=
  bytes.foldl (init := "0x") fun text byte => (byteHexDigits byte).foldl String.push text

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

end EthLib.Base
