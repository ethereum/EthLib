module

public import EthLib.Serialization.Proofs.Ssz.Codec.Loops
public import EthLib.Serialization.Ssz.Codec.Json

/-! Hex strings written by the JSON mapping read back as the bytes they came from. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Lean

/-- The two digits one byte is written as, high half first. -/
private def hexPair (byte : UInt8) : List Char :=
  [Base.hexDigitChar ⟨byte.toNat / 16, by have := byte.toNat_lt; omega⟩,
    Base.hexDigitChar ⟨byte.toNat % 16, by omega⟩]

/-- The digits a byte string is written as, behind no marker. -/
private def hexDigitsOf (data : Bytes) : List Char :=
  data.toList.flatMap hexPair

/-- Writing appends the digits of each byte in turn. -/
private theorem toHex_eq (data : Bytes) :
    (toHex data).toList = '0' :: 'x' :: hexDigitsOf data := by
  -- The fold starts from the marker and pushes two characters per byte.
  have general : ∀ (bytes : List UInt8) (text : String),
      (bytes.foldl (fun text byte =>
        (text.push (Base.hexDigitChar ⟨byte.toNat / 16, by have := byte.toNat_lt; omega⟩)).push
          (Base.hexDigitChar ⟨byte.toNat % 16, by omega⟩)) text).toList
        = text.toList ++ bytes.flatMap hexPair := by
    intro bytes
    induction bytes <;> simp [*, hexPair]
  simpa [toHex, hexDigitsOf, Array.foldl_toList] using general data.toList "0x"

/-- Each of the sixteen digits reads back as its own value. -/
private theorem hexDigit_hexDigitChar (digit : Fin 16) :
    hexDigit (Base.hexDigitChar digit) = .ok digit.val := by
  -- Sixteen characters, each checked against the three ranges the reader tests.
  obtain ⟨value, small⟩ := digit
  rcases value with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | value
  all_goals first | rfl | omega

/-- Reading the digits of a byte string gives that byte string back. -/
private theorem hexBytes_digits (data : Bytes) : hexBytes (hexDigitsOf data) = .ok data := by
  -- Two digits at a time rebuild one byte, and the rest of the string follows.
  have general : ∀ (bytes : List UInt8),
      hexBytes (bytes.flatMap hexPair) = .ok bytes.toArray := by
    intro bytes
    induction bytes with
    | nil => simp [hexBytes_nil]
    | cons byte rest ih =>
      simp [hexPair, hexBytes_cons, hexDigit_hexDigitChar, Nat.div_add_mod, ih, Bind.bind,
        Except.bind, pure, Except.pure, UInt8.ofNat_toNat]
  simpa [hexDigitsOf] using general data.toList

/-- A hex string the mapping wrote reads back as the bytes it was written from. -/
theorem ofHex_toHex (data : Bytes) : ofHex (toHex data) = .ok data := by
  simp [ofHex, toHex_eq, hexBytes_digits]

end EthLib.Serialization.Ssz
