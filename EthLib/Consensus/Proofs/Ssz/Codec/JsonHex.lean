import EthLib.Consensus.Ssz.Codec.Json

/-! Hex strings written by the JSON mapping read back as the bytes they came from. -/

namespace EthLib.Consensus.Ssz

open Lean

/-- The two digits one byte is written as, high half first. -/
private def hexPair (byte : UInt8) : List Char :=
  [hexAlphabet[byte.toNat >>> 4]!, hexAlphabet[byte.toNat &&& 0xF]!]

/-- The digits a byte string is written as, behind no marker. -/
private def hexDigitsOf (data : Bytes) : List Char :=
  data.toList.flatMap hexPair

/-- Writing appends the digits of each byte in turn. -/
private theorem toHex_eq (data : Bytes) :
    (toHex data).toList = '0' :: 'x' :: hexDigitsOf data := by
  -- The fold starts from the marker and pushes two characters per byte.
  have general : ∀ (bytes : List UInt8) (text : String),
      (bytes.foldl (fun text byte =>
        (text.push hexAlphabet[byte.toNat >>> 4]!).push
          hexAlphabet[byte.toNat &&& 0xF]!) text).toList
        = text.toList ++ bytes.flatMap hexPair := by
    intro bytes
    induction bytes <;> simp [*, hexPair]
  simpa [toHex, hexDigitsOf, Array.foldl_toList] using general data.toList "0x"

/-- Each of the sixteen digits reads back as its own value. -/
private theorem hexDigit_alphabet {value : Nat} (small : value < 16) :
    hexDigit hexAlphabet[value]! = .ok value := by
  -- Sixteen characters, each checked against the three ranges the reader tests.
  rcases value with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | value
  all_goals first | rfl | omega

/-- A byte is its high half times sixteen plus its low half. -/
private theorem byte_halves (byte : UInt8) :
    16 * (byte.toNat >>> 4) + (byte.toNat &&& 0xF) = byte.toNat := by
  rw [Nat.and_two_pow_sub_one_eq_mod byte.toNat 4, Nat.shiftRight_eq_div_pow]
  omega

/-- Reading the digits of a byte string gives that byte string back. -/
private theorem hexBytes_digits (data : Bytes) : hexBytes (hexDigitsOf data) = .ok data := by
  -- Two digits at a time rebuild one byte, and the rest of the string follows.
  have general : ∀ (bytes : List UInt8),
      hexBytes (bytes.flatMap hexPair) = .ok bytes.toArray := by
    intro bytes
    induction bytes with
    | nil => simp [hexBytes]
    | cons byte rest ih =>
      have high : byte.toNat >>> 4 < 16 := by
        rw [Nat.shiftRight_eq_div_pow]
        have := byte.toNat_lt
        omega
      have low : byte.toNat &&& 0xF < 16 := Nat.and_lt_two_pow _ (by decide : 15 < 2 ^ 4)
      simp [hexPair, hexBytes, hexDigit_alphabet high, hexDigit_alphabet low,
        byte_halves byte, ih, Bind.bind, Except.bind, pure, Except.pure,
        UInt8.ofNat_toNat]
  simpa [hexDigitsOf] using general data.toList

/-- A hex string the mapping wrote reads back as the bytes it was written from. -/
theorem ofHex_toHex (data : Bytes) : ofHex (toHex data) = .ok data := by
  simp [ofHex, toHex_eq, hexBytes_digits]

end EthLib.Consensus.Ssz
