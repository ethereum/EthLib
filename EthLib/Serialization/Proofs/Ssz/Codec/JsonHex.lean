module

public import EthLib.Base.Proofs.Hex
public import EthLib.Serialization.Proofs.Ssz.Codec.Loops
public import EthLib.Serialization.Ssz.Codec.Json

/-! Hex strings written by the JSON mapping read back as the bytes they came from. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Lean

/-- The digits a byte string is written as, behind no marker. -/
private def hexDigitsOf (data : Bytes) : List Char :=
  data.toList.flatMap Base.byteHexDigits

/-- Writing appends the digits of each byte in turn. -/
private theorem toHex_eq (data : Bytes) :
    (toHex data).toList = '0' :: 'x' :: hexDigitsOf data :=
  Base.toList_hexString data.toList

/-- Reading the digits of a byte string gives that byte string back. -/
private theorem hexBytes_digits (data : Bytes) : hexBytes (hexDigitsOf data) = .ok data := by
  simp [hexBytes, hexDigitsOf, Base.hexBytes?_flatMap]

/-- A hex string the mapping wrote reads back as the bytes it was written from. -/
theorem ofHex_toHex (data : Bytes) : ofHex (toHex data) = .ok data := by
  simp [ofHex, toHex_eq, hexBytes_digits]

end EthLib.Serialization.Ssz
