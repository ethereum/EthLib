module

public import EthLib.Base.Bytes
public import EthLib.Serialization.Ssz.Codec.Json

/-!
# `Serialization.Ssz.Codec.HexBytes`

Bytes of a fixed count, read from hex text such as a key or a root in a query.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The bytes of a given count that a text writes as hex after a lowercase `0x`, or none.

The digits may be in either case. -/
def parseHexBytes (count : Nat) (text : String) : Option (Vector UInt8 count) :=
  match ofHex text with
  | .ok data => Base.exactBytes? count ⟨data⟩
  | .error _ => none

end EthLib.Serialization.Ssz
