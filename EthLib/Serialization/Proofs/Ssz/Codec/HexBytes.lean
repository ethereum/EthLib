module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonHex
public import EthLib.Serialization.Ssz.Codec.HexBytes

/-!
# Proofs: bytes of a fixed count read from hex text

The hex text of bytes reads back as those bytes.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The hex text of bytes reads back as those bytes when the count fits. -/
theorem parseHexBytes_toHex {count : Nat} (data : Vector UInt8 count) :
    parseHexBytes count (toHex ⟨data.toArray⟩) = some data := by
  simp [parseHexBytes, Base.exactBytes?, Base.exactArray?_toArray, ofHex_toHex]

end EthLib.Serialization.Ssz
