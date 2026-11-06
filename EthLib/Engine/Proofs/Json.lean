module

public import EthLib.Engine.Json
public import EthLib.Base.Hex

/-!
# Proofs: the hex digits of the JSON decoders

The decoders read a hex digit by its ASCII byte.

They read back each digit that `hexDigitChar` writes, whichever case they allow.
-/

public section

namespace EthLib.Engine.Json

open EthLib.Base

/-- The decoders read the value of each digit that `hexDigitChar` writes. -/
theorem hexValue_hexDigitChar (upper : Bool) (n : Fin 16) :
    hexValue upper (hexDigitChar n).toUInt8 = some n.val.toUInt8 := by
  revert n
  decide +revert

end EthLib.Engine.Json
