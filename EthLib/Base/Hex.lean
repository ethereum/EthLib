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

end EthLib.Base
