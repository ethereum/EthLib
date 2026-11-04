module

/-!
# `Base.Bytes`

Byte strings of a fixed length, with the length in the type.

Source: section 3 of the Yellow Paper, Shanghai version, in
[`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

It writes `B_n` for the byte strings of length `n`.
-/

@[expose] public section

namespace EthLib.Base

/-- `B_32`: exactly 32 bytes, such as a storage key. -/
abbrev Bytes32 := Vector UInt8 32

end EthLib.Base
