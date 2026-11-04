module

public import EthLib.Base.Bytes

/-!
# `Base.Hash32`

A 32-byte hash, the size of a Keccak-256 digest.

In section 4.4 of the Yellow Paper, Shanghai version, the hashes of a block header are in `B_32`:
[`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).
-/

@[expose] public section

namespace EthLib.Base

/-- Exactly 32 bytes, such as a Keccak-256 digest or the root of a trie. -/
abbrev Hash32 := Bytes32

end EthLib.Base
