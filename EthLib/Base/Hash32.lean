module

public import EthLib.Base.Bytes

/-!
# `Base.Hash32`

A 32-byte hash, the size of a Keccak-256 digest.

Source: `Hash32 = Bytes32` in [`crypto/hash.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/crypto/hash.py#L19) of execution-specs at `2c0c8e7`.
-/

@[expose] public section

namespace EthLib.Base

/-- `Hash32`: exactly 32 bytes, such as a Keccak-256 digest or the root of a trie. -/
abbrev Hash32 := Bytes32

end EthLib.Base
