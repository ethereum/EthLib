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

/-- Exactly 32 bytes, such as a Keccak-256 digest or the root of a trie.

The two layers read the name in two ways.

The execution layer gives another name to any 32 bytes, so a hash and other 32 bytes mix freely.

The consensus layer makes it a type of its own, kept apart from other 32 bytes such as a root.

EthLib takes the first reading: the name abbreviates 32 bytes, in both layers.

Making it a type of its own takes a pull request that converts every use. -/
abbrev Hash32 := Bytes32

/-- The 32 zero bytes, which stand for no block hash, no root or an empty node of a branch. -/
def ZERO_HASH : Hash32 := Vector.replicate 32 0

end EthLib.Base
