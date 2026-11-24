module

public import EthLib.Base.U256

/-!
# `Base.Address`

The 20-byte address of an account, in `B_20` by section 4.1 of the [Yellow Paper][paper].

The Yellow Paper is the Shanghai version.

[paper]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Base

/-- An address: exactly 20 bytes.

Lean core orders addresses byte by byte, from the first byte, with a lawful linear order. -/
abbrev Address := Vector UInt8 20

/-- The word of an address: its 20 bytes after 12 zero bytes, read big-endian.

The opening of Appendix H of the Yellow Paper converts an address to a word this way.

Twenty bytes write a value below 2^160, so the reduction modulo 2^256 never applies. -/
def Address.toU256 (a : Address) : U256 := BitVec.ofNat 256 (ByteOrder.ofBE a.toList)

/-- The address in a word: the last 20 of its 32 big-endian bytes.

The opening of Appendix H of the Yellow Paper converts a word to an address this way.

The first 12 bytes are dropped, so the address is the word modulo 2^160. -/
def toAddressMasked (w : U256) : Address := (U256.toBeBytes w).drop 12

end EthLib.Base
