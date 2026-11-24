module

public import EthLib.Base.ByteOrder
public import EthLib.Base.Bytes

/-!
# `Base.U256`

The 256-bit unsigned integer, the word of the EVM, by section 9.1 of the [Yellow Paper][paper].

The Yellow Paper is the Shanghai version.

[paper]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Base

/-- An unsigned integer below 2^256.

It is a bit vector, so `+`, `-` and `*` wrap modulo 2^256. -/
abbrev U256 := BitVec 256

namespace U256

/-- The integer that a word encodes in two's complement, in `[-2^255, 2^255)`.

The signed instructions of Appendix H of the Yellow Paper read a word this way. -/
def toSigned (w : U256) : Int :=
  -- A word with its top bit set stands for that word minus 2^256.
  if w.toNat < 2 ^ 255 then w.toNat else w.toNat - 2 ^ 256

/-- The word that encodes an integer in two's complement.

Outside `[-2^255, 2^255)`, the integer reduces modulo 2^256.

The instructions pass it only integers inside that range. -/
def fromSigned (v : Int) : U256 := BitVec.ofInt 256 v

/-- The word that 32 bytes write, the first byte the most significant.

Any 32 bytes write a value below 2^256, so the reduction modulo 2^256 never applies. -/
def fromBeBytes (bytes : Vector UInt8 32) : U256 := BitVec.ofNat 256 (ByteOrder.ofBE bytes.toList)

/-- The word as 32 bytes, the first byte the most significant.

The opening of Appendix H of the Yellow Paper reads a word as a big-endian integer.

A word is below 2^256, so it always fits in 32 bytes. -/
def toBeBytes (w : U256) : Bytes32 :=
  ByteOrder.toBE 32 w.toNat

end U256

end EthLib.Base
