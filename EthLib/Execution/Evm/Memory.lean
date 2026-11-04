module

/-!
# `Evm.Memory`

How the EVM reads a window of a byte buffer, such as the call data of a precompile.

A read is total: an index past the end of the buffer reads as zero.

So a short buffer reads as if padded with zeros, and bytes past the window are ignored.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- The byte at index `i` of the buffer, or `0` past its end. -/
def byteAt (data : ByteArray) (i : Nat) : UInt8 :=
  data.data.getD i 0

/-- `size` bytes of the buffer from `start`, padded with zeros on the right.

Appendix H.2 of the Yellow Paper reads call data this way, as zero past its end. -/
def bufferRead (data : ByteArray) (start size : Nat) : List UInt8 :=
  (List.range size).map fun i => byteAt data (start + i)

end EthLib.Execution.Evm
