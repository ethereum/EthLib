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

/-- `buffer_read`: `size` bytes of the buffer from `start`, padded with zeros on the right.

Source: [`forks/frontier/vm/memory.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/memory.py#L63) of execution-specs at `2c0c8e7`. -/
def bufferRead (data : ByteArray) (start size : Nat) : List UInt8 :=
  (List.range size).map fun i => byteAt data (start + i)

end EthLib.Execution.Evm
