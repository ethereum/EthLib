module

public import EthLib.Base.Bytes

/-!
# `Evm.Machine.Memory`

How the EVM reads a window of a byte buffer, such as the call data of a precompile.

A read is total: an index past the end of the buffer reads as zero.

So a short buffer reads as if padded with zeros, and bytes past the window are ignored.

The memory of a frame is a byte array, which grows in whole words before each access.

So a read or a write of memory stays within its size.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- `size` bytes of the buffer from `start`, padded with zeros on the right, as a byte array.

Appendix H.2 of the Yellow Paper reads call data this way, as zero past its end.

The bytes inside the buffer are copied as one block, then the zeros follow.

The start can be any word, far past any index that a compiled byte array holds.

So the block is cut to the buffer first, and a start past its end copies nothing.

A read that ends inside the buffer needs no zeros, so it appends none. -/
def bufferBytes (data : ByteArray) (start size : Nat) : ByteArray :=
  -- The bytes `d[x]` of the buffer `d` for `start ≤ x < min(start + size, ||d||)`, as one block.
  let inside := if start < data.size then data.extract start (min (start + size) data.size)
    else .empty
  -- Then `d[x] = 0` for each `x ≥ ||d||`, up to `size` bytes, as Appendix H.2 reads `I_d`.
  if inside.size = size then inside
  else inside ++ ByteArray.mk (Array.replicate (size - inside.size) 0)

/-- `size` bytes of the buffer from `start`, padded with zeros on the right, as a list. -/
def bufferRead (data : ByteArray) (start size : Nat) : List UInt8 :=
  (bufferBytes data start size).data.toList

/-- The memory with `value` written from `start`.

The memory must hold the whole range, so the size does not change.

An empty value changes nothing, whatever its start.

That start can reach 2^256, which no compiled index of a byte array holds, so it is never read.

The bytes of the value replace those of the range, in place when nothing else holds the memory. -/
def memoryWrite (memory : ByteArray) (start : Nat) (value : ByteArray) : ByteArray :=
  -- An empty value writes nothing.
  if value.size = 0 then memory
  -- `mu'_m[start + i] = value[i]` for each `i < ||value||`.
  else value.copySlice 0 memory start value.size

/-- The `size` bytes of memory from `start`.

The memory must hold the whole range.

An empty range reads nothing, and its start is never read, as for a write. -/
def memoryReadBytes (memory : ByteArray) (start size : Nat) : ByteArray :=
  -- `mu_m[start ... (start + size - 1)]`, and nothing for `size = 0`.
  if size = 0 then .empty else memory.extract start (start + size)

/-- The memory grown by `n` zero bytes.

No growth leaves the memory as it is, with no copy. -/
def memoryExtend (memory : ByteArray) (n : Nat) : ByteArray :=
  -- §9.1: all locations of memory are initially 0, and no write reaches past the active memory.
  if n = 0 then memory else memory ++ ByteArray.mk (Array.replicate n 0)

end EthLib.Execution.Evm
