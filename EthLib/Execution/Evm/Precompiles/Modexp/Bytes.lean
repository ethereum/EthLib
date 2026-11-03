module

public import EthLib.Base.BigEndian
public import EthLib.Execution.Evm.Precompiles.Modexp.Constants

/-!
# `Modexp.Bytes`

Reading big-endian integers out of the call data.

EIP-198 says the call data is "assumed to be infinitely right-padded with zero bytes".

So every read is total: an index past the end reads as zero.

That is the rule of `buffer_read` in `forks/bpo2/vm/memory.py`, in execution-specs at `2c0c8e7`.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base

/-- The byte at index `i` of the call data, or `0` past its end. -/
def byteAt (data : ByteArray) (i : Nat) : UInt8 :=
  data.data.getD i 0

/-- `size` bytes of the call data from `start`, zero-padded on the right.

`buffer_read` in `forks/bpo2/vm/memory.py`. -/
def bufferRead (data : ByteArray) (start size : Nat) : List UInt8 :=
  (List.range size).map fun i => byteAt data (start + i)

/-- The big-endian integer held by `size` bytes of the call data from `start`. -/
def readNat (data : ByteArray) (start size : Nat) : Nat :=
  bytesToNat (bufferRead data start size)

end EthLib.Execution.Evm.Precompiles.Modexp
