module

public import EthLib.Base.BigEndian
public import EthLib.Execution.Evm.Machine.Memory
public import EthLib.Execution.Evm.Precompiles.Modexp.Constants

/-!
# `Modexp.Encoding`

Reading big-endian integers out of the call data.

EIP-198 says the call data is "assumed to be infinitely right-padded with zero bytes".

So every read is total: an index past the end reads as zero, as `Evm.Machine.Memory` reads it.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base
open EthLib.Execution.Evm (bufferRead)

/-- The big-endian integer held by `size` bytes of the call data from `start`. -/
def readNat (data : ByteArray) (start size : Nat) : Nat :=
  bytesToNat (bufferRead data start size)

end EthLib.Execution.Evm.Precompiles.Modexp
