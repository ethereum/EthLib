module

public import EthLib.Base.U256
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Precompiles.Modexp.Bytes

/-!
# `Evm.Instructions.Keccak`

The word that KECCAK256 pushes, as a function of the data it hashes.

Source: [`forks/frontier/vm/instructions/keccak.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/instructions/keccak.py#L56-L58) of execution-specs at `2c0c8e7`, function `keccak`.

Its operation is `hashed = keccak256(data)`, then `push(evm.stack, U256.from_be_bytes(hashed))`.

Only that step is here.

The reads of the stack and the memory, the gas and the program counter wait for the EVM frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Execution.Precompiles.Modexp (bytesToNat)

/-- `keccak`: the word pushed for the data `data`, the big-endian reading of its Keccak-256 digest.

`U256.from_be_bytes` rejects a buffer of more than 32 bytes.

The digest has exactly 32, so nothing is rejected and nothing is cut. -/
def keccak256Word (data : ByteArray) : U256 :=
  BitVec.ofNat 256 (bytesToNat (keccak256 data).toList)

end EthLib.Execution.Evm.Instructions
