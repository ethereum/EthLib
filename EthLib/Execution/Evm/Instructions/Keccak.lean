module

public import EthLib.Base.U256
public import EthLib.Cryptography.Hash.Keccak

/-!
# `Evm.Instructions.Keccak`

The KECCAK256 instruction of the EVM.

Source: [`forks/frontier/vm/instructions/keccak.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/instructions/keccak.py#L56-L58) of execution-specs at `2c0c8e7`.

Every later fork there computes the same result, up to Bogota.

The instruction hashes a region of memory and pushes the digest, read as a big-endian word.

Only that last step is here, as a function of the bytes read.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- `keccak`: the word pushed for `data`, which is `U256.from_be_bytes(keccak256(data))`.

The digest has exactly 32 bytes, so it fits in one word with nothing cut. -/
def keccak (data : ByteArray) : U256 := U256.fromBeBytes (keccak256 data)

end EthLib.Execution.Evm.Instructions
