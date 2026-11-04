module

public import EthLib.Base.U256
public import EthLib.Cryptography.Hash.Keccak

/-!
# `Evm.Instructions.Keccak`

The KECCAK256 instruction of the EVM.

Source: Appendix H.2 of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

Every fork since Frontier computes the same result.

The instruction hashes a region of memory and pushes the digest, read as a big-endian word.

Only that last step is here, as a function of the bytes read.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The word pushed for `data`: the Keccak-256 digest of `data`, read as a big-endian word.

The digest has exactly 32 bytes, so it fits in one word with nothing cut. -/
def keccak (data : ByteArray) : U256 := U256.fromBeBytes (keccak256 data)

end EthLib.Execution.Evm.Instructions
