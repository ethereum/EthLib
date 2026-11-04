module

public import EthLib.Execution.Evm.Instructions.Keccak
public import EthLib.Base.Proofs.U256

/-!
# Proofs: `Evm.Instructions.Keccak`

- The word is the big-endian value of the 32 digest bytes, with no reduction modulo 2^256.
- Two messages give the same word only if they give the same digest.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The word is the integer the digest writes, the first byte the most significant. -/
theorem toNat_keccak (data : ByteArray) :
    (keccak data).toNat = bytesToNat (keccak256 data).toList :=
  U256.toNat_fromBeBytes _

/-- The word determines the digest. -/
theorem keccak256_eq_of_keccak_eq {a b : ByteArray} (h : keccak a = keccak b) :
    keccak256 a = keccak256 b :=
  U256.fromBeBytes_injective h

end EthLib.Execution.Evm.Instructions
