module

public import EthLib.Execution.Evm.Instructions.Keccak
public import EthLib.Base.Proofs.U256
public import EthLib.Cryptography.Proofs.Hash.Keccak256

/-!
# Proofs: `Evm.Instructions.Keccak`

- The word is the big-endian value of the 32 digest bytes, with no reduction modulo 2^256.
- Two messages give the same word only if they give the same digest.

The known answers are the empty message and the byte `0xCC`.

Their digests are `Len = 0` and `Len = 8` of `ShortMsgKAT_256.txt`, which `Proofs.Hash.Keccak256` checks.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256 hexBytes keccak256_empty keccak256_len8)

/-- The word is the integer the digest writes, the first byte the most significant. -/
theorem toNat_keccak (data : ByteArray) :
    (keccak data).toNat = bytesToNat (keccak256 data).toList :=
  U256.toNat_fromBeBytes _

/-- The word determines the digest. -/
theorem keccak256_eq_of_keccak_eq {a b : ByteArray} (h : keccak a = keccak b) :
    keccak256 a = keccak256 b :=
  U256.fromBeBytes_injective h

/-! ## Known answers -/

/-- The empty message: `0xc5d2...a470`, the digest of `Len = 0` with its first byte the most significant. -/
theorem keccak_empty :
    keccak ByteArray.empty
      = 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470#256 := by
  -- The word reads the digest through its array, which the known answer gives.
  show BitVec.ofNat 256 (bytesToNat (keccak256 ByteArray.empty).toArray.toList) = _
  rw [keccak256_empty]
  decide +kernel

/-- The byte `0xCC`: `0xeead...0b8a`, the digest of `Len = 8` with its first byte the most significant. -/
theorem keccak_cc :
    keccak (hexBytes "CC")
      = 0xEEAD6DBFC7340A56CAEDC044696A168870549A6A7F6F56961E84A54BD9970B8A#256 := by
  -- The word reads the digest through its array, which the known answer gives.
  show BitVec.ofNat 256 (bytesToNat (keccak256 (hexBytes "CC")).toArray.toList) = _
  rw [keccak256_len8]
  decide +kernel

end EthLib.Execution.Evm.Instructions
