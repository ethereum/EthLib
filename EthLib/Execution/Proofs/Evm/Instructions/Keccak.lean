module

public import EthLib.Execution.Evm.Instructions.Keccak
public import EthLib.Execution.Proofs.Precompiles.Modexp.Bytes
public import EthLib.Cryptography.Proofs.Hash.Keccak256

/-!
# Proofs: `Evm.Instructions.Keccak`

- The word is the number that the 32 digest bytes write in big-endian order, below 2^256, so nothing is cut.
- The digest is the 32 big-endian bytes of the word, so no digest byte is lost.
- Two inputs give the same word only if they give the same digest.

The known answers at the end are the empty message and the byte `0xCC`, whose digests `Proofs.Hash.Keccak256` already checks.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Execution.Precompiles.Modexp (bytesToNat natToBytes)

/-- The Keccak-256 digest, as a list, has exactly 32 bytes. -/
theorem length_keccak256_digest (data : ByteArray) : (keccak256 data).toList.length = 32 := by
  rw [Vector.length_toList]
  rfl

/-- The word is the integer that the digest writes, with the first byte the most significant. -/
theorem toNat_keccak256Word (data : ByteArray) :
    (keccak256Word data).toNat = bytesToNat (keccak256 data).toList := by
  have h := Precompiles.Modexp.bytesToNat_lt (keccak256 data).toList
  rw [length_keccak256_digest] at h
  simp only [keccak256Word, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- The digest is the 32 big-endian bytes of the word. -/
theorem natToBytes_toNat_keccak256Word (data : ByteArray) :
    natToBytes 32 (keccak256Word data).toNat = (keccak256 data).toList := by
  rw [toNat_keccak256Word, ← length_keccak256_digest data]
  exact Precompiles.Modexp.natToBytes_bytesToNat _

/-- The word determines the digest. -/
theorem digest_eq_of_keccak256Word_eq {a b : ByteArray}
    (h : keccak256Word a = keccak256Word b) : keccak256 a = keccak256 b := by
  have h1 := natToBytes_toNat_keccak256Word a
  have h2 := natToBytes_toNat_keccak256Word b
  rw [h] at h1
  exact Vector.toList_inj.mp (h1.symm.trans h2)

/-! ## Known answers -/

/-- The word of a known digest: the integer written by the known bytes. -/
theorem keccak256Word_of_digest {data : ByteArray} {digest : ByteArray}
    (h : (keccak256 data).toArray = digest.data) :
    keccak256Word data = BitVec.ofNat 256 (bytesToNat digest.data.toList) := by
  -- The list of the digest is the list of the array that the known answer names.
  have hl : (keccak256 data).toList = digest.data.toList := by
    rw [← Vector.toList_toArray (xs := keccak256 data), h]
  rw [keccak256Word, hl]

/-- The empty message: the digest of `Len = 0` of `ShortMsgKAT_256.txt`, as a big-endian integer. -/
theorem keccak256Word_empty :
    keccak256Word ByteArray.empty
      = 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470#256 := by
  rw [keccak256Word_of_digest Cryptography.Hash.Keccak.keccak256_empty]
  decide +kernel

/-- The byte `0xCC`: the digest of `Len = 8` of `ShortMsgKAT_256.txt`, as a big-endian integer. -/
theorem keccak256Word_cc :
    keccak256Word (Cryptography.Hash.Keccak.hexBytes "CC")
      = 0xEEAD6DBFC7340A56CAEDC044696A168870549A6A7F6F56961E84A54BD9970B8A#256 := by
  rw [keccak256Word_of_digest Cryptography.Hash.Keccak.keccak256_len8]
  decide +kernel

end EthLib.Execution.Evm.Instructions
