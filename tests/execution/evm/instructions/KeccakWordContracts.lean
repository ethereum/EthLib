import EthLib.Execution.Proofs.Evm.Instructions.Keccak

/-!
# Contracts of `keccak256Word` on arbitrary inputs

Each example applies one public theorem, on arbitrary inputs where it takes any.

They fail to compile if a theorem changes its statement.
-/

open EthLib.Cryptography.Hash.Keccak (keccak256 hexBytes)
open EthLib.Execution.Evm.Instructions
open EthLib.Execution.Precompiles.Modexp (bytesToNat natToBytes natToBytes_bytesToNat)

/-- The digest of any message has exactly 32 bytes. -/
example (data : ByteArray) : (keccak256 data).toList.length = 32 :=
  length_keccak256_digest data

/-- The word is the big-endian value of the digest, not reduced modulo 2^256. -/
example (data : ByteArray) :
    (keccak256Word data).toNat = bytesToNat (keccak256 data).toList :=
  toNat_keccak256Word data

/-- The 32 big-endian bytes of the word give back the digest. -/
example (data : ByteArray) :
    natToBytes 32 (keccak256Word data).toNat = (keccak256 data).toList :=
  natToBytes_toNat_keccak256Word data

/-- Equal words come from equal digests. -/
example (a b : ByteArray) (h : keccak256Word a = keccak256Word b) :
    keccak256 a = keccak256 b :=
  digest_eq_of_keccak256Word_eq h

/-- Any known digest gives the word its bytes write. -/
example (data digest : ByteArray) (h : (keccak256 data).toArray = digest.data) :
    keccak256Word data = BitVec.ofNat 256 (bytesToNat digest.data.toList) :=
  keccak256Word_of_digest h

/-- Any byte list survives the round trip through its value. -/
example (bytes : List UInt8) :
    natToBytes bytes.length (bytesToNat bytes) = bytes :=
  natToBytes_bytesToNat bytes

/-- The empty message. -/
example :
    keccak256Word ByteArray.empty
      = 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470#256 :=
  keccak256Word_empty

/-- The byte `0xCC`. -/
example :
    keccak256Word (hexBytes "CC")
      = 0xEEAD6DBFC7340A56CAEDC044696A168870549A6A7F6F56961E84A54BD9970B8A#256 :=
  keccak256Word_cc
