module

public import EthLib.Cryptography.Sphincs
public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Bytes

/-!
# Proofs: EthLib's bytes as the security model's bit vectors

The security proof writes leanSPHINCS over bit vectors, and EthLib over byte vectors.

A digest, a seed or a message becomes the little-endian bytes of its bit vector.

The model's byte encoding lists those bytes, so EthLib hashes the bytes the model hashes.

The address words and the counters are big-endian in both.

EthLib writes them with `toByte`, and the model writes the integer of a bit vector.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

export EthLib.Cryptography.HashSig (ofBV getElem_ofBV toList_ofBV ofBV_ofNat ofBV_eq_toLE
  ofBV_ofNat_ofLE ofBV_inj ofOutput queryH)

/-! ## The parameters

The model is generic over its parameters.

EthLib's configuration has layers of heights 10, 8 and 8, and 24 FORS trees of height 10. -/

/-- EthLib's configuration in the model: 26 index bits in three layers, the lower two of height 8.

FORS has 24 trees of height 10, and the model's cap is 1,182,000,000 signatures. -/
abbrev params : SphincsSecurity.Params := .layered 26 3 8 24 10 1182000000

scoped instance : SphincsSecurity.Params := params

/-! ## The bytes of each object -/

/-- The model's little-endian bytes are the shared ones. -/
theorem bytesLE_eq (n : Nat) (x : BitVec (8 * n)) :
    SphincsSecurity.bytesLE n x = HashSig.bytesLE n x :=
  rfl

/-- A digest's 16 bytes. -/
abbrev ofDigest {w : Nat} (x : BitVec w) : Digest := ofBV N x

/-- The 16 bytes of `PK.seed`, which the model calls the public parameter. -/
abbrev ofParam {w : Nat} (x : BitVec w) : PkSeed := ofBV N x

/-- A randomizer's 16 bytes. -/
abbrev ofRandomizer {w : Nat} (x : BitVec w) : Randomizer := ofBV RANDOMIZER_LEN x

/-- A seed's 32 bytes. -/
abbrev ofSeed {w : Nat} (x : BitVec w) : Seed := ofBV SEED_LEN x

/-- A message's 32 bytes. -/
abbrev ofMessage {w : Nat} (x : BitVec w) : Message := ofBV MESSAGE_LEN x

@[simp] theorem toList_ofDigest (x : SphincsSecurity.Digest) :
    (ofDigest x).toList = SphincsSecurity.bytesLE 16 x :=
  toList_ofBV 16 x

@[simp] theorem toList_ofParam (x : SphincsSecurity.PublicParameter) :
    (ofParam x).toList = SphincsSecurity.bytesLE 16 x :=
  toList_ofBV 16 x

@[simp] theorem toList_ofRandomizer (x : SphincsSecurity.Randomness) :
    (ofRandomizer x).toList = SphincsSecurity.bytesLE 16 x :=
  toList_ofBV 16 x

@[simp] theorem toList_ofSeed (x : SphincsSecurity.MasterSeed) :
    (ofSeed x).toList = SphincsSecurity.bytesLE 32 x :=
  toList_ofBV 32 x

@[simp] theorem toList_ofMessage (x : SphincsSecurity.Message) :
    (ofMessage x).toList = SphincsSecurity.bytesLE 32 x :=
  toList_ofBV 32 x

/-- The 32 bytes of a hash value, such as `SK.prf`. -/
@[simp] theorem toList_ofOutput (x : HashSig.HashOutput) :
    (ofOutput x).toList = SphincsSecurity.bytesLE 32 x :=
  toList_ofBV 32 x

/-- The 32 bytes of a hash value, packed as EthLib's hash output such as `SK.prf`. -/
@[simp] theorem toList_data_packBytes_ofOutput (x : HashSig.HashOutput) :
    (packBytes (n := HASH_LEN) (ofOutput x)).data.toList = SphincsSecurity.bytesLE 32 x :=
  toList_ofBV 32 x

/-- EthLib's tag is the model's: the 11 ASCII bytes of `leanSPHINCS`. -/
theorem seedTag_eq : SEED_TAG = SphincsSecurity.seedTag :=
  rfl

/-- The tag has 11 bytes, the length byte of the framed message. -/
theorem ofNat_length_seedTag : UInt8.ofNat SphincsSecurity.seedTag.length = 0x0b :=
  rfl

/-! ## The first 16 bytes of a hash value -/

/-- `Trunc_16` of a hash value is the bytes of its low 128 bits. -/
theorem trunc_ofOutput_truncateHash (x : HashSig.HashOutput) :
    trunc N (ofOutput x) = ofDigest (HashSig.truncateHash x) := by
  apply Vector.ext
  intro i hi
  simp only [N] at hi
  simp only [trunc, Vector.getElem_ofFn]
  exact HashSig.getElem_ofOutput_of_lt x i hi

/-! ## Big-endian words -/

/-- `toByte k n`, as a list, is the big-endian writing of `n` as a bit vector of `8 k` bits.

The model writes its values as bit vectors, so the right side goes through one to match it. -/
@[simp] theorem toList_toByte_toBE (k n : Nat) :
    (toByte k n).toList = (Base.ByteOrder.toBE k (BitVec.ofNat (8 * k) n).toNat).toList := by
  rw [BitVec.toNat_ofNat, Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from rfl, Base.ByteOrder.toBE_mod]
  rfl

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
