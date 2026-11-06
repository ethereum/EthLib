module

public import EthLib.Cryptography.Sphincs
public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Bytes

/-!
# Proofs: EthLib's bytes as the security model's bit vectors

The security proof writes leanSPHINCS over bit vectors, and EthLib over byte vectors.

A bit vector becomes its little-endian bytes, and the model's byte encoding lists those bytes.

So EthLib builds a hash input from the converted values, and the model from the values themselves.

The model is generic over its parameters.

EthLib's configuration has layers of heights 10, 8 and 8, and 24 FORS trees of height 10.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

export EthLib.Cryptography.HashSig (ofBV getElem_ofBV toList_ofBV ofBV_ofNat ofBV_eq_uintToBytes
  ofBV_ofNat_bytesToUint ofBV_inj ofOutput queryH)

/-! ## The parameters -/

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

/-- A public parameter's 16 bytes. -/
abbrev ofParam {w : Nat} (x : BitVec w) : PublicParam := ofBV PUBLIC_PARAM_LEN x

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

/-! ## The two halves of a hash value -/

/-- The first 16 bytes of a hash value are the bytes of its low 128 bits. -/
theorem halfOf_zero_ofOutput (x : HashSig.HashOutput) :
    halfOf 0 (ofOutput x) = ofDigest (HashSig.truncateHash x) := by
  apply Vector.ext
  intro i hi
  simp only [N] at hi
  simp only [halfOf, Vector.getElem_ofFn, Fin.isValue, Fin.val_zero, Nat.mul_zero, Nat.zero_add]
  exact HashSig.getElem_ofOutput_of_lt x i hi

/-- The last 16 bytes of a hash value are the bytes of its high 128 bits. -/
theorem halfOf_one_ofOutput (x : HashSig.HashOutput) :
    halfOf 1 (ofOutput x) = ofDigest (SphincsSecurity.upperHash x) := by
  apply Vector.ext
  intro i hi
  simp only [N] at hi
  simp only [halfOf, Vector.getElem_ofFn, getElem_ofBV, SphincsSecurity.upperHash,
    HashSig.digestBits]
  rw [HashSig.extractLsb'_byte_low x 128 128 i (by omega)]
  exact (getElem_ofBV 32 x (16 * 1 + i) (by omega)).trans (by congr 2; omega)

/-- Half `i mod 2` of a hash value: the first for even `i`, the last for odd `i`. -/
theorem halfOf_mod_two_ofOutput (x : HashSig.HashOutput) (i : Nat) :
    halfOf ⟨i % 2, Nat.mod_lt _ (by decide)⟩ (ofOutput x)
      = ofDigest (SphincsSecurity.hashHalf i x) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · simp only [h, SphincsSecurity.hashHalf, ↓reduceIte]
    exact halfOf_zero_ofOutput x
  · simp only [h, SphincsSecurity.hashHalf, Nat.one_ne_zero, ↓reduceIte]
    exact halfOf_one_ofOutput x

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
