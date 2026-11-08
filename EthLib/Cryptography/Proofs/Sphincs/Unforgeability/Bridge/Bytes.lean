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

EthLib writes them with `toByte`, and the model with its big-endian bytes of a bit vector.

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

/-- Byte `i` of the big-endian bytes of `n`, as a number, from the integer. -/
private theorem toNat_byte_ofNat (w a n : Nat) :
    (UInt8.ofBitVec ((BitVec.ofNat w n).extractLsb' a 8)).toNat = n % 2 ^ w / 2 ^ a % 2 ^ 8 := by
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]

/-- EthLib's `len` big-endian bytes of `n` are the model's, of `n` as a `8 len`-bit vector. -/
theorem natToBytes_eq_bytesBE (len n : Nat) :
    Base.natToBytes len n = SphincsSecurity.bytesBE len (BitVec.ofNat (8 * len) n) := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih =>
    rw [Base.natToBytes_succ, ih, SphincsSecurity.bytesBE, SphincsSecurity.bytesBE,
      List.ofFn_succ', List.concat_eq_append]
    congr 1
    · -- A higher byte of `n` is the byte one place lower of `n / 256`.
      refine congrArg List.ofFn (funext fun i => UInt8.toNat.inj ?_)
      rw [toNat_byte_ofNat, toNat_byte_ofNat]
      apply Nat.eq_of_testBit_eq
      intro j
      have hi := i.isLt
      simp only [Fin.val_castSucc, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
        show (256 : Nat) = 2 ^ 8 from rfl]
      rw [show j + 8 * (len + 1 - 1 - i.val) = j + 8 * (len - 1 - i.val) + 8 by omega]
      by_cases hj : j < 8
      · simp only [hj, decide_true, Bool.true_and,
          show j + 8 * (len - 1 - i.val) + 8 < 8 * (len + 1) by omega,
          show j + 8 * (len - 1 - i.val) < 8 * len by omega]
      · simp [hj]
    · -- The last byte is `n mod 256`.
      congr 1
      apply UInt8.toNat.inj
      rw [toNat_byte_ofNat, Fin.val_last, show len + 1 - 1 - len = 0 by omega, Nat.mul_zero,
        pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))]
      simp

/-- `toByte k n`, as a list, is the model's big-endian bytes of `n` on `8 k` bits. -/
@[simp] theorem toList_toByte_bytesBE (k n : Nat) :
    (toByte k n).toList = SphincsSecurity.bytesBE k (BitVec.ofNat (8 * k) n) := by
  rw [← natToBytes_eq_bytesBE]
  rfl

/-- The model's big-endian integer of a byte string is EthLib's. -/
theorem beInt_eq_bytesToNat (bytes : List UInt8) :
    SphincsSecurity.beInt bytes = Base.bytesToNat bytes := by
  simp only [SphincsSecurity.beInt, Base.bytesToNat, Nat.mul_comm 256]

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
