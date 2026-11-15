module

public import EthLib.Cryptography.Xmss
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Types
public import EthLib.Cryptography.Proofs.HashSig.Bytes

/-!
# Proofs: EthLib's bytes as the security proof's bit vectors

The security proof writes leanXMSS over bit vectors, EthLib over byte vectors.

Both schemes share the conversion of a bit vector to its little-endian bytes.

Here each leanXMSS object gets its own byte count, and a hash value its two halves.

The proof's own little-endian encoding has exactly those bytes.

So EthLib builds a hash input from the converted values.

The proof builds the same input from the values themselves.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

export EthLib.Cryptography.HashSig (ofBV getElem_ofBV toList_ofBV ofBV_ofNat ofBV_eq_uintToBytes
  ofBV_ofNat_bytesToUint ofBV_inj ofOutput)

/-! ## The bytes of each object

Each EthLib object has its own length constant, so each gets its own conversion and its own lemma.

The lemmas state the proof's encodings as it writes them: `bytesLE 16` and `bytesLE 32`. -/

/-- A digest's 16 bytes. -/
abbrev ofDigest {w : Nat} (x : BitVec w) : Digest := ofBV DIGEST_LEN x

/-- A public parameter's 16 bytes. -/
abbrev ofParam {w : Nat} (x : BitVec w) : PublicParam := ofBV PUBLIC_PARAM_LEN x

/-- A randomizer's 16 bytes. -/
abbrev ofRandomizer {w : Nat} (x : BitVec w) : Randomizer := ofBV RANDOMIZER_LEN x

/-- A seed's 32 bytes. -/
abbrev ofSeed {w : Nat} (x : BitVec w) : Seed := ofBV SEED_LEN x

/-- A message's 32 bytes. -/
abbrev ofMessage {w : Nat} (x : BitVec w) : Message := ofBV MESSAGE_LEN x

@[simp] theorem toList_ofDigest (x : XmssSecurity.Digest) :
    (ofDigest x).toList = XmssSecurity.bytesLE 16 x :=
  toList_ofBV 16 x

@[simp] theorem toList_ofParam (x : XmssSecurity.PublicParameter) :
    (ofParam x).toList = XmssSecurity.bytesLE 16 x :=
  toList_ofBV 16 x

@[simp] theorem toList_ofRandomizer (x : XmssSecurity.Randomness) :
    (ofRandomizer x).toList = XmssSecurity.bytesLE 16 x :=
  toList_ofBV 16 x

@[simp] theorem toList_ofSeed (x : XmssSecurity.MasterSeed) :
    (ofSeed x).toList = XmssSecurity.bytesLE 32 x :=
  toList_ofBV 32 x

@[simp] theorem toList_ofMessage (x : XmssSecurity.Message) :
    (ofMessage x).toList = XmssSecurity.bytesLE 32 x :=
  toList_ofBV 32 x

/-! ## The two halves of a hash value -/

/-- The first 16 bytes of a hash value are the bytes of its low 128 bits. -/
theorem halfOf_zero_ofOutput (x : XmssSecurity.HashOutput) :
    halfOf 0 (ofOutput x) = ofDigest (XmssSecurity.truncateHash x) := by
  apply Vector.ext
  intro i hi
  simp only [DIGEST_LEN] at hi
  simp only [halfOf, Vector.getElem_ofFn]
  simp only [Fin.isValue, Fin.val_zero, Nat.mul_zero, Nat.zero_add]
  exact HashSig.getElem_ofOutput_of_lt x i hi

/-- The last 16 bytes of a hash value are the bytes of its high 128 bits. -/
theorem halfOf_one_ofOutput (x : XmssSecurity.HashOutput) :
    halfOf 1 (ofOutput x) = ofDigest (XmssSecurity.upperHash x) := by
  apply Vector.ext
  intro i hi
  simp only [DIGEST_LEN] at hi
  simp only [halfOf, Vector.getElem_ofFn, getElem_ofBV, XmssSecurity.upperHash,
    XmssSecurity.digestBits]
  rw [HashSig.extractLsb'_byte_low x 128 128 i (by omega)]
  congr 2
  omega

/-- The half of a hash value that starts chain `i`: the first for even `i`, the last for odd `i`. -/
theorem halfOf_mod_two_ofOutput (x : XmssSecurity.HashOutput) (i : Nat) :
    halfOf ⟨i % 2, Nat.mod_lt _ (by decide)⟩ (ofOutput x)
      = ofDigest (XmssSecurity.hashHalf i x) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · simp only [h, XmssSecurity.hashHalf, ↓reduceIte]
    exact halfOf_zero_ofOutput x
  · simp only [h, XmssSecurity.hashHalf, Nat.one_ne_zero, ↓reduceIte]
    exact halfOf_one_ofOutput x

end EthLib.Cryptography.Xmss.Unforgeability
