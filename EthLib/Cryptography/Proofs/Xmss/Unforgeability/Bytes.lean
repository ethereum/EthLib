import EthLib.Cryptography.Xmss
import EthLib.Cryptography.Proofs.Xmss.Types
import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Types

/-!
# Proofs: EthLib's bytes as the security proof's bit vectors

The security proof writes leanXMSS over bit vectors, EthLib over byte vectors.

A bit vector is the integer its little-endian bytes encode.

```text
    x : BitVec (8 n)   <->   ofBV n x : Vector UInt8 n,   byte i = bits 8 i to 8 i + 7
```

The proof's own encoding is `bytesLE`, and `ofBV n x` has exactly those bytes.

So EthLib builds a hash input from `ofBV` values.

The proof builds the same input from the values themselves.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-! ## Bit vectors as bytes -/

/-- The `n` low little-endian bytes of a bit vector.

The byte count is an argument, not read off the width, so each EthLib type names its own. -/
def ofBV (n : Nat) {w : Nat} (x : BitVec w) : Vector UInt8 n :=
  Vector.ofFn fun i => UInt8.ofBitVec (x.extractLsb' (8 * i.val) 8)

/-- Byte `i` of `ofBV n x` is bits `8 i` to `8 i + 7` of `x`. -/
@[simp] theorem getElem_ofBV (n : Nat) {w : Nat} (x : BitVec w) (i : Nat) (hi : i < n) :
    (ofBV n x)[i] = UInt8.ofBitVec (x.extractLsb' (8 * i) 8) := by
  simp [ofBV]

/-- `ofBV n` lists the bytes the proof's `bytesLE n` does. -/
theorem toList_ofBV (n : Nat) (x : BitVec (8 * n)) :
    (ofBV n x).toList = XmssSecurity.bytesLE n x := by
  apply List.ext_getElem (by simp [XmssSecurity.bytesLE])
  intro i _ _
  simp [XmssSecurity.bytesLE]

/-- Bits `a` to `a + c - 1` of `z mod 2^b` are those of `z`, when `a + c <= b`. -/
private theorem mod_div_mod (z a b c : Nat) (h : a + c ≤ b) :
    z % 2 ^ b / 2 ^ a % 2 ^ c = z / 2 ^ a % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < c
  · simp [hj, show j + a < b by omega]
  · simp [hj]

/-- The bytes of the `8 n`-bit vector of an integer are its `n` low little-endian bytes. -/
theorem ofBV_ofNat (n z : Nat) : ofBV n (BitVec.ofNat (8 * n) z) = littleEndian n z := by
  apply Vector.ext
  intro i hi
  simp only [getElem_ofBV, littleEndian, Vector.getElem_ofFn]
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  -- Byte `i` of `z mod 2^(8n)` is byte `i` of `z`, since `i < n`.
  rw [mod_div_mod z (8 * i) (8 * n) 8 (by omega),
    show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [pow_mul]; norm_num]
  simp

/-- The bytes of a bit vector of any width are the little-endian bytes of its integer. -/
theorem ofBV_eq_littleEndian (n : Nat) {w : Nat} (y : BitVec w) :
    ofBV n y = littleEndian n y.toNat := by
  apply Vector.ext
  intro i hi
  simp only [getElem_ofBV, littleEndian, Vector.getElem_ofFn]
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [pow_mul]; norm_num]
  simp

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

/-- A hash value's 32 bytes. -/
abbrev ofOutput {w : Nat} (x : BitVec w) : Vector UInt8 32 := ofBV 32 x

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

/-- The bytes of a fixed-size object, as a list. -/
@[simp] theorem toList_data_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).data.toList = v.toList :=
  rfl

/-! ## Back from bytes

An object from outside enters the proof through its integer.

A signature that an adversary sends is one such object.

That works at any width.

So it needs no cast between EthLib's length constants and the proof's widths. -/

/-- Put the integer of `n` bytes in a bit vector at least `8 n` bits wide.

Then its bytes are the bytes we started from. -/
theorem ofBV_ofNat_fromLittleEndian {n w : Nat} (v : Vector UInt8 n) (hw : 8 * n ≤ w) :
    ofBV n (BitVec.ofNat w (fromLittleEndian v)) = v := by
  rw [ofBV_eq_littleEndian, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, littleEndian_fromLittleEndian]
  calc fromLittleEndian v < 256 ^ n := fromLittleEndian_lt v
    _ = 2 ^ (8 * n) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw

/-- Two bit vectors of at most `8 n` bits with the same `n` bytes are equal. -/
theorem ofBV_inj {n w : Nat} {x y : BitVec w} (hw : w ≤ 8 * n) (h : ofBV n x = ofBV n y) :
    x = y := by
  rw [ofBV_eq_littleEndian, ofBV_eq_littleEndian] at h
  have := congrArg fromLittleEndian h
  rw [fromLittleEndian_littleEndian, fromLittleEndian_littleEndian] at this
  -- Both integers are below `2^w <= 256^n`, so the modulus does nothing.
  have hpow : 2 ^ w ≤ 256 ^ n := by
    calc 2 ^ w ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by decide) hw
      _ = 256 ^ n := by rw [pow_mul]; norm_num
  apply BitVec.eq_of_toNat_eq
  rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt hpow), Nat.mod_eq_of_lt (lt_of_lt_of_le y.isLt hpow)]
    at this

/-! ## The two halves of a hash value -/

/-- Bits `8 i` to `8 i + 7` of the low part of a bit vector are the vector's own. -/
private theorem extractLsb'_byte_low {w : Nat} (x : BitVec w) (lo m i : Nat) (h : 8 * i + 8 ≤ m) :
    (x.extractLsb' lo m).extractLsb' (8 * i) 8 = x.extractLsb' (lo + 8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  -- Dividing by `2^(8i)` inside `mod 2^m` keeps the low byte.
  rw [mod_div_mod _ (8 * i) m 8 h, Nat.div_div_eq_div_mul, ← pow_add]

/-- The first 16 bytes of a hash value are the bytes of its low 128 bits. -/
theorem halfOf_zero_ofOutput (x : XmssSecurity.HashOutput) :
    halfOf 0 (ofOutput x) = ofDigest (XmssSecurity.truncateHash x) := by
  apply Vector.ext
  intro i hi
  simp only [DIGEST_LEN] at hi
  simp only [halfOf, Vector.getElem_ofFn, getElem_ofBV, XmssSecurity.truncateHash,
    XmssSecurity.digestBits]
  rw [extractLsb'_byte_low x 0 128 i (by omega)]
  congr 2
  omega

/-- The last 16 bytes of a hash value are the bytes of its high 128 bits. -/
theorem halfOf_one_ofOutput (x : XmssSecurity.HashOutput) :
    halfOf 1 (ofOutput x) = ofDigest (XmssSecurity.upperHash x) := by
  apply Vector.ext
  intro i hi
  simp only [DIGEST_LEN] at hi
  simp only [halfOf, Vector.getElem_ofFn, getElem_ofBV, XmssSecurity.upperHash,
    XmssSecurity.digestBits]
  rw [extractLsb'_byte_low x 128 128 i (by omega)]
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
