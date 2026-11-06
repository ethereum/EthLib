module

public import EthLib.Base.Bytes
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Cryptography.Proofs.HashSig.Oracle

/-!
# Proofs: bit vectors as bytes, and the oracle's answers as bytes

The security games write values as bit vectors, and EthLib writes them as byte vectors.

A bit vector is the integer its little-endian bytes encode.

A bit vector `x : BitVec (8 n)` becomes a byte vector of length `n`.

Byte `i` holds bits `8 i` to `8 i + 7`.

So the 32 bytes of an oracle answer start with the 16 bytes of its low 128 bits.

Those 16 bytes are uniform when the answer is.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleSpec OracleComp ENNReal
open EthLib.Base (bytesToUint uintToBytes)

/-! ## Bit vectors as bytes -/

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The `n` low little-endian bytes of a bit vector.

The byte count is an argument, not read off the width, so each EthLib type names its own. -/
def ofBV (n : Nat) {w : Nat} (x : BitVec w) : Vector UInt8 n :=
  Vector.ofFn fun i => UInt8.ofBitVec (x.extractLsb' (8 * i.val) 8)

/-- Byte `i` of `ofBV n x` is bits `8 i` to `8 i + 7` of `x`. -/
@[simp] theorem getElem_ofBV (n : Nat) {w : Nat} (x : BitVec w) (i : Nat) (hi : i < n) :
    (ofBV n x)[i] = UInt8.ofBitVec (x.extractLsb' (8 * i) 8) := by
  simp [ofBV]

/-- `ofBV n` lists the bytes that `bytesLE n` does. -/
theorem toList_ofBV (n : Nat) (x : BitVec (8 * n)) :
    (ofBV n x).toList = bytesLE n x := by
  apply List.ext_getElem (by simp [bytesLE])
  intro i _ _
  simp [bytesLE]

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
theorem ofBV_ofNat (n z : Nat) : ofBV n (BitVec.ofNat (8 * n) z) = uintToBytes n z := by
  apply Vector.ext
  intro i hi
  simp only [getElem_ofBV, uintToBytes, Vector.getElem_ofFn]
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  -- Byte `i` of `z mod 2^(8n)` is byte `i` of `z`, since `i < n`.
  rw [mod_div_mod z (8 * i) (8 * n) 8 (by omega),
    show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [pow_mul]; norm_num]
  simp

/-- The bytes of a bit vector of any width are the little-endian bytes of its integer. -/
theorem ofBV_eq_uintToBytes (n : Nat) {w : Nat} (y : BitVec w) :
    ofBV n y = uintToBytes n y.toNat := by
  apply Vector.ext
  intro i hi
  simp only [getElem_ofBV, uintToBytes, Vector.getElem_ofFn]
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [pow_mul]; norm_num]
  simp

/-- `LE_{8k}(z)`, listed, is `bytesLE k` of `z` as an `8 k`-bit vector. -/
theorem toList_uintToBytes (k z : Nat) :
    (uintToBytes k z).toList = bytesLE k (BitVec.ofNat (8 * k) z) := by
  rw [← ofBV_ofNat, toList_ofBV]

/-- The integer that the bytes of a bit vector encode is the bit vector's. -/
theorem bytesToUint_ofBV (n : Nat) (x : BitVec (8 * n)) :
    bytesToUint (ofBV n x) = x.toNat := by
  rw [ofBV_eq_uintToBytes, Base.bytesToUint_uintToBytes]
  -- The integer is below `2^(8n) = 256^n`, so the modulus does nothing.
  exact Nat.mod_eq_of_lt (by simpa [pow_mul] using x.isLt)

/-- The byte that holds a 5-bit field below a 3-bit field, as one 8-bit vector. -/
theorem append_ofNat (tau mu : Nat) (htau : tau < 32) (hmu : mu < 8) :
    BitVec.ofNat 3 mu ++ BitVec.ofNat 5 tau = BitVec.ofNat (8 * 1) (tau + 32 * mu) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmu,
    show tau % 2 ^ 5 = tau from Nat.mod_eq_of_lt (by omega)]
  -- The high field sits above the 5 low bits, so `or` is a sum.
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## Byte arrays as lists -/

/-- The bytes of a fixed-size object, as a list. -/
@[simp] theorem toList_data_packBytes {n : Nat} (v : Vector UInt8 n) :
    (Base.packBytes v).data.toList = v.toList :=
  rfl

/-- The bytes of two byte arrays, joined, as a list. -/
@[simp] theorem toList_data_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  simp [ByteArray.data_append]

/-! ## Back from bytes

An object from outside enters a game through its integer.

A signature that an adversary sends is one such object.

That works at any width, so it needs no cast between byte counts and bit widths. -/

/-- Put the integer of `n` bytes in a bit vector at least `8 n` bits wide.

Then its bytes are the bytes we started from. -/
theorem ofBV_ofNat_bytesToUint {n w : Nat} (v : Vector UInt8 n) (hw : 8 * n ≤ w) :
    ofBV n (BitVec.ofNat w (bytesToUint v)) = v := by
  rw [ofBV_eq_uintToBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Base.uintToBytes_bytesToUint]
  calc bytesToUint v < 256 ^ n := Base.bytesToUint_lt v
    _ = 2 ^ (8 * n) := by rw [pow_mul]; norm_num
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw

/-- Two bit vectors of at most `8 n` bits with the same `n` bytes are equal. -/
theorem ofBV_inj {n w : Nat} {x y : BitVec w} (hw : w ≤ 8 * n) (h : ofBV n x = ofBV n y) :
    x = y := by
  rw [ofBV_eq_uintToBytes, ofBV_eq_uintToBytes] at h
  have := congrArg bytesToUint h
  rw [Base.bytesToUint_uintToBytes, Base.bytesToUint_uintToBytes] at this
  -- Both integers are below `2^w <= 256^n`, so the modulus does nothing.
  have hpow : 2 ^ w ≤ 256 ^ n := by
    calc 2 ^ w ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by decide) hw
      _ = 256 ^ n := by rw [pow_mul]; norm_num
  apply BitVec.eq_of_toNat_eq
  rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt hpow), Nat.mod_eq_of_lt (lt_of_lt_of_le y.isLt hpow)]
    at this

/-! ## The oracle's answers as bytes -/

/-- A hash value's 32 bytes. -/
abbrev ofOutput {w : Nat} (x : BitVec w) : Vector UInt8 32 := ofBV 32 x

/-- `H` as a query to the oracle.

The input's bytes go in, and the answer's 32 bytes come out. -/
def queryH {m : Type → Type} [Monad m] [HasQuery HashSpec m] (input : ByteArray) :
    m (Vector UInt8 32) :=
  ofOutput <$> oracleHash (m := m) input.data.toList

/-- Bits `8 i` to `8 i + 7` of the low part of a bit vector are the vector's own. -/
theorem extractLsb'_byte_low {w : Nat} (x : BitVec w) (lo m i : Nat) (h : 8 * i + 8 ≤ m) :
    (x.extractLsb' lo m).extractLsb' (8 * i) 8 = x.extractLsb' (lo + 8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  -- Dividing by `2^(8i)` inside `mod 2^m` keeps the low byte.
  rw [mod_div_mod _ (8 * i) m 8 h, Nat.div_div_eq_div_mul, ← pow_add]

/-- Byte `i < 16` of an answer is byte `i` of its low 128 bits. -/
theorem getElem_ofOutput_of_lt (x : HashOutput) (i : Nat) (hi : i < 16) :
    (ofOutput x)[i] = (ofBV 16 (truncateHash x))[i] := by
  simp only [getElem_ofBV, truncateHash, digestBits]
  rw [extractLsb'_byte_low x 0 128 i (by omega), Nat.zero_add]

/-- The low 128 bits of a uniform answer, as 16 bytes, are 16 uniform bytes. -/
theorem prEvent_ofBV_truncateHash (P : Vector UInt8 16 → Prop) :
    Pr{let u ← $ᵗ HashOutput}[P (ofBV 16 (truncateHash u))]
      = (Nat.card {d : Vector UInt8 16 // P d} : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [← prEvent_map ($ᵗ HashOutput) truncateHash (fun b => P (ofBV 16 b)),
    EvalDistEq.prEvent_eq evalDist_truncate_uniformHashOutput,
    SampleableType.prEvent_uniformSample, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  -- The 128-bit values and the 16-byte vectors are in bijection through their bytes.
  have hc : Nat.card {b : BitVec digestBits // P (ofBV 16 b)} =
      Nat.card {d : Vector UInt8 16 // P d} :=
    Nat.card_congr
      { toFun := fun b => ⟨ofBV 16 b.1, b.2⟩
        invFun := fun d => ⟨BitVec.ofNat _ (bytesToUint d.1), by
          rw [ofBV_ofNat_bytesToUint d.1 (w := digestBits) (by simp [digestBits])]
          exact d.2⟩
        left_inv := fun b => Subtype.ext
          (ofBV_inj (n := 16) (by simp [digestBits])
            (ofBV_ofNat_bytesToUint _ (by simp [digestBits])))
        right_inv := fun d => Subtype.ext (ofBV_ofNat_bytesToUint _ (by simp [digestBits])) }
  rw [hc]
  congr 1
  norm_num [digestBits]

/-- The fraction `(2^n - C) / 2^n` is `1 - C / 2^n`, as an extended real. -/
theorem ofReal_one_sub_div (C n : ℕ) (hC : C ≤ 2 ^ n) :
    (((2 ^ n - C : ℕ) : ℝ≥0∞) / 2 ^ n) = ENNReal.ofReal (1 - (C : ℝ) / 2 ^ n) := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h : (1 : ℝ) - C / 2 ^ n = ((2 ^ n - C : ℕ) : ℝ) / 2 ^ n := by
    rw [Nat.cast_sub hC]
    field_simp
    push_cast
    ring
  rw [h, ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num)]
  norm_num

end EthLib.Cryptography.HashSig
