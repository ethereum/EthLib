module

public import EthLib.Cryptography.Bls.HashToCurve
public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Base.Proofs.BigEndian
public import EthLib.Cryptography.Proofs.Bls.FpZMod
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Floor

/-!
# Proofs: the message expansion and the hash to the field of the hash to G2

Sources:

- [RFC 9380 §5.2](https://www.rfc-editor.org/rfc/rfc9380#section-5.2), `hash_to_field`.
- [RFC 9380 §5.3.1](https://www.rfc-editor.org/rfc/rfc9380#section-5.3.1), `expand_message_xmd`.
- [RFC 9380 §5.3.3](https://www.rfc-editor.org/rfc/rfc9380#section-5.3.3), DSTs over 255 bytes.
- [RFC 8017 §4](https://www.rfc-editor.org/rfc/rfc8017#section-4), I2OSP and OS2IP.
- [FIPS 180-4 §6.2](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf), SHA-256.

The file restates `expand_message_xmd` and `hash_to_field` as a model over lists of bytes.

The model hashes with the FIPS 180-4 model of SHA-256.

It reads and writes integers with OS2IP and I2OSP of RFC 8017 §4.

The code agrees with the model on every message shorter than 2^61 - 323 bytes.

The DST must be shorter than 2^61 - 17 bytes.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

/-! ## The model -/

namespace Spec

/-- SHA-256 of FIPS 180-4 §6.2 on a list of bytes. -/
def sha256 (bytes : List UInt8) : List UInt8 :=
  (Hash.Sha256.Spec.hash ⟨bytes.toArray⟩).data.toList

/-- I2OSP of RFC 8017 §4.1: `x` as `len` bytes, the most significant first.

RFC 9380 calls it only for `x < 256 ^ len`. -/
def i2osp (x len : Nat) : List UInt8 := Base.natToBytes len x

/-- OS2IP of RFC 8017 §4.2: the bytes as digits in base 256, the first one the most significant. -/
def os2ip (bytes : List UInt8) : Nat := Nat.ofDigits 256 (bytes.reverse.map UInt8.toNat)

/-- The bitwise XOR of two byte strings of one length, RFC 9380 §4. -/
def strxor (a b : List UInt8) : List UInt8 := List.zipWith (· ^^^ ·) a b

/-- The 17 ASCII bytes of the string `H2C-OVERSIZE-DST-`, RFC 9380 §5.3.3. -/
def oversizePrefix : List UInt8 := "H2C-OVERSIZE-DST-".toList.map fun c => c.toNat.toUInt8

/-- The tag that a DST longer than 255 bytes is replaced with, RFC 9380 §5.3.3. -/
def shortDst (dst : List UInt8) : List UInt8 :=
  if 255 < dst.length then sha256 (oversizePrefix ++ dst) else dst

/-- The block `b_i` of RFC 9380 §5.3.1, steps 8 and 10, given `b_0` and `DST_prime`. -/
def block (b0 dstPrime : List UInt8) : Nat → List UInt8
  | 0 => b0
  | 1 => sha256 (b0 ++ i2osp 1 1 ++ dstPrime)
  | i + 2 => sha256 (strxor b0 (block b0 dstPrime (i + 1)) ++ i2osp (i + 2) 1 ++ dstPrime)

/-- `expand_message_xmd` of RFC 9380 §5.3.1 with SHA-256.

SHA-256 has `b_in_bytes = 32` and `s_in_bytes = 64`.

A DST longer than 255 bytes is first shortened as §5.3.3 requires.

The result is none where step 2 aborts. -/
def expandMessageXmd (msg dst : List UInt8) (lenInBytes : Nat) : Option (List UInt8) :=
  let ell := ⌈(lenInBytes : ℚ) / 32⌉₊
  if 255 < ell ∨ 65535 < lenInBytes then none else
    let dst := shortDst dst
    let dstPrime := dst ++ i2osp dst.length 1
    let msgPrime := i2osp 0 64 ++ msg ++ i2osp lenInBytes 2 ++ i2osp 0 1 ++ dstPrime
    let b0 := sha256 msgPrime
    some (((List.range ell).flatMap fun i => block b0 dstPrime (i + 1)).take lenInBytes)

/-- The security level `k = 128` of the suite `BLS12381G2_XMD:SHA-256_SSWU_RO_`, RFC 9380 §8.8.2. -/
def securityLevel : Nat := 128

/-- The bytes per element `L = ceil((ceil(log2(p)) + k) / 8)` of RFC 9380 §5. -/
def fieldBytes : Nat := ⌈((Nat.clog 2 Fp.modulus + securityLevel : Nat) : ℚ) / 8⌉₊

/-- `hash_to_field` of RFC 9380 §5.2 into `GF(p^2)`, where `m = 2`, with `expand_message_xmd`.

Each element is the pair `(e_0, e_1)` of its coordinates over `GF(p)`. -/
def hashToField (msg dst : List UInt8) (count : Nat) :
    Option (List (ZMod Fp.modulus × ZMod Fp.modulus)) :=
  (expandMessageXmd msg dst (count * 2 * fieldBytes)).map fun uniform =>
    (List.range count).map fun i =>
      let e (j : Nat) : ZMod Fp.modulus :=
        os2ip ((uniform.drop (fieldBytes * (j + i * 2))).take fieldBytes)
      (e 0, e 1)

end Spec

/-! ## The pieces -/

/-- The SHA-256 of the code is the model's on a message shorter than 2⁶¹ bytes. -/
private theorem hash_toList {x : ByteArray} (admitted : x.size < 2 ^ 61) :
    (Hash.Sha256.hash x).data.toList = Spec.sha256 x.data.toList := by
  rw [Hash.Sha256.hash_eq_spec x admitted, Spec.sha256, Array.toArray_toList]

/-- The low byte of a number, as the code takes it. -/
private theorem ofNat_and_255 (n : Nat) : UInt8.ofNat (n &&& 255) = UInt8.ofNat n := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, UInt8.ofNat_mod_size]

private theorem i2osp_one (n : Nat) : (i2osp n 1).data.toList = Spec.i2osp n 1 := by
  simp only [i2osp, Spec.i2osp, Base.natToBytes, Base.natToBytes.go, Array.toList_ofFn,
    List.ofFn_succ, List.ofFn_zero, ofNat_and_255]
  simp

private theorem i2osp_two (n : Nat) : (i2osp n 2).data.toList = Spec.i2osp n 2 := by
  simp only [i2osp, Spec.i2osp, Base.natToBytes, Base.natToBytes.go, Array.toList_ofFn,
    List.ofFn_succ, List.ofFn_zero, ofNat_and_255]
  simp [Nat.shiftRight_eq_div_pow]

@[simp] private theorem i2osp_size (n len : Nat) : (i2osp n len).size = len := by
  simp [i2osp, ByteArray.size]

private theorem strxor_toList (a b : ByteArray) :
    (strxor a b).data.toList = Spec.strxor a.data.toList b.data.toList :=
  Array.toList_zipWith

@[simp] private theorem strxor_size (a b : ByteArray) :
    (strxor a b).size = min a.size b.size := by
  simp only [strxor, ByteArray.size, Array.size_zipWith]

private theorem oversizeDstPrefix_toList :
    oversizeDstPrefix.data.toList = Spec.oversizePrefix := by
  rw [oversizeDstPrefix, String.toUTF8_eq_toByteArray]
  decide +kernel

/-- The ceiling of a quotient of naturals, as a division that rounds up. -/
private theorem ceil_div_eq (n d : Nat) (hd : 0 < d) : ⌈(n : ℚ) / d⌉₊ = (n + d - 1) / d := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hd']
    have hmod := Nat.mod_lt (n + d - 1) hd
    have hdiv := Nat.div_add_mod (n + d - 1) d
    have : n ≤ (n + d - 1) / d * d := by
      rw [Nat.mul_comm]
      omega
    exact_mod_cast this
  · have h := Nat.le_ceil ((n : ℚ) / d)
    rw [div_le_iff₀ hd'] at h
    have h' : n ≤ ⌈(n : ℚ) / d⌉₊ * d := by exact_mod_cast h
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd, Nat.succ_mul]
    omega

/-- The bytes of a fold of appends are the bytes of the accumulator, then those of each array. -/
private theorem foldl_append_toList (bs : List ByteArray) (acc : ByteArray) :
    (bs.foldl (· ++ ·) acc).data.toList = acc.data.toList ++ bs.flatMap (·.data.toList) := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih => simp [ih, ByteArray.data_append, List.append_assoc]

/-- One step of the loop of the code, from the block `b_(i - 1)` to the block `b_i`. -/
private def nextBlock (b0 dstPrime : ByteArray) (i : Nat) (s : Array ByteArray × ByteArray) :
    Array ByteArray × ByteArray :=
  (s.1.push (Hash.Sha256.hash (strxor b0 s.2 ++ i2osp i 1 ++ dstPrime)),
    Hash.Sha256.hash (strxor b0 s.2 ++ i2osp i 1 ++ dstPrime))

/-- The loop of the code computes the blocks `b_1` to `b_(n + 1)` of the model. -/
private theorem foldl_nextBlock (b0 dstPrime : ByteArray) (hb0 : b0.size = 32)
    (hdp : dstPrime.size < 2 ^ 60) (n : Nat) :
    (((List.range' 2 n).foldl (fun s i => nextBlock b0 dstPrime i s)
        (#[Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime)],
          Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime))).1.toList.map (·.data.toList)
        = (List.range (n + 1)).map fun i => Spec.block b0.data.toList dstPrime.data.toList (i + 1))
      ∧ ((List.range' 2 n).foldl (fun s i => nextBlock b0 dstPrime i s)
          (#[Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime)],
            Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime))).2.data.toList
        = Spec.block b0.data.toList dstPrime.data.toList (n + 1)
      ∧ ((List.range' 2 n).foldl (fun s i => nextBlock b0 dstPrime i s)
          (#[Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime)],
            Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime))).2.size = 32 := by
  induction n with
  | zero =>
    have h1 : (Hash.Sha256.hash (b0 ++ i2osp 1 1 ++ dstPrime)).data.toList
        = Spec.block b0.data.toList dstPrime.data.toList 1 := by
      rw [hash_toList (by simp only [ByteArray.size_append, i2osp_size]; omega), Spec.block,
        ByteArray.data_append, ByteArray.data_append, Array.toList_append, Array.toList_append,
        i2osp_one]
    simp [h1]
  | succ n ih =>
    obtain ⟨hl, hp, hs⟩ := ih
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 2 n).foldl _ _ = r at hl hp hs
    have hb : (Hash.Sha256.hash (strxor b0 r.2 ++ i2osp (2 + 1 * n) 1 ++ dstPrime)).data.toList
        = Spec.block b0.data.toList dstPrime.data.toList (n + 1 + 1) := by
      rw [hash_toList (by simp only [ByteArray.size_append, i2osp_size, strxor_size]; omega),
        Spec.block, ByteArray.data_append, ByteArray.data_append, Array.toList_append,
        Array.toList_append, i2osp_one, strxor_toList, hp, show 2 + 1 * n = n + 2 by omega]
    refine ⟨?_, hb, Hash.Sha256.hash_size _⟩
    rw [nextBlock, Array.toList_push, List.map_append, hl, List.range_succ (n := n + 1),
      List.map_append]
    simp only [List.map_cons, List.map_nil, hb]

/-! ## `expand_message_xmd` -/

/-- The tag that the code uses is the model's, and it has at most 255 bytes. -/
private theorem shortDst_toList (dst : ByteArray) (hdst : dst.size + 17 < 2 ^ 61) :
    (if dst.size > 255 then Hash.Sha256.hash (oversizeDstPrefix ++ dst) else dst).data.toList
        = Spec.shortDst dst.data.toList
      ∧ (if dst.size > 255 then Hash.Sha256.hash (oversizeDstPrefix ++ dst) else dst).size
        ≤ 255 := by
  by_cases h : dst.size > 255
  · have hp : oversizeDstPrefix.size = 17 := by
      rw [ByteArray.size, ← Array.length_toList, oversizeDstPrefix_toList]
      rfl
    have h' : 255 < dst.data.toList.length := by simpa using h
    simp only [h, h', Spec.shortDst, ↓reduceIte]
    rw [hash_toList (by rw [ByteArray.size_append, hp]; omega), ByteArray.data_append,
      Array.toList_append, oversizeDstPrefix_toList, Hash.Sha256.hash_size]
    exact ⟨rfl, by decide⟩
  · have h' : ¬ 255 < dst.data.toList.length := by simpa using h
    simp only [h, h', Spec.shortDst, ↓reduceIte]
    exact ⟨trivial, by omega⟩

/--
The message expansion is `expand_message_xmd` of RFC 9380 §5.3.1 with SHA-256.

It holds for every message shorter than 2^61 - 323 bytes and every DST shorter than 2^61 - 17 bytes.

A DST longer than 255 bytes is shortened as §5.3.3 requires.

The expansion fails exactly where step 2 aborts.
-/
theorem expandMessageXmd_eq_spec (msg dst : ByteArray) (lenInBytes : Nat)
    (hmsg : msg.size + 323 < 2 ^ 61) (hdst : dst.size + 17 < 2 ^ 61) :
    (expandMessageXmd msg dst lenInBytes).toOption.map (·.data.toList)
      = Spec.expandMessageXmd msg.data.toList dst.data.toList lenInBytes := by
  have hceil : ⌈(lenInBytes : ℚ) / 32⌉₊ = (lenInBytes + 32 - 1) / 32 := by
    exact_mod_cast ceil_div_eq lenInBytes 32 (by decide)
  rw [Spec.expandMessageXmd, hceil]
  unfold expandMessageXmd
  by_cases hlen : 65535 < lenInBytes
  · simp only [gt_iff_lt, hlen, ↓reduceIte, or_true]
    rfl
  by_cases hell : 255 < (lenInBytes + 32 - 1) / 32
  · simp only [gt_iff_lt, hlen, hell, ↓reduceIte, true_or, sha256OutputSize]
    rfl
  simp only [gt_iff_lt, hlen, hell, ↓reduceIte, or_self, sha256OutputSize]
  obtain ⟨hD, hDsize⟩ := shortDst_toList dst hdst
  generalize (if 255 < dst.size then Hash.Sha256.hash (oversizeDstPrefix ++ dst) else dst) = D
    at hD hDsize ⊢
  have hlenD : D.data.toList.length = D.size := Array.length_toList
  rw [← hD, hlenD]
  have hpad : Spec.i2osp 0 64 = (⟨Array.replicate sha256BlockSize 0⟩ : ByteArray).data.toList := by
    rw [Spec.i2osp, Base.natToBytes_zero_right, Array.toList_replicate]
    rfl
  set dp := D ++ i2osp D.size 1 with hdp_def
  set mp := (⟨Array.replicate sha256BlockSize 0⟩ : ByteArray) ++ msg ++ i2osp lenInBytes 2
    ++ i2osp 0 1 ++ dp with hmp_def
  have hdp : dp.data.toList = D.data.toList ++ Spec.i2osp D.size 1 := by
    rw [hdp_def, ByteArray.data_append, Array.toList_append, i2osp_one]
  have hdps : dp.size ≤ 256 := by
    rw [hdp_def, ByteArray.size_append, i2osp_size]
    omega
  have hmpl : mp.data.toList = Spec.i2osp 0 64 ++ msg.data.toList ++ Spec.i2osp lenInBytes 2
      ++ Spec.i2osp 0 1 ++ dp.data.toList := by
    rw [hpad, ← i2osp_two, ← i2osp_one 0, hmp_def]
    simp only [ByteArray.data_append, Array.toList_append]
  have hmps : mp.size < 2 ^ 61 := by
    have hz : (⟨Array.replicate sha256BlockSize 0⟩ : ByteArray).size = 64 := Array.size_replicate
    rw [hmp_def, ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_append, hz, i2osp_size, i2osp_size]
    omega
  rw [← hdp, ← hmpl, ← hash_toList hmps]
  have hb0 : (Hash.Sha256.hash mp).size = 32 := Hash.Sha256.hash_size _
  generalize Hash.Sha256.hash mp = b0 at hb0 ⊢
  have hdps' : dp.size < 2 ^ 60 := by omega
  clear_value dp mp
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.size, Array.mkEmpty_eq]
  have hout : ∀ x : ByteArray, Option.map (fun x => x.data.toList)
      (pure x : Except BlsError ByteArray).toOption = some x.data.toList := fun _ => rfl
  rw [hout, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero, ← Array.foldl_toList, foldl_append_toList]
  have hzero : (lenInBytes + 32 - 1) / 32 = 0 → lenInBytes = 0 := by omega
  generalize (lenInBytes + 32 - 1) / 32 = ell at hzero ⊢
  cases ell with
  | zero => simp [hzero rfl]
  | succ n =>
    rw [show (n + 1 + 1 - 2 + 1 - 1) / 1 = n by omega]
    obtain ⟨hl, -, -⟩ := foldl_nextBlock b0 dp hb0 hdps' n
    simp only [nextBlock] at hl
    simpa [List.flatMap_def] using congrArg (fun l => some (List.take lenInBytes l.flatten)) hl

/-! ## `hash_to_field` -/

/-- The big-endian reading of the code is OS2IP. -/
private theorem bytesToNat_eq_os2ip (bytes : List UInt8) :
    Base.bytesToNat bytes = Spec.os2ip bytes := by
  induction bytes using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [Base.bytesToNat_append, ih]
    simp [Spec.os2ip, Base.bytesToNat, Nat.ofDigits, Nat.mul_comm]
    omega

/-- The bytes per element are 64, since `p` has 381 bits. -/
theorem fieldBytes_eq : Spec.fieldBytes = 64 := by
  have hlog : Nat.clog 2 Fp.modulus = 381 := by
    apply le_antisymm (Nat.clog_le_of_le_pow (by decide +kernel))
    exact (Nat.lt_clog_iff_pow_lt (by decide)).2 (by decide +kernel)
  have h := ceil_div_eq (381 + 128) 8 (by decide)
  rw [Spec.fieldBytes, hlog, Spec.securityLevel]
  exact_mod_cast h

/-- An element read by the code is OS2IP of its bytes, reduced modulo `p`. -/
private theorem toZMod_fpFromBytesL (uniform : ByteArray) (off : Nat) :
    Fp.toZMod (fpFromBytesL (uniform.extract off (off + 64)) : Fp)
      = (Spec.os2ip ((uniform.data.toList.drop off).take 64) : ZMod Fp.modulus) := by
  rw [fpFromBytesL, ← bytesToNat_eq_os2ip, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  exact Fp.toZMod_ofNat _

/--
The hash to `Fp2` is `hash_to_field` of RFC 9380 §5.2 with `expand_message_xmd`.

It holds for every message shorter than 2^61 - 323 bytes and every DST shorter than 2^61 - 17 bytes.

Each element is mapped to the pair of its coordinates in `ZMod p`.
-/
theorem hashToFieldFp2_eq_spec (msg dst : ByteArray) (count : Nat)
    (hmsg : msg.size + 323 < 2 ^ 61) (hdst : dst.size + 17 < 2 ^ 61) :
    (hashToFieldFp2 msg dst count : Except BlsError (Vector Fp2 count)).toOption.map
        (fun us => us.toList.map fun u => (Fp.toZMod u.c0, Fp.toZMod u.c1))
      = Spec.hashToField msg.data.toList dst.data.toList count := by
  rw [Spec.hashToField, fieldBytes_eq, ← expandMessageXmd_eq_spec msg dst _ hmsg hdst]
  unfold hashToFieldFp2
  dsimp only
  cases expandMessageXmd msg dst (count * 2 * 64) with
  | error e => rfl
  | ok uniform =>
    simp only [bind, Except.bind, pure, Except.pure, Except.toOption, Option.map_some,
      Vector.toList_ofFn, List.map_ofFn]
    congr 1
    apply List.ext_getElem (by simp)
    intro i _ _
    simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_map, List.getElem_range,
      toZMod_fpFromBytesL, Nat.zero_add, Nat.add_comm 1]

end EthLib.Cryptography.Bls.HashToCurve
