module

public import EthLib.Cryptography.Proofs.Hash.KeccakBitsPermutation

/-!
# Proofs: the Keccak sponge on bytes and on bits

The Keccak implementation pads, absorbs and squeezes byte strings.

The bit model pads, absorbs and squeezes lists of bits.

FIPS 202 Appendix B.1 orders the bits of each byte from least significant to most significant.

This file proves that the two sponges agree in that order for one squeezed block.

The proof covers every positive byte rate up to 136 that is a multiple of 8.

Keccak-256 and Keccak-512 therefore equal their bit models on every message.
-/

@[expose] public section

namespace EthLib.Cryptography.Models.KeccakBits

open EthLib.Cryptography.Hash

/-! ## Bytes as bits -/

/-- Every byte gives eight bits. -/
theorem byteBits_length (byte : UInt8) : (byteBits byte).length = 8 := by
  simp [byteBits]

/-- A list of bytes gives eight bits for each byte. -/
theorem byteListBits_length (bs : List UInt8) :
    (bs.flatMap byteBits).length = 8 * bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp [byteBits_length, ih]
    omega

/-- A byte string gives eight bits for each byte. -/
theorem messageBits_length (msg : ByteArray) : (messageBits msg).length = 8 * msg.size := by
  simpa only [messageBits, Array.length_toList, ByteArray.size] using
    byteListBits_length msg.data.toList

/-- Bit `i` of a list of bytes is bit `i % 8` of byte `i / 8`. -/
theorem byteListBits_get (bs : List UInt8) (i : Nat) (h : i < 8 * bs.length) :
    (bs.flatMap byteBits)[i]'(by rw [byteListBits_length]; exact h) =
      (bs[i / 8]'(by omega)).toNat.testBit (i % 8) := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    have hlen : (byteBits b).length = 8 := byteBits_length b
    simp only [List.flatMap_cons]
    by_cases hi : i < 8
    -- The first eight bits come from the first byte.
    · rw [List.getElem_append_left (by simpa [hlen] using hi)]
      have div : i / 8 = 0 := Nat.div_eq_of_lt hi
      have rem : i % 8 = i := Nat.mod_eq_of_lt hi
      simp [byteBits, div, rem]
    -- The later bits come from the remaining bytes, eight positions earlier.
    · rw [List.getElem_append_right (by omega : (byteBits b).length ≤ i)]
      have k : i - 8 < 8 * bs.length := by
        simp only [List.length_cons] at h
        omega
      have j : (i - 8) / 8 + 1 = i / 8 := by omega
      have r : (i - 8) % 8 = i % 8 := by omega
      simp only [hlen]
      rw [ih (i - 8) k]
      simp only [← j, List.getElem_cons_succ, r]

/-- Bit `i` of a byte string is bit `i % 8` of byte `i / 8`. -/
theorem messageBits_get (msg : ByteArray) (i : Nat) (h : i < 8 * msg.size) :
    (messageBits msg)[i]'(by rw [messageBits_length]; exact h) =
      (msg.data[i / 8]'(by simp only [ByteArray.size] at h; omega)).toNat.testBit (i % 8) := by
  have ht : i < 8 * msg.data.toList.length := by
    simpa only [Array.length_toList, ByteArray.size] using h
  have result := byteListBits_get msg.data.toList i ht
  simp only [Array.getElem_toList] at result
  exact result

/-- The bits of two joined byte strings are the bits of the first, then of the second. -/
theorem messageBits_append (a b : ByteArray) :
    messageBits (a ++ b) = messageBits a ++ messageBits b := by
  simp only [messageBits, ByteArray.data_append, Array.toList_append, List.flatMap_append]

/-! ## Padding -/

/-- pad10*1 of the model at `rateBits` bits has its length from FIPS 202 Algorithm 9. -/
theorem paddingAt_length (rateBits length : Nat) :
    (paddingAt rateBits length).length =
      ((rateBits - ((length + 2) % rateBits)) % rateBits) + 2 := by
  simp only [paddingAt, List.length_cons, List.length_append, List.length_replicate,
    List.length_nil]

/-- pad10*1 of the model has its length from FIPS 202 Algorithm 9. -/
theorem padding_length (length : Nat) :
    (padding length).length = ((1088 - ((length + 2) % 1088)) % 1088) + 2 :=
  paddingAt_length 1088 length

/-- A padding bit at `rateBits` bits is one exactly at the first and at the last position. -/
theorem paddingAt_get (rateBits length i : Nat) (h : i < (paddingAt rateBits length).length) :
    (paddingAt rateBits length)[i] =
      (decide (i = 0) || decide (i + 1 = (paddingAt rateBits length).length)) := by
  cases i with
  | zero => simp [paddingAt]
  | succ j =>
    let n := (rateBits - ((length + 2) % rateBits)) % rateBits
    have bound : j < n + 1 := by
      simp only [paddingAt_length] at h
      dsimp [n]
      omega
    simp only [paddingAt_length]
    unfold paddingAt
    change (List.replicate n false ++ [true])[j]'(by simp; omega) =
      (decide (j + 1 = 0) || decide (j + 1 + 1 = n + 2))
    by_cases hj : j < n
    · simp [hj]
      omega
    · have eq : j = n := by omega
      subst j
      simp

/-- A padding bit is one exactly at the first and at the last position. -/
theorem padding_get (length i : Nat) (h : i < (padding length).length) :
    (padding length)[i] = (decide (i = 0) || decide (i + 1 = (padding length).length)) :=
  paddingAt_get 1088 length i h

/-- Bit `i` of the padding mask is bit 0 of the first flag, or bit 7 of the last flag. -/
private theorem maskBits : ∀ (first last : Bool) (i : Fin 8),
    (((if first then 1 else 0 : UInt8) ||| (if last then 128 else 0)).toNat.testBit i.val) =
      ((first && (decide (i.val = 0))) || (last && (decide (i.val = 7)))) := by
  decide +kernel

/-- Byte `pos` of the padding sets bit 0 when it is the first byte, and bit 7 when it is the last.

It sets no other bit. -/
theorem _root_.EthLib.Cryptography.Hash.Keccak.paddingByte_testBit (rate len pos bit : Nat)
    (h : bit < 8) :
    (Keccak.paddingByte rate len pos).toNat.testBit bit =
      (decide (pos = 0 ∧ bit = 0) || decide (pos + 1 = rate - len % rate ∧ bit = 7)) := by
  have hb := maskBits (decide (pos = 0)) (decide (pos + 1 = rate - len % rate)) ⟨bit, h⟩
  simpa [Keccak.paddingByte, Bool.and_eq_true] using hb

/-- The byte padding at `rate` bytes spells the bits of pad10*1 at `8 * rate` bits. -/
theorem paddingAtBits_eq {rate : Nat} (hr : 0 < rate) (len : Nat) :
    messageBits (Keccak.padding rate len) = paddingAt (8 * rate) (8 * len) := by
  have hl : (messageBits (Keccak.padding rate len)).length =
      (paddingAt (8 * rate) (8 * len)).length := by
    rw [messageBits_length, Keccak.size_padding, paddingAt_length]
    have hrem : len % rate < rate := Nat.mod_lt len hr
    have hmod : (8 * len + 2) % (8 * rate) = 8 * (len % rate) + 2 := by
      have hd := Nat.div_add_mod len rate
      have hmul : 8 * (rate * (len / rate)) = (8 * rate) * (len / rate) :=
        (Nat.mul_assoc 8 rate (len / rate)).symm
      have heq : 8 * len + 2 = (8 * (len % rate) + 2) + (8 * rate) * (len / rate) := by omega
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have hsub : (8 * rate - (8 * (len % rate) + 2)) % (8 * rate) =
        8 * rate - (8 * (len % rate) + 2) :=
      Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    omega
  apply List.ext_getElem hl
  intro i hi hj
  have hb : i < 8 * (Keccak.padding rate len).size := by simpa [messageBits_length] using hi
  rw [messageBits_get _ i hb, paddingAt_get _ _ i hj]
  have bitBound : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have iByte : i / 8 < rate - len % rate := by
    rw [Keccak.size_padding] at hb
    omega
  have byteEq : (Keccak.padding rate len).data[i / 8]'(by
      simp only [Keccak.padding_data, Array.size_ofFn]
      exact iByte) = Keccak.paddingByte rate len (i / 8) := by
    simp [Keccak.padding_data]
  rw [byteEq, Keccak.paddingByte_testBit _ _ _ _ bitBound]
  have plen : (paddingAt (8 * rate) (8 * len)).length = 8 * (rate - len % rate) := by
    rw [← hl, messageBits_length, Keccak.size_padding]
  -- The first padding bit is bit 0 of byte 0, and the last is bit 7 of the last byte.
  have first : (i / 8 = 0 ∧ i % 8 = 0) ↔ i = 0 := by omega
  have last : (i / 8 + 1 = rate - len % rate ∧ i % 8 = 7) ↔
      i + 1 = (paddingAt (8 * rate) (8 * len)).length := by omega
  simp only [first, last]

/-- The byte padding at the rate of 136 bytes spells the bits of pad10*1 at 1088 bits. -/
theorem paddingBits_eq (len : Nat) :
    messageBits (Keccak.padding 136 len) = padding (8 * len) := by
  simpa only [padding] using paddingAtBits_eq (rate := 136) (by decide) len

/-- The bits of a byte string padded at `rate` bytes are the padded bits of the model. -/
theorem paddedAtBits_eq {rate : Nat} (hr : 0 < rate) (msg : ByteArray) :
    messageBits (Keccak.pad rate msg) = paddedAt (8 * rate) msg := by
  simp only [Keccak.pad, messageBits_append, paddedAt, messageBits_length, paddingAtBits_eq hr]

/-- The bits of the padded byte string are the padded bits of the model. -/
theorem paddedBits_eq (msg : ByteArray) : messageBits (Keccak.pad 136 msg) = padded msg := by
  simpa only [padded] using paddedAtBits_eq (rate := 136) (by decide) msg

/-- The model and the lane implementation cut a message into the same number of blocks. -/
theorem paddedAt_blockCount_eq {rate : Nat} (hr : 0 < rate) (msg : ByteArray) :
    (paddedAt (8 * rate) msg).length / (8 * rate) = Keccak.blockCount rate msg.size := by
  rw [← paddedAtBits_eq hr, messageBits_length, Keccak.size_pad hr, ← Nat.mul_assoc]
  exact Nat.mul_div_right (Keccak.blockCount rate msg.size) (by omega)

/-- The model and the lane implementation cut a Keccak-256 message into the same block count. -/
theorem padded_blockCount_eq (msg : ByteArray) :
    (padded msg).length / 1088 = Keccak.blockCount 136 msg.size := by
  simpa only [padded] using paddedAt_blockCount_eq (rate := 136) (by decide) msg

/-! ## Absorbing -/

/-- A byte widened to a lane keeps its eight bits, and is zero above them. -/
private theorem byteExtend (b : UInt8) (i : Nat) (hi : i < 64) :
    b.toUInt64.toBitVec.getLsbD i = (decide (i < 8) && b.toNat.testBit i) := by
  rw [UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h : i < 8
  · simp only [h, decide_true, Bool.true_and]
    rw [← BitVec.testBit_toNat, UInt8.toNat_toBitVec]
  · simp only [h, decide_false, Bool.false_and]
    exact BitVec.getLsbD_of_ge b.toBitVec i (by omega)

/-- A byte shifted to byte `m` of a lane holds, at bit `i`, bit `i % 8` of the byte in byte `m`. -/
private theorem shiftedByte (b : UInt8) (m i : Nat) (hm : m < 8) (hi : i < 64) :
    (b.toUInt64 <<< UInt64.ofNat (8 * m)).toBitVec.getLsbD i =
      (decide (i / 8 = m) && b.toNat.testBit (i % 8)) := by
  have amount : (UInt64.ofNat (8 * m)).toBitVec.toNat % 64 = 8 * m := by
    simp
    omega
  simp only [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toNat_umod,
    show (64 : BitVec 64).toNat = 64 by decide, amount, BitVec.getLsbD_shiftLeft, hi,
    decide_true, Bool.true_and]
  by_cases h : i / 8 = m
  · rw [byteExtend _ _ (by omega)]
    simp only [h, decide_true, Bool.true_and, show ¬ i < 8 * m by omega, decide_false,
      Bool.not_false, show i - 8 * m = i % 8 by omega, show i % 8 < 8 by omega]
  · by_cases low : i < 8 * m
    · simp [h, low]
    · rw [byteExtend _ _ (by omega)]
      simp [h, low, show ¬ i - 8 * m < 8 by omega]

/-- A lane read from a byte string is its eight bytes from the start, each shifted to its place. -/
private theorem laneAt_eq (bytes : ByteArray) (s : Nat) :
    Keccak.Internal.laneAt bytes s =
      (EthLib.Base.byteAt bytes s).toUInt64 |||
      (EthLib.Base.byteAt bytes (s + 1)).toUInt64 <<< UInt64.ofNat (8 * 1) |||
      (EthLib.Base.byteAt bytes (s + 2)).toUInt64 <<< UInt64.ofNat (8 * 2) |||
      (EthLib.Base.byteAt bytes (s + 3)).toUInt64 <<< UInt64.ofNat (8 * 3) |||
      (EthLib.Base.byteAt bytes (s + 4)).toUInt64 <<< UInt64.ofNat (8 * 4) |||
      (EthLib.Base.byteAt bytes (s + 5)).toUInt64 <<< UInt64.ofNat (8 * 5) |||
      (EthLib.Base.byteAt bytes (s + 6)).toUInt64 <<< UInt64.ofNat (8 * 6) |||
      (EthLib.Base.byteAt bytes (s + 7)).toUInt64 <<< UInt64.ofNat (8 * 7) :=
  rfl

/-- Bit `i` of the lane at byte `s` is bit `i % 8` of byte `s + i / 8`, as in FIPS 202 §3.1.2. -/
theorem _root_.EthLib.Cryptography.Hash.Keccak.Internal.laneAt_testBit (bytes : ByteArray)
    (s i : Nat) (hi : i < 64) :
    (Keccak.Internal.laneAt bytes s).toBitVec.getLsbD i =
      (EthLib.Base.byteAt bytes (s + i / 8)).toNat.testBit (i % 8) := by
  rw [laneAt_eq]
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, byteExtend _ _ hi,
    shiftedByte _ 1 _ (by decide) hi, shiftedByte _ 2 _ (by decide) hi,
    shiftedByte _ 3 _ (by decide) hi, shiftedByte _ 4 _ (by decide) hi,
    shiftedByte _ 5 _ (by decide) hi, shiftedByte _ 6 _ (by decide) hi,
    shiftedByte _ 7 _ (by decide) hi]
  -- Exactly one of the eight bytes holds bit `i`: byte `i / 8`.
  have hq : i / 8 < 8 := by omega
  have low : (i < 8) ↔ (i / 8 = 0) := by omega
  have bit : i % 8 = i ∨ i / 8 ≠ 0 := by omega
  simp only [low]
  generalize hm : i / 8 = q at hq bit ⊢
  interval_cases q <;> simp_all
  -- Byte 0 holds bit `i` itself, since `i < 8`.
  rw [Nat.mod_eq_of_lt low]

/-- The bits of the block of `rate` bytes from byte `start`, as a `8 * rate`-bit block. -/
def blockBitsAt (rate : Nat) (bytes : ByteArray) (start : Nat) : BlockOf (8 * rate) :=
  Vector.ofFn fun i => (EthLib.Base.byteAt bytes (start + i.val / 8)).toNat.testBit (i.val % 8)

/-- The bits of the block of 136 bytes from byte `start`, as a block of the model. -/
def blockBits (bytes : ByteArray) (start : Nat) : Block := blockBitsAt 136 bytes start

/-- Lane `(x, y)` after absorbing at most 136 bytes is XORed with block lane `x + 5 * y`. -/
theorem _root_.EthLib.Cryptography.Hash.Keccak.Internal.absorbBlock_lane_le {rate : Nat}
    (hr : rate ≤ 136) (a : Keccak.State) (bytes : ByteArray) (start : Nat) (x y : Fin 5) :
    (Keccak.Internal.absorbBlock rate a bytes start).lane x y =
      a.lane x y ^^^ Keccak.Internal.blockLane rate bytes start (x.val + 5 * y.val) := by
  have z17 : Keccak.Internal.blockLane rate bytes start 17 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  have z18 : Keccak.Internal.blockLane rate bytes start 18 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  have z19 : Keccak.Internal.blockLane rate bytes start 19 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  have z20 : Keccak.Internal.blockLane rate bytes start 20 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  have z21 : Keccak.Internal.blockLane rate bytes start 21 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  have z22 : Keccak.Internal.blockLane rate bytes start 22 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  have z23 : Keccak.Internal.blockLane rate bytes start 23 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  have z24 : Keccak.Internal.blockLane rate bytes start 24 = 0 := by
    unfold Keccak.Internal.blockLane; exact ite_eq_right (by omega)
  fin_cases x <;> fin_cases y <;>
    simp [Keccak.Internal.absorbBlock, Keccak.State.lane, z17, z18, z19, z20, z21, z22, z23, z24]

/-- Lane `(x, y)` after absorbing a block is the lane XOR block lane `x + 5 * y`. -/
theorem _root_.EthLib.Cryptography.Hash.Keccak.Internal.absorbBlock_lane (a : Keccak.State)
    (bytes : ByteArray) (start : Nat) (x y : Fin 5) :
    (Keccak.Internal.absorbBlock 136 a bytes start).lane x y =
      a.lane x y ^^^ Keccak.Internal.blockLane 136 bytes start (x.val + 5 * y.val) :=
  Keccak.Internal.absorbBlock_lane_le (by decide) a bytes start x y

/-- Absorbing a `rate`-byte block, for `8 ∣ rate` and `rate ≤ 136`, equals absorbing its bits. -/
theorem absorbBlockAt_ofLanes {rate : Nat} (hlanes : 8 ∣ rate) (hr : rate ≤ 136)
    (a : Keccak.State) (bytes : ByteArray) (start : Nat) :
    ofLanes (Keccak.Internal.absorbBlock rate a bytes start) =
      absorbAt (ofLanes a) (blockBitsAt rate bytes start) := by
  obtain ⟨m, rfl⟩ := hlanes
  funext x y z
  have hz := z.isLt
  have hk : x.val + 5 * y.val < 25 := by
    have := x.isLt
    have := y.isLt
    omega
  have address : index x y z = 64 * (x.val + 5 * y.val) + z.val := rfl
  simp only [ofLanes, Keccak.Internal.absorbBlock_lane_le hr, UInt64.toBitVec_xor,
    BitVec.getLsbD_xor, absorbAt, Keccak.Internal.blockLane]
  congr 1
  by_cases hrate : x.val + 5 * y.val < m
  -- A rate lane reads 8 bytes of the block.
  · have inside : index x y z < 8 * (8 * m) := by omega
    simp only [show 8 * (x.val + 5 * y.val) < 8 * m by omega, ↓reduceIte, dite_eq_left inside,
      Keccak.Internal.laneAt_testBit _ _ _ hz, blockBitsAt, Vector.getElem_ofFn]
    have byte : start + 8 * (x.val + 5 * y.val) + z.val / 8 = start + index x y z / 8 := by
      omega
    have bit : z.val % 8 = index x y z % 8 := by omega
    rw [byte, bit]
  -- A capacity lane is XORed with zero.
  · have outside : ¬ index x y z < 8 * (8 * m) := by omega
    simp only [show ¬ 8 * (x.val + 5 * y.val) < 8 * m by omega, ↓reduceIte,
      dite_eq_right outside]
    simp

/-- Absorbing a block of 136 bytes is absorbing its bits in the model. -/
theorem absorbBlock_ofLanes (a : Keccak.State) (bytes : ByteArray) (start : Nat) :
    ofLanes (Keccak.Internal.absorbBlock 136 a bytes start) =
      absorb (ofLanes a) (blockBits bytes start) := by
  simpa only [absorb, blockBits] using
    absorbBlockAt_ofLanes (rate := 136) ⟨17, rfl⟩ (by decide) a bytes start

/-- Absorbing `n` blocks of `rate` bytes from byte `start` is absorbing their bits in order. -/
theorem absorbBlocksAt_ofLanes {rate : Nat} (hlanes : 8 ∣ rate) (hr : rate ≤ 136)
    (bytes : ByteArray) (n start : Nat) (a : Keccak.State) :
    ofLanes (Keccak.Internal.absorbBlocks Keccak.keccakF rate bytes n start a) =
      (List.range n).foldl
        (fun s j => permutation (absorbAt s (blockBitsAt rate bytes (start + rate * j))))
        (ofLanes a) := by
  induction n generalizing start a with
  | zero => rfl
  | succ n ih =>
    rw [Keccak.Internal.absorbBlocks, ih, permutation_ofLanes, absorbBlockAt_ofLanes hlanes hr,
      List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one,
      Nat.add_assoc, Nat.add_comm rate]

/-- Absorbing `n` blocks from byte `start` is absorbing their bits in the model, in order. -/
theorem absorbBlocks_ofLanes (bytes : ByteArray) (n start : Nat) (a : Keccak.State) :
    ofLanes (Keccak.Internal.absorbBlocks Keccak.keccakF 136 bytes n start a) =
      (List.range n).foldl
        (fun s j => permutation (absorb s (blockBits bytes (start + 136 * j)))) (ofLanes a) := by
  simpa only [absorb, blockBits] using
    absorbBlocksAt_ofLanes (rate := 136) ⟨17, rfl⟩ (by decide) bytes n start a

/-- Block `i` of the bits padded at `8 * rate` bits is the bits of block `i` of the padded bytes. -/
theorem paddedBlockAt_eq {rate : Nat} (hr : 0 < rate) (msg : ByteArray)
    (i : Fin ((paddedAt (8 * rate) msg).length / (8 * rate))) :
    paddedBlockAt (Nat.mul_pos (by decide) hr) msg i =
      blockBitsAt rate (Keccak.pad rate msg) (rate * i.val) := by
  apply Vector.ext
  intro j hj
  have count := paddedAt_blockCount_eq hr msg
  have hi := i.isLt
  have size := Keccak.size_pad hr msg
  have hjByte : j / 8 < rate := by omega
  have hmul : rate * (i.val + 1) ≤ rate * Keccak.blockCount rate msg.size :=
    Nat.mul_le_mul_left rate (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have inside : rate * i.val + j / 8 < (Keccak.pad rate msg).size := by omega
  have heq : 8 * rate * i.val + j = j + 8 * (rate * i.val) := by
    rw [Nat.mul_assoc, Nat.add_comm]
  have bitBound : 8 * rate * i.val + j < 8 * (Keccak.pad rate msg).size := by
    have hmul8 : 8 * (rate * i.val + j / 8 + 1) ≤ 8 * (Keccak.pad rate msg).size :=
      Nat.mul_le_mul_left 8 inside
    omega
  have bit := messageBits_get (Keccak.pad rate msg) (8 * rate * i.val + j) bitBound
  simp only [paddedAtBits_eq hr] at bit
  have byteIndex : (8 * rate * i.val + j) / 8 = rate * i.val + j / 8 := by
    rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.add_comm]
  have bitIndex : (8 * rate * i.val + j) % 8 = j % 8 := by
    rw [heq, Nat.add_mul_mod_self_left]
  simp only [byteIndex, bitIndex] at bit
  simp only [paddedBlockAt, blockBitsAt, Vector.getElem_ofFn, EthLib.Base.byteAt,
    dite_eq_left inside, ByteArray.getElem_eq_getElem_data]
  exact bit

/-- Block `i` of the padded bits is the bits of block `i` of the padded bytes. -/
theorem paddedBlock_eq (msg : ByteArray) (i : Fin ((padded msg).length / 1088)) :
    paddedBlock msg i = blockBits (Keccak.pad 136 msg) (136 * i.val) := by
  simpa only [paddedBlock, blockBits] using paddedBlockAt_eq (rate := 136) (by decide) msg i

/-- The lane sponge at `rate` bytes absorbs every message to the state of the bit model. -/
theorem absorbAllAt_eq {rate : Nat} (hr : 0 < rate) (hlanes : 8 ∣ rate) (hle : rate ≤ 136)
    (msg : ByteArray) :
    ofLanes (Keccak.spongeAbsorb Keccak.keccakF rate msg) =
      absorbAllAt (rateBits := 8 * rate) (Nat.mul_pos (by decide) hr) msg := by
  have zero : ofLanes Keccak.State.zero = (fun _ _ _ => false) := by
    funext x y z
    fin_cases x <;> fin_cases y <;> simp [ofLanes, Keccak.State.zero, Keccak.State.lane]
  have values : (List.finRange ((paddedAt (8 * rate) msg).length / (8 * rate))).map Fin.val =
      List.range (Keccak.blockCount rate msg.size) := by
    rw [← paddedAt_blockCount_eq hr]
    apply List.ext_getElem (by simp)
    intro j _ _
    simp
  rw [Keccak.spongeAbsorb, absorbBlocksAt_ofLanes hlanes hle, zero, absorbAllAt, ← values,
    List.foldl_map]
  simp only [Nat.zero_add, paddedBlockAt_eq hr]

/-- The lane sponge absorbs Keccak-256 input to the state of the model, read bit by bit. -/
theorem absorbAll_eq (msg : ByteArray) :
    ofLanes (Keccak.spongeAbsorb Keccak.keccakF 136 msg) = absorbAll msg := by
  simpa only [absorbAll] using absorbAllAt_eq (rate := 136) (by decide) ⟨17, rfl⟩ (by decide) msg

/-! ## Squeezing -/

/-- Byte `m` of a lane, for `m < 8`, holds lane bits `8m` to `8m + 7`. -/
private theorem bytesOfLane_bit (v : UInt64) (m j : Nat) (hm : m < 8) (hj : j < 8) :
    ((Keccak.Internal.bytesOfLane v)[m]'(by
      simp [Keccak.Internal.bytesOfLane]; omega)).toBitVec.getLsbD j =
      v.toBitVec.getLsbD (8 * m + j) := by
  interval_cases m <;>
    simp [Keccak.Internal.bytesOfLane, UInt64.toBitVec_toUInt8,
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat, BitVec.ushiftRight_eq',
      BitVec.getLsbD_ushiftRight, hj]

/-- Squeezed byte `i` is byte `i % 8` of lane `(i / 8, 0)`. -/
theorem squeeze_get (a : Keccak.State) (i : Fin 32) :
    (Keccak.Internal.squeeze a)[i] =
      (Keccak.Internal.bytesOfLane (a.lane ⟨i.val / 8, by omega⟩ 0))[i.val % 8]'(by
        simp [Keccak.Internal.bytesOfLane]
        omega) := by
  fin_cases i <;> rfl

/-- Squeezed byte `i` of `squeeze512` is byte `i % 8` of lane `((i / 8) % 5, i / 40)`. -/
theorem squeeze512_get (a : Keccak.State) (i : Fin 64) :
    (Keccak.Internal.squeeze512 a)[i] =
      (Keccak.Internal.bytesOfLane
        (a.lane ⟨(i.val / 8) % 5, by omega⟩ ⟨i.val / 40, by omega⟩))[i.val % 8]'(by
          simp [Keccak.Internal.bytesOfLane]
          omega) := by
  fin_cases i <;> rfl

/-- Pack eight bits into a byte, the first bit lowest. -/
private def pack8 (a b c d e f g h : Bool) : UInt8 :=
  UInt8.ofNat ((if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
    (if d then 8 else 0) + (if e then 16 else 0) + (if f then 32 else 0) +
    (if g then 64 else 0) + (if h then 128 else 0))

/-- Each bit of a packed byte is the bit packed at its position. -/
private theorem pack8_bit : ∀ (a b c d e f g h : Bool) (i : Fin 8),
    (pack8 a b c d e f g h).toBitVec.getLsbD i.val = (#v[a, b, c, d, e, f, g, h])[i] := by
  decide +kernel

/-- A conditional addition is the addition of a conditional term. -/
private theorem carry (p : Bool) (n w : Nat) :
    (if p then n + w else n) = n + (if p then w else 0) := by
  cases p <;> simp

/-- An output byte of the model packs its eight state bits, the lowest first. -/
private theorem outputPack (s : State) (i : Nat) :
    outputByte s i = pack8 (stateBit s (8 * i + 0)) (stateBit s (8 * i + 1))
      (stateBit s (8 * i + 2)) (stateBit s (8 * i + 3)) (stateBit s (8 * i + 4))
      (stateBit s (8 * i + 5)) (stateBit s (8 * i + 6)) (stateBit s (8 * i + 7)) := by
  simp only [outputByte, pack8, List.range_succ, List.range_zero, List.foldl_append,
    List.foldl_cons, List.foldl_nil, carry, Nat.pow_zero, Nat.pow_succ, Nat.reduceMul,
    Nat.zero_add, Nat.add_zero]

/-- Bit `j` of an output byte of the model is state bit `8 * i + j`. -/
private theorem outputByte_bit (s : State) (i j : Nat) (hj : j < 8) :
    (outputByte s i).toBitVec.getLsbD j = stateBit s (8 * i + j) := by
  rw [outputPack, pack8_bit _ _ _ _ _ _ _ _ ⟨j, hj⟩]
  interval_cases j <;> rfl

/-- Output byte `i` of a lane state (`i < 200`) is byte `i % 8` of lane `((i / 8) % 5, i / 40)`. -/
theorem outputByte_ofLanes (a : Keccak.State) {i : Nat} (hi : i < 200) :
    outputByte (ofLanes a) i =
      (Keccak.Internal.bytesOfLane
        (a.lane ⟨(i / 8) % 5, by omega⟩ ⟨i / 40, by omega⟩))[i % 8]'(by
          simp [Keccak.Internal.bytesOfLane]
          omega) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [outputByte_bit _ _ _ hj, bytesOfLane_bit _ _ _ (by omega) hj]
  -- Output bit `8 * i + j` lies in lane `((i / 8) % 5, i / 40)`, at bit `8 * (i % 8) + j`.
  have hdiv : (8 * i + j) / 64 = i / 8 := by omega
  have hx : xy ((8 * i + j) / 64 % 5) = ⟨(i / 8) % 5, by omega⟩ :=
    Fin.ext (by simp only [xy, hdiv, Nat.mod_mod])
  have hy : xy ((8 * i + j) / 64 / 5) = ⟨i / 40, by omega⟩ :=
    Fin.ext (by simp only [xy, hdiv]; omega)
  have hz : (8 * i + j) % 64 = 8 * (i % 8) + j := by omega
  simp only [stateBit, ofLanes, zcoord, hx, hy, hz]

/-- Each of the first 32 output bytes of the model is the squeezed byte of `squeeze`. -/
theorem outputByte_eq_squeeze (a : Keccak.State) (i : Fin 32) :
    outputByte (ofLanes a) i.val = (Keccak.Internal.squeeze a)[i] := by
  rw [outputByte_ofLanes a (by omega), squeeze_get]
  have hx : (⟨(i.val / 8) % 5, by omega⟩ : Fin 5) = ⟨i.val / 8, by omega⟩ :=
    Fin.ext (by simp; omega)
  have hy : (⟨i.val / 40, by omega⟩ : Fin 5) = 0 :=
    Fin.ext (by simp; omega)
  simp only [hx, hy]

/-- Each of the first 64 output bytes of the model is the squeezed byte of `squeeze512`. -/
theorem outputByte_eq_squeeze512 (a : Keccak.State) (i : Fin 64) :
    outputByte (ofLanes a) i.val = (Keccak.Internal.squeeze512 a)[i] := by
  rw [outputByte_ofLanes a (by omega), squeeze512_get]

/-! ## The hashes -/

/-- A lane squeeze of the first `outBytes` bytes of the absorbed state equals `sponge`.

The output fits one rate block, as FIPS 202 Algorithm 8 requires before a further permutation. -/
theorem sponge_eq_of_squeeze {rate outBytes : Nat} (hr : 0 < rate) (hlanes : 8 ∣ rate)
    (hle : rate ≤ 136) (hout : outBytes ≤ rate) (sq : Keccak.State → Vector UInt8 outBytes)
    (hsq : ∀ (a : Keccak.State) (i : Fin outBytes), (sq a)[i] = outputByte (ofLanes a) i.val)
    (msg : ByteArray) :
    sq (Keccak.spongeAbsorb Keccak.keccakF rate msg) =
      sponge (rateBits := 8 * rate) (Nat.mul_pos (by decide) hr)
        (Nat.mul_le_mul_left 8 hout) msg := by
  apply Vector.ext
  intro i hi
  have out := hsq (Keccak.spongeAbsorb Keccak.keccakF rate msg) ⟨i, hi⟩
  simp only [Fin.getElem_fin, absorbAllAt_eq hr hlanes hle] at out
  simpa only [sponge, squeezeBytes, Vector.getElem_ofFn] using out

/-- Byte `i` of the Keccak-256 digest of the model is output byte `i` of the absorbed state. -/
theorem keccak256_getElem (msg : ByteArray) (i : Nat) (h : i < 32) :
    (keccak256 msg)[i] = outputByte (absorbAll msg) i := by
  simp only [keccak256, sponge, squeezeBytes, absorbAll, Vector.getElem_ofFn]

/-- Byte `i` of the Keccak-512 digest of the model is output byte `i` of the absorbed state. -/
theorem keccak512_getElem (msg : ByteArray) (i : Nat) (h : i < 64) :
    (keccak512 msg)[i] =
      outputByte (absorbAllAt (rateBits := 576) (by decide) msg) i := by
  simp only [keccak512, sponge, squeezeBytes, Vector.getElem_ofFn]

/-- The lane implementation of Keccak-256 equals the bit model, for every message. -/
theorem keccak256_eq (msg : ByteArray) : Keccak.keccak256 msg = keccak256 msg := by
  simpa only [Keccak.keccak256, Keccak.RATE, Keccak.DIGEST_LEN, keccak256] using
    sponge_eq_of_squeeze (rate := 136) (outBytes := Keccak.DIGEST_LEN) (by decide) ⟨17, rfl⟩
      (by decide) (by decide) Keccak.Internal.squeeze
      (fun a i => (outputByte_eq_squeeze a i).symm) msg

/-- The lane implementation of Keccak-512 equals the bit model, for every message. -/
theorem keccak512_eq (msg : ByteArray) : Keccak.keccak512 msg = keccak512 msg := by
  simpa only [Keccak.keccak512, Keccak.RATE_512, Keccak.DIGEST_LEN_512, keccak512] using
    sponge_eq_of_squeeze (rate := 72) (outBytes := Keccak.DIGEST_LEN_512) (by decide) ⟨9, rfl⟩
      (by decide) (by decide) Keccak.Internal.squeeze512
      (fun a i => (outputByte_eq_squeeze512 a i).symm) msg

end EthLib.Cryptography.Models.KeccakBits
