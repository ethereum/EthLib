module

public import EthLib.Cryptography.Proofs.Hash.KeccakBitsPermutation

/-!
# Keccak byte and bit representation

FIPS 202 Appendix B.1 orders the bits in each byte from low to high.
These lemmas relate byte and bit inputs, complete-block absorption and output bits.
The complete sponge correspondence is proved in `KeccakBitsRefinement`.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

/-- A byte's bit at a bounded index, in the source byte order. -/
theorem byteBits_get (b : UInt8) (i : Nat) (hi : i < 8) :
    (byteBits b)[i]'(by simpa [byteBits] using hi) = b.toNat.testBit i := by
  simp only [byteBits, List.getElem_map, List.getElem_range]

/-- A list of bytes contributes eight bits per byte. -/
theorem byteListBits_length (bs : List UInt8) : (bs.flatMap byteBits).length = 8 * bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => simp [byteBits_length, ih]; omega

/-- A bit index selects its byte and its low-to-high position in that byte. -/
theorem byteListBits_get (bs : List UInt8) (i : Nat) (h : i < 8 * bs.length) :
    (bs.flatMap byteBits)[i]'(by rw [byteListBits_length]; exact h) =
      (bs[i / 8]'(by omega)).toNat.testBit (i % 8) := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    have hlen : (byteBits b).length = 8 := byteBits_length b
    simp only [List.flatMap_cons]
    by_cases hi : i < 8
    · rw [List.getElem_append_left (by simpa [hlen] using hi)]
      have div : i / 8 = 0 := Nat.div_eq_of_lt hi
      have rem : i % 8 = i := Nat.mod_eq_of_lt hi
      simp [byteBits, div, rem]
    · rw [List.getElem_append_right (by omega : (byteBits b).length ≤ i)]
      have k : i - 8 < 8 * bs.length := by simp only [List.length_cons] at h; omega
      have j : (i - 8) / 8 + 1 = i / 8 := by omega
      have r : (i - 8) % 8 = i % 8 := by omega
      simp only [hlen]
      rw [ih (i - 8) k]
      simp only [← j, List.getElem_cons_succ, r]

private theorem maskBits : ∀ (first last : Bool) (i : Fin 8),
    (((if first then 1 else 0 : UInt8) ||| (if last then 128 else 0)).toNat.testBit i.val) =
      ((first && (decide (i.val = 0))) || (last && (decide (i.val = 7)))) := by
  decide +kernel
/-- The byte padding sets exactly the first and last source bits. -/
theorem paddingByte_get (len pos bit : Nat) (h : bit < 8) :
    (Keccak.paddingByte len pos).toNat.testBit bit =
      (decide (pos = 0 ∧ bit = 0) ||
       decide (pos + 1 = Keccak.RATE - len % Keccak.RATE ∧ bit = 7)) := by
  have hb := maskBits (decide (pos = 0))
    (decide (pos + 1 = Keccak.RATE - len % Keccak.RATE)) ⟨bit, h⟩
  simpa [Keccak.paddingByte, Bool.and_eq_true] using hb

/-- Each message bit is read from its source byte and bit position. -/
theorem messageBits_get (msg : ByteArray) (i : Nat) (h : i < 8 * msg.size) :
    (messageBits msg)[i]'(by rw [messageBits_length]; exact h) =
      (msg.data[i / 8]'(by simp only [ByteArray.size] at h; omega)).toNat.testBit (i % 8) := by
  unfold messageBits
  have ht : i < 8 * msg.data.toList.length := by simpa only [Array.length_toList, ByteArray.size] using h
  have result := byteListBits_get msg.data.toList i ht
  simp only [Array.getElem_toList] at result
  exact result

/-- Byte-to-bit conversion preserves concatenation. -/
theorem messageBits_append (a b : ByteArray) :
    messageBits (a ++ b) = messageBits a ++ messageBits b := by
  simp only [messageBits, ByteArray.data_append, Array.toList_append, List.flatMap_append]

/-- Byte padding spells exactly the independent pad10*1 bits. -/
theorem paddingBits_eq (len : Nat) : messageBits (Keccak.padding len) = padding (8 * len) := by
  have hl : (messageBits (Keccak.padding len)).length = (padding (8 * len)).length := by
    rw [messageBits_length, Keccak.size_padding, padding_length]
    simp only [Keccak.RATE]
    have h := Nat.mod_lt len (by decide : 0 < 136)
    omega
  apply List.ext_getElem hl
  intro i hi hj
  have hb : i < 8 * (Keccak.padding len).size := by simpa [messageBits_length] using hi
  rw [messageBits_get _ i hb, padding_get _ i hj]
  have bitBound : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have iByte : i / 8 < Keccak.RATE - len % Keccak.RATE := by
    rw [Keccak.size_padding] at hb
    omega
  have byteEq : (Keccak.padding len).data[i / 8]'(by
      simp only [Keccak.padding, Array.size_ofFn]
      exact iByte) = Keccak.paddingByte len (i / 8) := by
    simp [Keccak.padding]
  rw [byteEq, paddingByte_get _ _ _ bitBound]
  have plen : (padding (8 * len)).length = 8 * (Keccak.RATE - len % Keccak.RATE) := by
    rw [← hl, messageBits_length, Keccak.size_padding]
  have first : (i / 8 = 0 ∧ i % 8 = 0) ↔ i = 0 := by omega
  have last : (i / 8 + 1 = Keccak.RATE - len % Keccak.RATE ∧ i % 8 = 7) ↔
      i + 1 = (padding (8 * len)).length := by omega
  simp only [first, last]

/-- Every byte message has identical padded contents in both representations. -/
theorem paddedBits_eq (msg : ByteArray) :
    messageBits (Keccak.pad msg) = padded msg := by
  simp only [Keccak.pad, messageBits_append, padded, messageBits_length, paddingBits_eq]

/-- Each padded block bit comes from the corresponding padded byte and bit. -/
theorem paddedBlock_byteBit (msg : ByteArray) (i : Fin ((padded msg).length / 1088)) (j : Fin 1088) :
    (paddedBlock msg i)[j] =
      ((Keccak.pad msg).data[136 * i.val + j.val / 8]'(by
        have hm := padded_length_eq_lane msg
        have hi := i.isLt
        have hj := j.isLt
        simp only [ByteArray.size] at hm
        omega)).toNat.testBit (j.val % 8) := by
  have bitBound : 1088 * i.val + j.val < (messageBits (Keccak.pad msg)).length := by
    rw [paddedBits_eq]
    have hm := padded_size_multiple msg
    have hi := i.isLt
    have hj := j.isLt
    omega
  have equalBit := messageBits_get (Keccak.pad msg) (1088 * i.val + j.val) (by
    rw [← messageBits_length]; exact bitBound)
  have bitIndex : (1088 * i.val + j.val) / 8 = 136 * i.val + j.val / 8 := by omega
  have bitOffset : (1088 * i.val + j.val) % 8 = j.val % 8 := by omega
  simp only [bitIndex, bitOffset] at equalBit
  rw [paddedBlock_bit]
  simp only [paddedBits_eq] at equalBit
  exact equalBit

private theorem shift8 (v : UInt64) (i : Nat) (hi : i < 64) :
    (v <<< (8 : UInt64)).toBitVec.getLsbD i =
      (decide (8 ≤ i) && v.toBitVec.getLsbD (i - 8)) := by
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat,
    BitVec.shiftLeft_eq', BitVec.toNat_umod, BitVec.toNat_ofNat]
  simp only [show (64 : BitVec 64).toNat = 64 by decide, Nat.reducePow, Nat.reduceMod]
  simp only [BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  by_cases h : i < 8
  · have hn : ¬ 8 ≤ i := by omega
    simp [h, hn]
  · have hg : 8 ≤ i := by omega
    simp [h, hg]
private theorem byteExtend (b : UInt8) (i : Nat) (hi : i < 64) :
    b.toUInt64.toBitVec.getLsbD i = (decide (i < 8) && b.toNat.testBit i) := by
  rw [UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h : i < 8
  · simp only [h, decide_true, Bool.true_and]
    rw [← BitVec.testBit_toNat, UInt8.toNat_toBitVec]
  · have hg : 8 ≤ i := by omega
    simp only [h, decide_false, Bool.false_and]
    exact BitVec.getLsbD_of_ge b.toBitVec i hg

/-- A lane bit selects the matching little-endian byte, or zero past the input. -/
theorem laneOfBytes_bit (bs : List UInt8) (i : Nat) (hi : i < 64) :
    (Keccak.Internal.laneOfBytes bs).toBitVec.getLsbD i =
      (bs[i / 8]?.getD 0).toNat.testBit (i % 8) := by
  induction bs generalizing i with
  | nil => simp [Keccak.Internal.laneOfBytes]
  | cons b bs ih =>
    simp only [Keccak.Internal.laneOfBytes, List.foldr_cons, UInt64.toBitVec_or,
      BitVec.getLsbD_or, byteExtend _ _ hi, shift8 _ _ hi]
    by_cases h : i < 8
    · have hdiv : i / 8 = 0 := Nat.div_eq_of_lt h
      have hmod : i % 8 = i := Nat.mod_eq_of_lt h
      have hn : ¬ 8 ≤ i := by omega
      simp [h, hn, hdiv, hmod]
    · have eight : 8 ≤ i := by omega
      have hdiv : (i - 8) / 8 + 1 = i / 8 := by omega
      have hmod : (i - 8) % 8 = i % 8 := by omega
      have hbound : i - 8 < 64 := by omega
      simp only [Keccak.Internal.laneOfBytes] at ih
      rw [ih (i - 8) hbound]
      simp [h, eight, ← hdiv, hmod]

/-- The selected source chunk starts at its exact byte offset. -/
theorem chunks_get (size count k : Nat) (bytes : List UInt8) (h : k < count) :
    (Keccak.Internal.chunks size count bytes)[k]? = some ((bytes.drop (size * k)).take size) := by
  induction count generalizing k bytes with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [Keccak.Internal.chunks]
    | succ k =>
      have hk : k < n := by omega
      simp only [Keccak.Internal.chunks, List.getElem?_cons_succ]
      rw [ih k (bytes.drop size) hk]
      simp [List.drop_drop, Nat.mul_succ, Nat.add_comm]

/-- A lane built from a chunk reads the corresponding source byte bit. -/
theorem laneChunk_bit (bytes : List UInt8) (k i : Nat) (hi : i < 64) :
    (Keccak.Internal.laneOfBytes ((bytes.drop (8 * k)).take 8)).toBitVec.getLsbD i =
      (bytes[8 * k + i / 8]?.getD 0).toNat.testBit (i % 8) := by
  rw [laneOfBytes_bit _ _ hi]
  have h : i / 8 < 8 := by omega
  simp [List.getElem?_drop, h]

/-- Decode one complete rate block into source-ordered bits. -/
def byteBlock (bytes : Vector UInt8 136) : Block :=
  Vector.ofFn fun i => (bytes[i.val / 8]'(by have := i.isLt; omega)).toNat.testBit (i.val % 8)
/-- Every source block bit selects its source byte and bit position. -/
theorem byteBlock_get (bytes : Vector UInt8 136) (i : Fin 1088) :
    (byteBlock bytes)[i] = (bytes[i.val / 8]'(by have := i.isLt; omega)).toNat.testBit (i.val % 8) := by
  change (byteBlock bytes)[i.val]'i.isLt = _
  simp only [byteBlock, Vector.getElem_ofFn]

/-- Chunking returns exactly the requested number of chunks. -/
theorem chunks_length (size count : Nat) (bytes : List UInt8) :
    (Keccak.Internal.chunks size count bytes).length = count := by
  induction count generalizing bytes with
  | zero => rfl
  | succ n ih => simp [Keccak.Internal.chunks, ih]
/-- Absorbing a complete byte block agrees with independent bit absorption. -/
theorem absorbBlock_ofLanes (a : Keccak.State) (bytes : Vector UInt8 136) :
    ofLanes (Keccak.Internal.absorbBlock a bytes.toList) = absorb (ofLanes a) (byteBlock bytes) := by
  funext x y z
  let k := x.val + 5 * y.val
  have hk : k < 25 := by dsimp [k]; have := x.isLt; have := y.isLt; omega
  have hz := z.isLt
  have address : index x y z = 64 * k + z.val := rfl
  simp only [ofLanes, Keccak.Internal.absorbBlock, Vector.getElem_ofFn,
    UInt64.toBitVec_xor, BitVec.getLsbD_xor, Keccak.RATE]
  change _ = absorb (ofLanes a) (byteBlock bytes) x y z
  unfold absorb
  rw [address]
  simp only [ofLanes, show 136 / 8 = 17 by decide]
  change ((a[k]'(by simpa [Keccak.LANES] using hk)).toBitVec.getLsbD z.val ^^
    (((Keccak.Internal.chunks 8 17 bytes.toList).map Keccak.Internal.laneOfBytes).getD k 0).toBitVec.getLsbD z.val) =
    ((a[k]'(by simpa [Keccak.LANES] using hk)).toBitVec.getLsbD z.val ^^
      (if h : 64 * k + z.val < 1088 then (byteBlock bytes)[64 * k + z.val]'h else false))
  by_cases rate : k < 17
  · have bound : 64 * k + z.val < 1088 := by omega
    simp only [dite_eq_left bound, byteBlock, Vector.getElem_ofFn]
    have lane : ((Keccak.Internal.chunks 8 17 bytes.toList).map Keccak.Internal.laneOfBytes).getD k 0 =
        Keccak.Internal.laneOfBytes ((bytes.toList.drop (8 * k)).take 8) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, chunks_get 8 17 k bytes.toList rate]
      rfl
    rw [lane, laneChunk_bit _ _ _ hz]
    have j : z.val / 8 < 8 := by omega
    have byteIndex : (64 * k + z.val) / 8 = 8 * k + z.val / 8 := by omega
    have bitIndex : (64 * k + z.val) % 8 = z.val % 8 := by omega
    have valid : 8 * k + z.val / 8 < 136 := by omega
    simp only [byteIndex, bitIndex]
    have listBound : 8 * k + z.val / 8 < bytes.toList.length := by simpa using valid
    rw [List.getElem?_eq_getElem listBound]
    simp only [Option.getD_some, Vector.getElem_toList]
  · have bound : ¬64 * k + z.val < 1088 := by omega
    simp only [dite_eq_right bound, Bool.xor_false]
    have hl : ((Keccak.Internal.chunks 8 17 bytes.toList).map Keccak.Internal.laneOfBytes).length = 17 := by
      simp [chunks_length]
    have lane : ((Keccak.Internal.chunks 8 17 bytes.toList).map Keccak.Internal.laneOfBytes).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [lane]
    simp

private def pack8 (a b c d e f g h : Bool) : UInt8 :=
  UInt8.ofNat ((if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
    (if d then 8 else 0) + (if e then 16 else 0) + (if f then 32 else 0) +
    (if g then 64 else 0) + (if h then 128 else 0))
private theorem pack8_bit : ∀ (a b c d e f g h : Bool) (i : Fin 8),
    (pack8 a b c d e f g h).toBitVec.getLsbD i.val = (#v[a,b,c,d,e,f,g,h])[i] := by
  decide +kernel
private theorem carry (p : Bool) (n w : Nat) :
    (if p then n + w else n) = n + (if p then w else 0) := by
  cases p <;> simp
private theorem outputPack (s : State) (index : Nat) :
    outputByte s index = pack8 (stateBit s (8*index+0)) (stateBit s (8*index+1))
      (stateBit s (8*index+2)) (stateBit s (8*index+3)) (stateBit s (8*index+4))
      (stateBit s (8*index+5)) (stateBit s (8*index+6)) (stateBit s (8*index+7)) := by
  simp only [outputByte, pack8, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, carry, Nat.pow_zero, Nat.pow_succ, Nat.reduceMul, Nat.zero_add, Nat.add_zero]

/-- Every output byte bit is the corresponding source state bit. -/
theorem outputByte_bit (s : State) (index : Nat) (bit : Fin 8) :
    (outputByte s index).toBitVec.getLsbD bit.val = stateBit s (8 * index + bit.val) := by
  rw [outputPack]
  have h := pack8_bit (stateBit s (8*index+0)) (stateBit s (8*index+1))
    (stateBit s (8*index+2)) (stateBit s (8*index+3)) (stateBit s (8*index+4))
    (stateBit s (8*index+5)) (stateBit s (8*index+6)) (stateBit s (8*index+7)) bit
  rw [h]
  match bit with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl
  | ⟨n+8, h⟩ => omega

/-- Output bits from a lane state select its little-endian byte bits. -/
theorem state_output_bit (a : Keccak.State) (i j : Nat) (hi : i < 32) (hj : j < 8) :
    stateBit (ofLanes a) (8*i+j) =
      (a[i/8]'(by simp [Keccak.LANES]; omega)).toBitVec.getLsbD (8*(i%8)+j) := by
  have h1 : ((8*i+j)/64)%5 + 5*(((8*i+j)/64)/5 % 5) = i/8 := by omega
  have h2 : (8*i+j)%64 = 8*(i%8)+j := by omega
  simp only [stateBit, ofLanes, xy, zcoord, Nat.mod_mod, h1, h2]


end EthLib.Cryptography.Hash.KeccakBits
