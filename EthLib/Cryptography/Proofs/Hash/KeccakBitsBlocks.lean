module

public import EthLib.Cryptography.Proofs.Hash.KeccakBitsSqueeze

/-!
# Keccak padded block alignment

FIPS 202 section 4, Algorithm 8, splits the padded input into rate-sized blocks.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

/-- One complete source byte block from the padded message. -/
def paddedByteBlock (msg : ByteArray) (i : Fin (Keccak.blockCount msg.size)) : Vector UInt8 136 :=
  Vector.ofFn fun j => (Keccak.pad msg).data[136 * i.val + j.val]'(by
    have h := Keccak.block_le_size_pad msg i.isLt
    have hj := j.isLt
    simp only [Keccak.RATE, ByteArray.size] at h
    omega)
/-- The same block index in the independent bit representation. -/
def bitIndex (msg : ByteArray) (i : Fin (Keccak.blockCount msg.size)) :
    Fin ((padded msg).length / 1088) := ⟨i.val, by rw [padded_blockCount_eq]; exact i.isLt⟩
/-- The converted block index has the same natural value. -/
theorem bitIndex_val (msg : ByteArray) (i : Fin (Keccak.blockCount msg.size)) :
    (bitIndex msg i).val = i.val := rfl

/-- Every byte block element is the padded source byte at the same offset. -/
theorem paddedByteBlock_get (msg : ByteArray) (i : Fin (Keccak.blockCount msg.size))
    (j : Fin 136) :
    (paddedByteBlock msg i)[j] = (Keccak.pad msg).data[136 * i.val + j.val]'(by
      have h := Keccak.block_le_size_pad msg i.isLt
      have hj := j.isLt
      simp only [Keccak.RATE, ByteArray.size] at h
      omega) := by
  change (paddedByteBlock msg i)[j.val]'j.isLt = _
  simp only [paddedByteBlock, Vector.getElem_ofFn]

/-- Source byte and bit blocks contain the same bits. -/
theorem byteBlock_eq_paddedBlock (msg : ByteArray) (i : Fin (Keccak.blockCount msg.size)) :
    byteBlock (paddedByteBlock msg i) = paddedBlock msg (bitIndex msg i) := by
  apply Vector.ext
  intro j hj
  have hbit := paddedBlock_byteBit msg (bitIndex msg i) ⟨j, by omega⟩
  have hindex : 136 * i.val + j / 8 < (Keccak.pad msg).data.size := by
    have hb := Keccak.block_le_size_pad msg i.isLt
    simp only [Keccak.RATE, ByteArray.size] at hb
    omega
  simp only [byteBlock, Vector.getElem_ofFn, paddedByteBlock]
  change (paddedBlock msg (bitIndex msg i))[j]'hj = _ at hbit
  exact hbit.symm

/-- The byte block is the exact source slice at its block offset. -/
theorem paddedByteBlock_toList (msg : ByteArray) (i : Fin (Keccak.blockCount msg.size)) :
    (paddedByteBlock msg i).toList =
      ((Keccak.pad msg).data.toList.drop (136 * i.val)).take 136 := by
  have h := Keccak.block_le_size_pad msg i.isLt
  simp only [Keccak.RATE, ByteArray.size] at h
  have hlen : (paddedByteBlock msg i).toList.length =
      (((Keccak.pad msg).data.toList.drop (136 * i.val)).take 136).length := by
    simp only [Vector.toList, Array.length_toList, Vector.size_toArray, List.length_take,
      List.length_drop]
    omega
  apply List.ext_getElem hlen
  intro j hj hj2
  have bound : 136 * i.val + j < (Keccak.pad msg).data.size := by
    have : j < 136 := by simpa [Vector.toList, Array.length_toList, Vector.size_toArray] using hj
    omega
  simp only [Vector.getElem_toList, paddedByteBlock, Vector.getElem_ofFn,
    List.getElem_take, List.getElem_drop, Array.getElem_toList]

/-- The source chunk list consists of the aligned complete byte blocks. -/
theorem sourceChunks_eq (msg : ByteArray) :
    Keccak.Internal.chunks 136 (Keccak.blockCount msg.size) (Keccak.pad msg).data.toList =
      (List.finRange (Keccak.blockCount msg.size)).map (fun i => (paddedByteBlock msg i).toList) := by
  have hlen : (Keccak.Internal.chunks 136 (Keccak.blockCount msg.size) (Keccak.pad msg).data.toList).length =
      ((List.finRange (Keccak.blockCount msg.size)).map (fun i => (paddedByteBlock msg i).toList)).length := by
    simp [chunks_length]
  apply List.ext_getElem hlen
  intro j hj hj2
  have hj' : j < Keccak.blockCount msg.size := by simpa [chunks_length] using hj
  have hchunk := chunks_get 136 (Keccak.blockCount msg.size) j (Keccak.pad msg).data.toList hj'
  rw [List.getElem?_eq_getElem hj] at hchunk
  simp only [Option.some.injEq] at hchunk
  rw [hchunk]
  have hbyte := paddedByteBlock_toList msg ⟨j, hj'⟩
  simp only [List.getElem_map, List.getElem_finRange]
  exact hbyte.symm

/-- Both models enumerate the same padded block indices. -/
theorem blockIndices_eq (msg : ByteArray) :
    (List.finRange (Keccak.blockCount msg.size)).map (bitIndex msg) =
      List.finRange ((padded msg).length / 1088) := by
  have counts := padded_blockCount_eq msg
  have hlen : ((List.finRange (Keccak.blockCount msg.size)).map (bitIndex msg)).length =
      (List.finRange ((padded msg).length / 1088)).length := by simp [counts]
  apply List.ext_getElem hlen
  intro j hj hj2
  simp only [List.getElem_map, List.getElem_finRange]
  apply Fin.ext
  rfl

end EthLib.Cryptography.Hash.KeccakBits
