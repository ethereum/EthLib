module

public import EthLib.Serialization.Rlp.Decode

/-!
# `Serialization.Proofs.Rlp.Bytes`

The decoder reads the bytes of an array between two positions.

The theorems below see those bytes as a list, which the other proofs split and join.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

/-- Two byte arrays with the same bytes are equal. -/
theorem byteArray_eq_of_toList (a b : ByteArray) (h : a.data.toList = b.data.toList) : a = b := by
  cases a; cases b
  simp only [Array.toList_inj] at h
  rw [h]

/-- The bytes between two positions have as many bytes as the positions are apart. -/
theorem length_extract_toList (input : ByteArray) (pos stop : Nat) (hStop : stop ≤ input.size) :
    (input.extract pos stop).data.toList.length = stop - pos := by
  simp only [Array.length_toList, ByteArray.size_data, ByteArray.size_extract]
  omega

/-- No bytes lie between two positions that are not in order. -/
theorem extract_toList_of_le (input : ByteArray) (pos stop : Nat) (h : stop ≤ pos) :
    (input.extract pos stop).data.toList = [] := by
  simp
  omega

/-- The bytes from a position before the end are the byte there, then the bytes after it. -/
theorem extract_toList_cons (input : ByteArray) (pos stop : Nat) (hPos : pos < stop)
    (hStop : stop ≤ input.size) :
    (input.extract pos stop).data.toList =
      input.get! pos :: (input.extract (pos + 1) stop).data.toList := by
  obtain ⟨data⟩ := input
  simp only [ByteArray.size] at hStop
  simp only [ByteArray.get!, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop]
  rw [← List.getElem_cons_drop (by simp; omega)]
  simp only [Array.getElem_toList, getElem!_pos data pos (by omega)]
  rw [show stop - pos = stop - (pos + 1) + 1 by omega, List.take_succ_cons]

/-- Bytes that start with `b` start at a position before the end, with the byte `b` there. -/
theorem extract_toList_eq_cons {input : ByteArray} {pos stop : Nat} {b : UInt8} {rest : List UInt8}
    (hStop : stop ≤ input.size) (h : (input.extract pos stop).data.toList = b :: rest) :
    pos < stop ∧ input.get! pos = b ∧ (input.extract (pos + 1) stop).data.toList = rest := by
  by_cases hPos : pos < stop
  · rw [extract_toList_cons input pos stop hPos hStop, List.cons.injEq] at h
    exact ⟨hPos, h⟩
  · rw [extract_toList_of_le input pos stop (by omega)] at h
    cases h

/-- Bytes split in two at a position: the bytes before it, then the bytes after it. -/
theorem extract_toList_split (input : ByteArray) (pos mid stop : Nat) (h1 : pos ≤ mid)
    (h2 : mid ≤ stop) :
    (input.extract pos stop).data.toList =
      (input.extract pos mid).data.toList ++ (input.extract mid stop).data.toList := by
  rw [ByteArray.extract_eq_extract_append_extract mid h1 h2, ByteArray.toList_data_append]

/-- Bytes that are `l1 ++ l2` split after the bytes of `l1`. -/
theorem extract_toList_eq_append {input : ByteArray} {pos stop : Nat} {l1 l2 : List UInt8}
    (hPos : pos ≤ stop) (hStop : stop ≤ input.size)
    (h : (input.extract pos stop).data.toList = l1 ++ l2) :
    pos + l1.length ≤ stop ∧ (input.extract pos (pos + l1.length)).data.toList = l1 ∧
      (input.extract (pos + l1.length) stop).data.toList = l2 := by
  have hLen := congrArg List.length h
  rw [length_extract_toList input pos stop hStop, List.length_append] at hLen
  have hMid : pos + l1.length ≤ stop := by omega
  rw [extract_toList_split input pos (pos + l1.length) stop (by omega) hMid] at h
  have hLen1 := length_extract_toList input pos (pos + l1.length) (by omega)
  obtain ⟨h1, h2⟩ := List.append_inj h (by omega)
  exact ⟨hMid, h1, h2⟩

/-- Reading `k` bytes in base 256 is the fold of those bytes. -/
theorem readBigEndian_eq (input : ByteArray) (pos k acc : Nat) (hStop : pos + k ≤ input.size) :
    readBigEndian input pos k acc =
      (input.extract pos (pos + k)).data.toList.foldl
        (fun acc byte => 256 * acc + byte.toNat) acc := by
  induction k generalizing pos acc with
  | zero => simp [readBigEndian]
  | succ k ih =>
    rw [readBigEndian, ih (pos + 1) _ (by omega),
      extract_toList_cons input pos (pos + (k + 1)) (by omega) hStop, List.foldl_cons,
      show pos + 1 + k = pos + (k + 1) by omega]

/-- Reading `k` bytes in base 256 from zero is the number they write. -/
theorem readBigEndian_zero (input : ByteArray) (pos k : Nat) (hStop : pos + k ≤ input.size) :
    readBigEndian input pos k 0 = ofBigEndian (input.extract pos (pos + k)).data.toList :=
  readBigEndian_eq input pos k 0 hStop

end EthLib.Serialization.Rlp
