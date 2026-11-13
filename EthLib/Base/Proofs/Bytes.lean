module

public import EthLib.Base.Bytes

/-!
# Proofs: `Bytes`

The bytes of a fixed-size object have its length.

A read of those bytes returns the object.

So two objects with the same bytes are the same object.

The exclusive or of byte strings is commutative, and applying one string twice undoes it.

Applying an untyped string twice undoes it too: a byte past its end reads as zero.

A byte of a join or a slice is a byte of a part, or zero past its end.

Two strings of one size are equal when they agree on every byte.

A loop over the bytes of a string runs as a loop over the list of those bytes, in order.

Inside the array, a bounded read or write of a byte agrees with the defaulting one.
-/

@[expose] public section

namespace EthLib.Base

/-- A bounded byte read agrees with the defaulting read at the same index. -/
theorem byteArray_getElem_eq_get! (bytes : ByteArray) (index : Nat) (inside : index < bytes.size) :
    bytes[index]'inside = bytes.get! index := by
  change bytes.data[index] = bytes.data[index]!
  exact (getElem!_pos bytes.data index inside).symm

/-- A bounded byte write agrees with the defaulting write at the same index. -/
theorem byteArray_set_eq_set! (bytes : ByteArray) (index : Nat) (value : UInt8)
    (inside : index < bytes.size) : bytes.set index value inside = bytes.set! index value := by
  cases bytes with
  | mk data =>
    change index < data.size at inside
    change ByteArray.mk (data.set index value inside) =
      ByteArray.mk (data.setIfInBounds index value)
    rw [Array.setIfInBounds_def, dite_eq_left inside]

/-- A fixed-size object serializes to exactly its own length. -/
@[simp] theorem size_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).size = n := v.size_toArray

/-- Reading the bytes of an object returns that object. -/
@[simp] theorem readBytes_packBytes {n : Nat} (v : Vector UInt8 n) (h) :
    readBytes (packBytes v) 0 n h = v := by
  apply Vector.ext
  intro i hi
  simp [readBytes, packBytes]

/-- Two objects with the same bytes are the same object. -/
theorem packBytes_injective {n : Nat} :
    Function.Injective (packBytes (n := n)) := by
  -- The bytes are the object's array, and the array determines the vector.
  intro v w h
  exact Vector.toArray_inj.mp (congrArg ByteArray.data h)

/-- The exclusive or of two byte strings does not depend on their order. -/
theorem xorBytes_comm {n : Nat} (a b : Vector UInt8 n) : xorBytes a b = xorBytes b a := by
  apply Vector.ext
  intro i hi
  simp [xorBytes, UInt8.xor_comm]

/-- Applying the same byte string twice gives back the first string. -/
@[simp] theorem xorBytes_xorBytes_cancel_right {n : Nat} (a b : Vector UInt8 n) :
    xorBytes (xorBytes a b) b = a := by
  apply Vector.ext
  intro i hi
  simp [xorBytes, UInt8.xor_assoc]

/-! ## One byte of a buffer -/

/-- A byte of the buffer is the byte of its array, or zero past its end. -/
theorem byteAt_eq_getD (data : ByteArray) (i : Nat) : byteAt data i = data.data.getD i 0 := by
  unfold byteAt
  split
  · rename_i h
    simp [Array.getD_eq_getD_getElem?, ByteArray.getElem_eq_getElem_data,
      Array.getElem?_eq_getElem (by simpa [← ByteArray.size_data] using h)]
  · rename_i h
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
      (by simpa [← ByteArray.size_data] using Nat.le_of_not_lt h)]

/-- Past the end of the buffer every byte reads as zero. -/
theorem byteAt_of_size_le {data : ByteArray} {i : Nat} (h : data.size ≤ i) :
    byteAt data i = 0 := by
  simp [byteAt_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- A byte of two strings joined is a byte of the first, or of the second past its end. -/
theorem byteAt_append (a b : ByteArray) (i : Nat) :
    byteAt (a ++ b) i = if i < a.size then byteAt a i else byteAt b (i - a.size) := by
  have hs := @ByteArray.size_append a b
  unfold byteAt
  by_cases ha : i < a.size
  · rw [ite_eq_left ha, dite_eq_left ha, dite_eq_left (show i < (a ++ b).size by omega),
      ByteArray.getElem_append_left ha]
  · rw [ite_eq_right ha]
    by_cases hb : i - a.size < b.size
    · rw [dite_eq_left hb, dite_eq_left (show i < (a ++ b).size by omega),
        ByteArray.getElem_append_right (Nat.le_of_not_lt ha)]
    · rw [dite_eq_right hb, dite_eq_right (show ¬i < (a ++ b).size by omega)]

/-- Padding the buffer with zero bytes on the right changes no byte. -/
theorem byteAt_append_zeros (data : ByteArray) (n i : Nat) :
    byteAt (data ++ ByteArray.mk (Array.replicate n 0)) i = byteAt data i := by
  rw [byteAt_append]
  split
  · rfl
  · rw [byteAt_eq_getD, Nat.not_lt.mp ‹_› |> byteAt_of_size_le |>.symm]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl

/-- A byte of a slice is the byte at the same offset from its start, or zero past its end. -/
theorem byteAt_extract (b : ByteArray) (start stop j : Nat) :
    byteAt (b.extract start stop) j
      = if start + j < min stop b.size then byteAt b (start + j) else 0 := by
  have hs := @ByteArray.size_extract b start stop
  have hm := Nat.min_le_right stop b.size
  unfold byteAt
  by_cases hj : start + j < min stop b.size
  · rw [ite_eq_left hj, dite_eq_left (show j < (b.extract start stop).size by omega),
      dite_eq_left (show start + j < b.size by omega), ByteArray.getElem_extract]
  · rw [ite_eq_right hj, dite_eq_right (show ¬j < (b.extract start stop).size by omega)]

/-- Two strings of one size are equal when they agree on every byte. -/
theorem eq_of_byteAt {a b : ByteArray} (size : a.size = b.size)
    (bytes : ∀ i, byteAt a i = byteAt b i) : a = b := by
  apply ByteArray.ext
  apply Array.ext size
  intro i ha hb
  have h := bytes i
  unfold byteAt at h
  rw [dite_eq_left (show i < a.size from ha), dite_eq_left (show i < b.size from hb)] at h
  exact h

/-- Writing one byte of a buffer changes that byte and no other. -/
theorem byteAt_set {acc : ByteArray} {i : Nat} (h : i < acc.size) (v : UInt8) (j : Nat) :
    byteAt (acc.set i v h) j = if j = i then v else byteAt acc j := by
  have hs : (acc.set i v h).size = acc.size := by
    simp only [ByteArray.set, ByteArray.size, Array.size_set]
  unfold byteAt
  by_cases hj : j = i
  · subst hj
    rw [ite_eq_left rfl, dite_eq_left (show j < (acc.set j v h).size by omega)]
    simp [ByteArray.set, ByteArray.getElem_eq_getElem_data]
  · rw [ite_eq_right hj]
    by_cases hlt : j < acc.size
    · rw [dite_eq_left (show j < (acc.set i v h).size by omega), dite_eq_left hlt]
      simp [ByteArray.set, ByteArray.getElem_eq_getElem_data, Array.getElem_set, Ne.symm hj]
    · rw [dite_eq_right (show ¬j < (acc.set i v h).size by omega), dite_eq_right hlt]

/-- A byte of the exclusive or is the exclusive or of both bytes, or zero past the first string. -/
theorem byteAt_xorByteArray (a b : ByteArray) (j : Nat) :
    byteAt (xorByteArray a b) j = if j < a.size then byteAt a j ^^^ byteAt b j else 0 := by
  -- From index `i` on, the loop XORs each byte of the buffer with the byte of `b`.
  suffices ∀ i acc, byteAt (xorByteArray.go b i acc) j =
      if i ≤ j ∧ j < acc.size then byteAt acc j ^^^ byteAt b j else byteAt acc j by
    rw [xorByteArray, this 0 a]
    by_cases hj : j < a.size
    · simp [hj]
    · simp [hj, byteAt_of_size_le (Nat.le_of_not_lt hj)]
  intro i acc
  induction i, acc using xorByteArray.go.induct b with
  | case1 i acc h ih =>
    rw [xorByteArray.go, dite_eq_left h, ih, byteAt_set h]
    have hs : (acc.set i (acc[i] ^^^ byteAt b i) h).size = acc.size := by
      simp only [ByteArray.set, ByteArray.size, Array.size_set]
    rw [hs]
    by_cases hji : j = i
    · subst hji
      have hacc : acc[j] = byteAt acc j := by unfold byteAt; rw [dite_eq_left h]
      simp [hacc, h, show ¬(j + 1 ≤ j) by omega]
    · by_cases hle : i + 1 ≤ j ∧ j < acc.size
      · simp [hji, hle, show i ≤ j by omega]
      · have : ¬(i ≤ j ∧ j < acc.size) := by omega
        simp [hji, hle, this]
  | case2 i acc h =>
    rw [xorByteArray.go, dite_eq_right h]
    have : ¬(i ≤ j ∧ j < acc.size) := by omega
    simp [this]

/-- Applying the same string twice gives back the first string. -/
@[simp] theorem xorByteArray_xorByteArray_cancel_right (a b : ByteArray) :
    xorByteArray (xorByteArray a b) b = a := by
  apply eq_of_byteAt (by rw [xorByteArray_size, xorByteArray_size])
  intro j
  rw [byteAt_xorByteArray, byteAt_xorByteArray, xorByteArray_size]
  by_cases hj : j < a.size
  · simp [hj, UInt8.xor_assoc]
  · simp [hj, byteAt_of_size_le (Nat.le_of_not_lt hj)]

/-! ## A loop over the bytes -/

/-- A loop over a buffer with `i` bytes left runs as a loop over the last `i` bytes of its list.

With `i + 1` bytes left, it reads byte `size - 1 - i`. -/
theorem forIn_loop_eq_forIn_drop {β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (as : ByteArray) (f : UInt8 → β → m (ForInStep β)) :
    ∀ (i : Nat) (h : i ≤ as.size) (b : β),
      ByteArray.forIn.loop as f i h b = forIn (as.data.toList.drop (as.size - i)) b f := by
  have hl : as.data.toList.length = as.size := Array.length_toList
  intro i
  induction i with
  | zero =>
    intro h b
    rw [ByteArray.forIn.loop.eq_1, Nat.sub_zero, ← hl, List.drop_length]
    rfl
  | succ i ih =>
    intro h b
    have hlt : as.size - (i + 1) < as.data.toList.length := by omega
    rw [ByteArray.forIn.loop.eq_2, List.drop_eq_getElem_cons hlt, List.forIn_cons]
    -- With `i + 1` bytes left, the loop reads the first of them.
    have hget : as[as.size - 1 - i] = as.data.toList[as.size - (i + 1)] := by
      simp only [Array.getElem_toList, show as.size - 1 - i = as.size - (i + 1) by omega]
      rfl
    rw [hget]
    congr 1
    funext r
    cases r with
    | done b => rfl
    | yield b =>
      dsimp only
      rw [ih]
      congr 2
      omega

/-- A loop over the bytes of a buffer runs as a loop over the list of its bytes, in order. -/
theorem forIn_eq_forIn_toList {β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (as : ByteArray) (b : β) (f : UInt8 → β → m (ForInStep β)) :
    forIn as b f = forIn as.data.toList b f := by
  show ByteArray.forIn.loop as f as.size (Nat.le_refl _) b = _
  rw [forIn_loop_eq_forIn_drop, Nat.sub_self, List.drop_zero]

end EthLib.Base
