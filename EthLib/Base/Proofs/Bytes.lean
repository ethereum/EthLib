module

public import EthLib.Base.Bytes

/-!
# Proofs: `Bytes`

The bytes of a fixed-size object: their length, the reads that return the object, and equality.

Also the exclusive or of byte strings, the bytes of joins and slices, loops over bytes, and writes.
-/

@[expose] public section

namespace EthLib.Base

/-- A bounded byte read agrees with the defaulting read at the same index. -/
theorem byteArray_getElem_eq_get! (bytes : ByteArray) (index : Nat) (inside : index < bytes.size) :
    bytes[index]'inside = bytes.get! index := by
  change bytes.data[index] = bytes.data[index]!
  exact (getElem!_pos bytes.data index inside).symm

/-- A defaulting write inside the array is read back by the defaulting read. -/
theorem byteArray_get!_set!_self (b : ByteArray) {j : Nat} (v : UInt8)
    (hj : j < b.size) : (b.set! j v).get! j = v := by
  show (b.data.setIfInBounds j v)[j]! = v
  rw [getElem!_pos (b.data.setIfInBounds j v) j
    (by rw [Array.size_setIfInBounds]; exact hj), Array.getElem_setIfInBounds_self]

/-- A defaulting write leaves every other byte unchanged. -/
theorem byteArray_get!_set!_ne (b : ByteArray) {i j : Nat} (v : UInt8)
    (hne : i ≠ j) : (b.set! j v).get! i = b.get! i := by
  show (b.data.setIfInBounds j v)[i]! = b.data[i]!
  by_cases hi : i < b.data.size
  · rw [getElem!_pos (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_pos b.data i hi, Array.getElem_setIfInBounds_ne hi (fun hh => hne hh.symm)]
  · rw [getElem!_neg (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_neg b.data i hi]

/-- Two arrays of one size are equal when their defaulting reads agree inside them. -/
theorem byteArray_ext_get! {a b : ByteArray} (hsz : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext
  apply Array.ext hsz
  intro i hi1 hi2
  have := h i hi1
  rwa [show a.get! i = a.data[i]! from rfl, show b.get! i = b.data[i]! from rfl,
    getElem!_pos a.data i hi1, getElem!_pos b.data i hi2] at this

/-- Writing the same position twice keeps only the second write. -/
theorem byteArray_set!_set! (b : ByteArray) (j : Nat) (u v : UInt8) :
    (b.set! j u).set! j v = b.set! j v := by
  -- Compare the two arrays byte by byte.
  refine byteArray_ext_get! (by rw [ByteArray.size_set!, ByteArray.size_set!,
    ByteArray.size_set!]) (fun i hi => ?_)
  rw [ByteArray.size_set!, ByteArray.size_set!] at hi
  by_cases hij : i = j
  -- At the written position both sides hold the second value.
  · subst hij
    rw [byteArray_get!_set!_self _ _ (by rw [ByteArray.size_set!]; exact hi),
      byteArray_get!_set!_self _ _ hi]
  -- Elsewhere both sides hold the original byte.
  · rw [byteArray_get!_set!_ne _ _ hij, byteArray_get!_set!_ne _ _ hij,
      byteArray_get!_set!_ne _ _ hij]

/-- Writing a byte back to where it was read leaves the array unchanged. -/
theorem byteArray_set!_get!_self (b : ByteArray) {j : Nat} (hj : j < b.size) :
    b.set! j (b.get! j) = b := by
  -- Compare the two arrays byte by byte.
  refine byteArray_ext_get! (ByteArray.size_set! b j _) (fun i hi => ?_)
  rw [ByteArray.size_set!] at hi
  by_cases hij : i = j
  -- At the written position the new byte is the old byte.
  · subst hij; exact byteArray_get!_set!_self b _ hj
  -- Elsewhere nothing changed.
  · exact byteArray_get!_set!_ne b _ hij

/-- A fixed-size object serializes to exactly its own length. -/
@[simp] theorem size_packBytes {n : Nat} (v : Vector UInt8 n) :
    (packBytes v).size = n := v.size_toArray

/-- A read of a buffer gives the entries of its array of bytes, from the offset on.

Proofs rewrite with it to reason about the array of bytes. -/
theorem readBytes_eq_ofFn_data (b : ByteArray) (offset n : Nat) (h : offset + n ≤ b.size) :
    readBytes b offset n h =
      Vector.ofFn fun i => b.data[offset + i.val]'(by simp only [ByteArray.size] at h; omega) :=
  rfl

/-- Reading the bytes of an object returns that object. -/
@[simp] theorem readBytes_packBytes {n : Nat} (v : Vector UInt8 n) (h) :
    readBytes (packBytes v) 0 n h = v := by
  apply Vector.ext
  intro i hi
  simp [readBytes_eq_ofFn_data, packBytes]

/-- Two objects with the same bytes are the same object. -/
theorem packBytes_injective {n : Nat} :
    Function.Injective (packBytes (n := n)) := by
  -- The bytes are the object's array, and the array determines the vector.
  intro v w h
  exact Vector.toArray_inj.mp (congrArg ByteArray.data h)

/-- A buffer read as an object of its own size has the same bytes. -/
@[simp] theorem packBytes_mk_data {n : Nat} (b : ByteArray) (h : b.data.size = n) :
    packBytes (⟨b.data, h⟩ : Vector UInt8 n) = b := rfl

/-- An array of the wanted length reads as its own elements. -/
theorem exactArray?_of_size_eq {α : Type} {n : Nat} {a : Array α} (h : a.size = n) :
    exactArray? n a = some ⟨a, h⟩ :=
  dite_eq_left h

/-- An array of any other length reads as nothing. -/
theorem exactArray?_of_size_ne {α : Type} {n : Nat} {a : Array α} (h : a.size ≠ n) :
    exactArray? n a = none :=
  dite_eq_right h

/-- The elements of a vector, read back at its length, give the vector. -/
@[simp] theorem exactArray?_toArray {α : Type} {n : Nat} (v : Vector α n) :
    exactArray? n v.toArray = some v :=
  exactArray?_of_size_eq v.size_toArray

/-- An array of the wanted length reads as its own elements. -/
theorem exactArray_of_size_eq {α ε : Type} {n : Nat} {a : Array α} (bad : Nat → ε)
    (h : a.size = n) : exactArray n a bad = .ok ⟨a, h⟩ := by
  simp [exactArray, exactArray?_of_size_eq h]

/-- An array of any other length gives the error built from its length. -/
theorem exactArray_of_size_ne {α ε : Type} {n : Nat} {a : Array α} (bad : Nat → ε)
    (h : a.size ≠ n) : exactArray n a bad = .error (bad a.size) := by
  simp [exactArray, exactArray?_of_size_ne h]

/-- The elements of a vector, read back at its length, give the vector. -/
@[simp] theorem exactArray_toArray {α ε : Type} {n : Nat} (v : Vector α n) (bad : Nat → ε) :
    exactArray n v.toArray bad = .ok v :=
  exactArray_of_size_eq bad v.size_toArray

/-- An array reads as a vector exactly when the vector has the elements of the array. -/
theorem exactArray_eq_ok_iff {α ε : Type} {n : Nat} {a : Array α} {bad : Nat → ε}
    {v : Vector α n} : exactArray n a bad = .ok v ↔ v.toArray = a := by
  by_cases h : a.size = n
  · rw [exactArray_of_size_eq bad h]
    constructor
    · intro made
      cases made
      rfl
    · rintro rfl
      rfl
  · rw [exactArray_of_size_ne bad h]
    constructor
    · intro made
      cases made
    · rintro rfl
      exact absurd v.size_toArray h

/-- A vector read from an array has the elements of that array. -/
theorem toArray_of_exactArray? {α : Type} {n : Nat} {a : Array α} {v : Vector α n}
    (h : exactArray? n a = some v) : v.toArray = a := by
  unfold exactArray? at h
  split at h
  · cases h
    rfl
  · cases h

/-- The bytes of an object, read back at its size, give the object. -/
@[simp] theorem exactBytes?_packBytes {n : Nat} (v : Vector UInt8 n) :
    exactBytes? n (packBytes v) = some v :=
  exactArray?_toArray v

/-- A buffer of the wanted length reads as its own bytes. -/
theorem exactBytes?_of_size_eq {n : Nat} {b : ByteArray} (h : b.size = n) :
    exactBytes? n b = some ⟨b.data, h⟩ :=
  exactArray?_of_size_eq h

/-- A buffer of any other length reads as nothing. -/
theorem exactBytes?_of_size_ne {n : Nat} {b : ByteArray} (h : b.size ≠ n) :
    exactBytes? n b = none :=
  exactArray?_of_size_ne h

/-- A buffer of the wanted length reads as its own bytes. -/
theorem exactBytes_of_size_eq {ε : Type} {n : Nat} {b : ByteArray} (bad : Nat → ε)
    (h : b.size = n) : exactBytes n b bad = .ok ⟨b.data, h⟩ :=
  exactArray_of_size_eq bad h

/-- A buffer of any other length gives the error built from its length. -/
theorem exactBytes_of_size_ne {ε : Type} {n : Nat} {b : ByteArray} (bad : Nat → ε)
    (h : b.size ≠ n) : exactBytes n b bad = .error (bad b.size) :=
  exactArray_of_size_ne bad h

/-- A buffer built from an object's array, read back at its size, gives the object. -/
@[simp] theorem exactBytes_mk_toArray {ε : Type} {n : Nat} (v : Vector UInt8 n) (bad : Nat → ε) :
    exactBytes n ⟨v.toArray⟩ bad = .ok v :=
  exactBytes_of_size_eq (b := ⟨v.toArray⟩) bad v.size_toArray

/-- The packed bytes of an object, read back at its size, give the object. -/
@[simp] theorem exactBytes_packBytes {ε : Type} {n : Nat} (v : Vector UInt8 n) (bad : Nat → ε) :
    exactBytes n (packBytes v) bad = .ok v :=
  exactArray_toArray v bad

/-- A buffer reads as an object exactly when the object has the bytes of the buffer. -/
theorem exactBytes_eq_ok_iff {ε : Type} {n : Nat} {b : ByteArray} {bad : Nat → ε}
    {v : Vector UInt8 n} : exactBytes n b bad = .ok v ↔ v.toArray = b.data :=
  exactArray_eq_ok_iff

/-- A buffer fails to read exactly when it has another length, with the error for that length. -/
theorem exactBytes_eq_error_iff {ε : Type} {n : Nat} {b : ByteArray} {bad : Nat → ε} {e : ε} :
    exactBytes n b bad = .error e ↔ b.size ≠ n ∧ e = bad b.size := by
  by_cases h : b.size = n
  · rw [exactBytes_of_size_eq bad h]
    constructor
    · intro made
      cases made
    · rintro ⟨other, -⟩
      exact absurd h other
  · rw [exactBytes_of_size_ne bad h]
    constructor
    · intro made
      cases made
      exact ⟨h, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

/-- An object read from a buffer has the bytes of that buffer. -/
theorem packBytes_of_exactBytes? {n : Nat} {b : ByteArray} {v : Vector UInt8 n}
    (h : exactBytes? n b = some v) : packBytes v = b := by
  rw [packBytes, toArray_of_exactArray? h]

/-- A byte of an object is the byte at the same index of its bytes. -/
theorem getElem_eq_get!_packBytes {n : Nat} (v : Vector UInt8 n) (i : Nat) (h : i < n) :
    v[i] = (packBytes v).get! i := by
  change v.toArray[i]'(by simpa using h) = v.toArray[i]!
  exact (getElem!_pos v.toArray i (by simpa using h)).symm

/-- Writing a byte of an object writes the same byte of its bytes. -/
theorem packBytes_set {n : Nat} (v : Vector UInt8 n) (i : Nat) (x : UInt8) (h : i < n) :
    packBytes (v.set i x h) = (packBytes v).set! i x := by
  change ByteArray.mk (v.toArray.set i x (by simpa using h)) =
    ByteArray.mk (v.toArray.setIfInBounds i x)
  rw [Array.setIfInBounds_def, dite_eq_left (by simpa using h)]

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
theorem byteAtOrZero_eq_getD (data : ByteArray) (i : Nat) : byteAtOrZero data i = data.data.getD i 0 := by
  unfold byteAtOrZero
  split
  · rename_i h
    simp [Array.getD_eq_getD_getElem?, ByteArray.getElem_eq_getElem_data,
      Array.getElem?_eq_getElem (by simpa [← ByteArray.size_data] using h)]
  · rename_i h
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
      (by simpa [← ByteArray.size_data] using Nat.le_of_not_lt h)]

/-- Past the end of the buffer every byte reads as zero. -/
theorem byteAtOrZero_of_size_le {data : ByteArray} {i : Nat} (h : data.size ≤ i) :
    byteAtOrZero data i = 0 := by
  simp [byteAtOrZero_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- A byte of two strings joined is a byte of the first, or of the second past its end. -/
theorem byteAtOrZero_append (a b : ByteArray) (i : Nat) :
    byteAtOrZero (a ++ b) i = if i < a.size then byteAtOrZero a i else byteAtOrZero b (i - a.size) := by
  have hs := @ByteArray.size_append a b
  unfold byteAtOrZero
  by_cases ha : i < a.size
  · rw [ite_eq_left ha, dite_eq_left ha, dite_eq_left (show i < (a ++ b).size by omega),
      ByteArray.getElem_append_left ha]
  · rw [ite_eq_right ha]
    by_cases hb : i - a.size < b.size
    · rw [dite_eq_left hb, dite_eq_left (show i < (a ++ b).size by omega),
        ByteArray.getElem_append_right (Nat.le_of_not_lt ha)]
    · rw [dite_eq_right hb, dite_eq_right (show ¬i < (a ++ b).size by omega)]

/-- Padding the buffer with zero bytes on the right changes no byte. -/
theorem byteAtOrZero_append_zeros (data : ByteArray) (n i : Nat) :
    byteAtOrZero (data ++ ByteArray.mk (Array.replicate n 0)) i = byteAtOrZero data i := by
  rw [byteAtOrZero_append]
  split
  · rfl
  · rw [byteAtOrZero_eq_getD, Nat.not_lt.mp ‹_› |> byteAtOrZero_of_size_le |>.symm]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl

/-- A byte of a slice is the byte at the same offset from its start, or zero past its end. -/
theorem byteAtOrZero_extract (b : ByteArray) (start stop j : Nat) :
    byteAtOrZero (b.extract start stop) j
      = if start + j < min stop b.size then byteAtOrZero b (start + j) else 0 := by
  have hs := @ByteArray.size_extract b start stop
  have hm := Nat.min_le_right stop b.size
  unfold byteAtOrZero
  by_cases hj : start + j < min stop b.size
  · rw [ite_eq_left hj, dite_eq_left (show j < (b.extract start stop).size by omega),
      dite_eq_left (show start + j < b.size by omega), ByteArray.getElem_extract]
  · rw [ite_eq_right hj, dite_eq_right (show ¬j < (b.extract start stop).size by omega)]

/-- Two strings of one size are equal when they agree on every byte. -/
theorem eq_of_byteAtOrZero {a b : ByteArray} (size : a.size = b.size)
    (bytes : ∀ i, byteAtOrZero a i = byteAtOrZero b i) : a = b := by
  apply ByteArray.ext
  apply Array.ext size
  intro i ha hb
  have h := bytes i
  unfold byteAtOrZero at h
  rw [dite_eq_left (show i < a.size from ha), dite_eq_left (show i < b.size from hb)] at h
  exact h

/-- Writing one byte of a buffer changes that byte and no other. -/
theorem byteAtOrZero_set {acc : ByteArray} {i : Nat} (h : i < acc.size) (v : UInt8) (j : Nat) :
    byteAtOrZero (acc.set i v h) j = if j = i then v else byteAtOrZero acc j := by
  have hs : (acc.set i v h).size = acc.size := by
    simp only [ByteArray.set, ByteArray.size, Array.size_set]
  unfold byteAtOrZero
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
theorem byteAtOrZero_xorByteArray (a b : ByteArray) (j : Nat) :
    byteAtOrZero (xorByteArray a b) j = if j < a.size then byteAtOrZero a j ^^^ byteAtOrZero b j else 0 := by
  -- From index `i` on, the loop XORs each byte of the buffer with the byte of `b`.
  suffices ∀ i acc, byteAtOrZero (xorByteArray.go b i acc) j =
      if i ≤ j ∧ j < acc.size then byteAtOrZero acc j ^^^ byteAtOrZero b j else byteAtOrZero acc j by
    rw [xorByteArray, this 0 a]
    by_cases hj : j < a.size
    · simp [hj]
    · simp [hj, byteAtOrZero_of_size_le (Nat.le_of_not_lt hj)]
  intro i acc
  induction i, acc using xorByteArray.go.induct b with
  | case1 i acc h ih =>
    rw [xorByteArray.go, dite_eq_left h, ih, byteAtOrZero_set h]
    have hs : (acc.set i (acc[i] ^^^ byteAtOrZero b i) h).size = acc.size := by
      simp only [ByteArray.set, ByteArray.size, Array.size_set]
    rw [hs]
    by_cases hji : j = i
    · subst hji
      have hacc : acc[j] = byteAtOrZero acc j := by unfold byteAtOrZero; rw [dite_eq_left h]
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
  apply eq_of_byteAtOrZero (by rw [xorByteArray_size, xorByteArray_size])
  intro j
  rw [byteAtOrZero_xorByteArray, byteAtOrZero_xorByteArray, xorByteArray_size]
  by_cases hj : j < a.size
  · simp [hj, UInt8.xor_assoc]
  · simp [hj, byteAtOrZero_of_size_le (Nat.le_of_not_lt hj)]

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

namespace EthLib.Base

/-- Packing the list view of a byte array recovers that array. -/
@[simp] theorem toByteArray_data_toList (bytes : ByteArray) :
    bytes.data.toList.toByteArray = bytes := by
  apply ByteArray.ext
  simp

end EthLib.Base
