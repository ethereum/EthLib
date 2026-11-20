module

public import EthLib.Serialization.Proofs.Ssz.Codec.Loops

/-! Packed byte storage preserves the bytes and errors of SSZ serialization. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

mutual

/-- Read the bytes of a packed value as ordinary arrays. -/
def ValueOf.toArrayValue : ValueOf ByteArray → Value
  | .bool b => .bool b
  | .uint n => .uint n
  | .bytes bs => .bytes bs.data
  | .bits data => .bits data
  | .seq vs => .seq (ValueOf.toArrayValues vs)
  | .union tag v => .union tag (ValueOf.toArrayValue v)

/-- Replace the packed bytes of each value in order. -/
def ValueOf.toArrayValues : List (ValueOf ByteArray) → List Value
  | [] => []
  | v :: vs => ValueOf.toArrayValue v :: ValueOf.toArrayValues vs

end

/-- Replacing the packed leaves of a list of values acts element by element. -/
theorem ValueOf.toArrayValues_eq (vs : List (ValueOf ByteArray)) :
    ValueOf.toArrayValues vs = vs.map ValueOf.toArrayValue := by
  induction vs <;> simp [ValueOf.toArrayValues, *]

private def arraySlots (slots : List (Bool × ByteArray)) : List (Bool × Array UInt8) :=
  slots.map fun (flag, bytes) => (flag, bytes.data)

@[simp] private theorem buffer_size_packed (bytes : ByteArray) :
    ByteBuffer.size bytes = bytes.data.size := rfl

@[simp] private theorem buffer_reserve_packed (n : Nat) :
    (ByteBuffer.reserve n : ByteArray).data = (ByteBuffer.reserve n : Array UInt8) := rfl

@[simp] private theorem buffer_ofArray_packed (bytes : Array UInt8) :
    (ByteBuffer.ofArray bytes : ByteArray).data = (ByteBuffer.ofArray bytes : Array UInt8) := rfl

@[simp] private theorem byteHeadWidthFrom (slots : List (Bool × ByteArray)) (out : Nat) :
    headWidthFrom slots out = headWidthFrom (arraySlots slots) out := by
  induction slots generalizing out with
  | nil => rfl
  | cons part parts ih =>
    obtain ⟨isInline, bytes⟩ := part
    cases isInline <;> simp [headWidthFrom, arraySlots, ih]

@[simp] private theorem byteBodyWidthFrom (slots : List (Bool × ByteArray)) (out : Nat) :
    bodyWidthFrom slots out = bodyWidthFrom (arraySlots slots) out := by
  induction slots generalizing out with
  | nil => rfl
  | cons part parts ih =>
    obtain ⟨isInline, bytes⟩ := part
    cases isInline <;> simp [bodyWidthFrom, arraySlots, ih]

@[simp] private theorem byteHeadOfFrom (start : Nat) (slots : List (Bool × ByteArray))
    (out : ByteArray) :
    (headOfFrom start slots out).data = headOfFrom start (arraySlots slots) out.data := by
  induction slots generalizing out start with
  | nil => rfl
  | cons part parts ih =>
    obtain ⟨isInline, bytes⟩ := part
    cases isInline <;> simp [headOfFrom, arraySlots, ih]

@[simp] private theorem byteBodiesOfFrom (slots : List (Bool × ByteArray)) (out : ByteArray) :
    (bodiesOfFrom slots out).data = bodiesOfFrom (arraySlots slots) out.data := by
  induction slots generalizing out with
  | nil => rfl
  | cons part parts ih =>
    obtain ⟨isInline, bytes⟩ := part
    cases isInline <;> simp [bodiesOfFrom, arraySlots, ih]

@[simp] private theorem byteAssembleSlots (slots : List (Bool × ByteArray)) :
    (assembleSlots slots).map ByteArray.data = assembleSlots (arraySlots slots) := by
  unfold assembleSlots headWidth bodyWidth
  simp only [byteHeadWidthFrom, byteBodyWidthFrom]
  split <;> simp [Except.map, Except.pure, pure, throw, throwThe,
    MonadExceptOf.throw, Bind.bind, Except.bind]

@[simp] private theorem byteAppendFold (parts : List ByteArray) (out : ByteArray) :
    (parts.foldl (· ++ ·) out).data = (parts.map ByteArray.data).foldl (· ++ ·) out.data := by
  induction parts generalizing out <;> simp [*]

@[simp] private theorem byteAssembleFixed (parts : List ByteArray) :
    (assembleFixed parts).map ByteArray.data = assembleFixed (parts.map ByteArray.data) := by
  unfold assembleFixed
  simp only [List.foldl_map, ByteBuffer.size_array, buffer_size_packed]
  split <;> simp [Except.map, Except.pure, pure, throw, throwThe,
    MonadExceptOf.throw, Bind.bind, Except.bind, List.foldl_map]

private theorem arraySlots_zip (flags : List Bool) (parts : List ByteArray) :
    arraySlots (List.zipWith Prod.mk flags parts) =
      List.zipWith Prod.mk flags (parts.map ByteArray.data) := by
  induction flags generalizing parts with
  | nil => rfl
  | cons flag flags ih =>
    cases parts with
    | nil => rfl
    | cons part parts =>
      change (flag, part.data) :: arraySlots (List.zipWith Prod.mk flags parts) = _
      rw [ih]
      rfl

@[simp] private theorem byteAssemble (flags : List Bool) (parts : List ByteArray) :
    (assemble flags parts).map ByteArray.data = assemble flags (parts.map ByteArray.data) := by
  simp [assemble, arraySlots_zip]


@[simp] private theorem ValueOf.toArrayValues_length (vs : List (ValueOf ByteArray)) :
    (ValueOf.toArrayValues vs).length = vs.length := by simp [ValueOf.toArrayValues_eq]

@[simp] private theorem data_packBitsDelimited (bits : Array Bool) :
    (packBitsDelimited bits : ByteArray).data = (packBitsDelimited bits : Array UInt8) := rfl

@[simp] private theorem data_empty_buffer : (∅ : ByteArray).data = (∅ : Array UInt8) := rfl

private theorem arraySlots_variable (parts : List ByteArray) :
    arraySlots (parts.map fun part => (false, part)) =
      (parts.map ByteArray.data).map (fun part => (false, part)) := by
  simp [arraySlots]

/-- The same encoding and error result with either buffer representation. -/
theorem serialize_data_eq : ∀ (shape : Desc) (value : ValueOf ByteArray),
    (serialize shape value).map ByteArray.data = serialize shape (ValueOf.toArrayValue value) := by
  intro shape value
  induction shape, value using serialize.induct
    (motive2 := fun fields values =>
      (serializeStruct fields values).map ByteArray.data =
        serializeStruct fields (ValueOf.toArrayValues values))
    (motive3 := fun fields values =>
      (serializeFields fields values).map (List.map ByteArray.data) =
        serializeFields fields (ValueOf.toArrayValues values))
    (motive4 := fun fields values done =>
      (serializeFieldsFrom fields values done).map (List.map ByteArray.data) =
        serializeFieldsFrom fields (ValueOf.toArrayValues values) (done.map ByteArray.data))
    (motive5 := fun element values =>
      (serializeSequence element values).map ByteArray.data =
        serializeSequence element (ValueOf.toArrayValues values))
    (motive6 := fun element values =>
      (serializeEach element values).map (List.map ByteArray.data) =
        serializeEach element (ValueOf.toArrayValues values))
    (motive7 := fun element values done =>
      (serializeEachFrom element values done).map (List.map ByteArray.data) =
        serializeEachFrom element (ValueOf.toArrayValues values) (done.map ByteArray.data))
  all_goals try rfl
  all_goals
    try simp_all [serialize, ValueOf.toArrayValue, Except.map, Except.pure, pure,
      Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  case case3 width n big => simp [Nat.not_lt.mpr big]
  case case5 length data sized =>
    by_cases overflow : offsetLimit ≤ length <;> simp [overflow]
  case case7 limit data within =>
    simp only [Nat.not_lt.mpr within, ↓reduceIte]
    by_cases overflow : offsetLimit ≤ data.size <;> simp [overflow]
  case case11 limit data big => simp [Nat.not_le.mpr big]
  case case12 limit bits => cases boundCheck limit bits.size <;> rfl
  case case16 element limit elements big => simp [Nat.not_le.mpr big]
  case case17 element limit elements ih =>
    cases boundCheck limit elements.length <;> exact (by first | exact ih | rfl)
  case case20 selectors options selector data ih =>
    cases lookupOption selectors options selector with
    | error => rfl
    | ok option =>
      cases checkSelector selector with
      | error => rfl
      | ok _ =>
        simp only []
        rw [← ih option]
        cases serialize option data <;>
          simp [ByteArray.data_append]
  case case21 shape value _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases shape <;> cases value <;> simp_all [ValueOf.toArrayValue, serialize]
    all_goals (rename_i wrong; exact absurd rfl (wrong _ _ _ _ rfl rfl rfl))
  case case22 fields values ih =>
    simp only [serializeStruct, Bind.bind, Except.bind, ← ih]
    cases serializeFields fields values with
    | error => rfl
    | ok parts => exact byteAssemble (fields.map Desc.isFixed) parts
  case case23 => simp [serializeFields, ValueOf.toArrayValues]
  case case24 field fields value values iht ihh =>
    simp only [serializeFields, ValueOf.toArrayValues, Bind.bind, Except.bind]
    rw [← iht]
    cases serialize field value <;> simp_all
  case case25 fields values empty pair =>
    cases fields <;> cases values
    all_goals first | exact False.elim (empty rfl rfl) |
      exact False.elim (pair _ _ _ _ rfl rfl) | simp [ValueOf.toArrayValues, serializeFields]
  case case26 done => simp [ValueOf.toArrayValues, serializeFieldsFrom]
  case case27 field fields value values done iht ihh =>
    simp only [serializeFieldsFrom, ValueOf.toArrayValues, Bind.bind, Except.bind]
    rw [← iht]
    cases serialize field value <;> simp_all
  case case28 fields values done empty pair =>
    cases fields <;> cases values
    all_goals first | exact False.elim (empty rfl rfl) |
      exact False.elim (pair _ _ _ _ rfl rfl) | simp [ValueOf.toArrayValues, serializeFieldsFrom]
  case case29 element elements ih =>
    simp only [serializeSequence, Bind.bind, Except.bind, ← ih]
    cases serializeEach element elements with
    | error => rfl
    | ok parts =>
      cases parts with
      | nil => rfl
      | cons part parts =>
        simp only [List.map_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        by_cases fixed : element.isFixed = true
        · simp only [fixed, ↓reduceIte]
          exact byteAssembleFixed (part :: parts)
        · simp only [fixed, ↓reduceIte, Bool.false_eq_true]
          have slots := byteAssembleSlots ((part :: parts).map fun bytes => (false, bytes))
          rw [arraySlots_variable] at slots
          exact slots
  case case30 element => simp [serializeEach, ValueOf.toArrayValues]
  case case31 element value rest iht ihh =>
    simp only [serializeEach, ValueOf.toArrayValues, Bind.bind, Except.bind]
    rw [← iht]
    cases serialize element value <;> simp_all
  case case32 element done => simp [ValueOf.toArrayValues, serializeEachFrom]
  case case33 element value rest done iht ihh =>
    simp only [serializeEachFrom, ValueOf.toArrayValues, Bind.bind, Except.bind]
    rw [← iht]
    cases serialize element value <;> simp_all

private theorem serializeEach_byteVector (width : Nat) (parts : List Bytes)
    (within : ∀ part ∈ parts, part.size = width ∧ part.size < offsetLimit) :
    serializeEach (.byteVector width) (parts.map Value.bytes) = .ok parts := by
  induction parts with
  | nil => exact serializeEach_nil _
  | cons part rest ih =>
    obtain ⟨sized, bounded⟩ := within part List.mem_cons_self
    have head : serialize (.byteVector width) (.bytes part : Value) = .ok part := by
      have sizeBuffer : ByteBuffer.size part = part.size := rfl
      simp [serialize, sizeBuffer, ← sized, Nat.not_le_of_lt bounded,
        Pure.pure, Except.pure]
    have tail := ih fun bytes mem => within bytes (List.mem_cons_of_mem _ mem)
    simp [serializeEach_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem fixedSlices_size (data : Bytes) (width index : Nat)
    (bounded : (index + 1) * width ≤ data.size) :
    (data.extract (index * width) ((index + 1) * width)).size = width := by
  rw [Array.size_extract, Nat.min_eq_left bounded, Nat.succ_mul]
  omega

private theorem fixedSlices_fold (data : Bytes) (width count : Nat)
    (bounded : count * width ≤ data.size) :
    let parts := (List.range count).map fun index =>
      data.extract (index * width) ((index + 1) * width)
    parts.foldl (fun total part => total + part.size) 0 = count * width ∧
    parts.foldl (· ++ ·) #[] = data.extract 0 (count * width) := by
  induction count with
  | zero => simp
  | succ count ih =>
    have prefixBound := Nat.le_trans (Nat.mul_le_mul_right width (Nat.le_succ count)) bounded
    obtain ⟨total, joined⟩ := ih prefixBound
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    rw [total, fixedSlices_size data width count bounded, joined, Array.extract_append_extract,
      Nat.min_eq_left (Nat.zero_le _),
      Nat.max_eq_right (Nat.mul_le_mul_right width (Nat.le_succ count)), Nat.succ_mul]
    simp

/-- The fixed-width elements cut from a payload serialize to that exact payload. -/
theorem serialize_byteVectorSlices (data : Bytes) (width count : Nat)
    (sized : data.size = count * width) (bounded : data.size < offsetLimit) :
    serialize (.vector (.byteVector width) count) (.seq ((List.range count).map fun index =>
      .bytes (data.extract (index * width) ((index + 1) * width)))) = .ok data := by
  let parts := (List.range count).map fun index =>
    data.extract (index * width) ((index + 1) * width)
  have within : ∀ part ∈ parts, part.size = width ∧ part.size < offsetLimit := by
    intro part mem
    obtain ⟨index, index_mem, rfl⟩ := List.mem_map.mp mem
    have index_lt := List.mem_range.mp index_mem
    have last : (index + 1) * width ≤ data.size := by
      rw [sized]
      exact Nat.mul_le_mul_right width (by omega)
    have partSize := fixedSlices_size data width index last
    exact ⟨partSize, Nat.lt_of_le_of_lt (by simp [Array.size_extract]; omega) bounded⟩
  have mapped : (List.range count).map (fun index => Value.bytes
      (data.extract (index * width) ((index + 1) * width))) = parts.map Value.bytes := by
    simp [parts, List.map_map, Function.comp_def]
  have counted : parts.length = count := by simp [parts]
  change serialize (.vector (.byteVector width) count)
    (Value.seq ((List.range count).map (fun index => Value.bytes
      (data.extract (index * width) ((index + 1) * width))))) = .ok data
  rw [mapped]
  have wrote : assembleFixed parts = .ok data := by
    obtain ⟨total, joined⟩ := fixedSlices_fold data width count (Nat.le_of_eq sized.symm)
    have totalSize : parts.foldl (fun total part => total + part.size) 0 = data.size :=
      total.trans sized.symm
    have joinedData : parts.foldl (· ++ ·) #[] = data :=
      joined.trans (Array.extract_eq_self_of_le (Nat.le_of_eq sized))
    have bufferSize (part : Bytes) : ByteBuffer.size part = part.size := rfl
    have reserve (size : Nat) : (ByteBuffer.reserve size : Bytes) = #[] := by
      change Array.emptyWithCapacity size = #[]
      exact Array.emptyWithCapacity_eq
    simp only [assembleFixed, bufferSize, totalSize, Nat.not_le_of_lt bounded, ite_false,
      reserve, joinedData, Pure.pure, Except.pure]
  rw [serialize]
  simp only [List.length_map, counted, beq_self_eq_true, ite_true, serializeSequence,
    serializeEach_byteVector width parts within, Bind.bind, Except.bind]
  cases empty : parts with
  | nil =>
    have emptyReserve : (ByteBuffer.reserve 0 : Bytes) = ∅ := by rfl
    simpa [empty, assembleFixed, offsetLimit, emptyReserve] using wrote
  | cons part rest =>
    rw [empty] at wrote
    simpa only [List.isEmpty_cons, Bool.false_eq_true, ite_false, show
      Desc.isFixed (.byteVector width) = true from rfl, ite_true] using wrote

end EthLib.Serialization.Ssz
