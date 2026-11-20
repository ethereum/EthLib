module

public import EthLib.Serialization.Exports.SszRecord
import EthLib.Serialization.Proofs.Ssz.Type.Legality
import EthLib.Serialization.Proofs.Ssz.Typed.Basic
import all EthLib.Serialization.Exports.SszRecord
import all EthLib.Serialization.Exports.Ssz

/-! The compact record exports agree with the tagged SSZ exports. -/

public section

namespace EthLib.Serialization.Ssz.Exports.Proofs

open EthLib.Exports (PyValue)

private theorem appendRecordField_eq (type : Desc) (value : ValueOf ByteArray) (out : ByteArray) :
    appendRecordField type value out = (do
      let part ← (serialize type value).toOption
      if out.size + part.size ≥ offsetLimit then none else some (out ++ part)) := by
  cases type <;> cases value <;> try rfl
  case uint.uint width number =>
    have data : SszType.pushUintBytes width number out =
        out ++ ByteArray.mk (uintBytes width number) :=
      ByteArray.ext (by simpa only [ByteArray.data_append] using
        SszType.data_pushUintBytes width number out)
    have size : (ByteArray.mk (uintBytes width number)).size = width := by
      simpa only [uintBytes, ← ByteArray.size_data] using
        (Base.uintToBytes width number).size_toArray
    by_cases fits : uintFits width number
    · simp [appendRecordField, serialize, fits, data, bind, Option.bind, ByteBuffer.ofArray, size,
        Except.toOption]
    · simp [appendRecordField, serialize, fits, bind, Option.bind, Except.toOption]

private theorem append_some {cell : RecordCell} {names names' : List String}
    {out out' : ByteArray} (h : cell.append (names, out) = some (names', out')) :
    ∃ type value part, cell.readType = some type ∧ type.wellFormed = .ok () ∧
      cell.readValue id = some value ∧ serialize type value = .ok part ∧
      names' = cell.name :: names ∧ cell.name ∉ names ∧
      out' = out ++ part ∧ out'.size < offsetLimit := by
  simp only [RecordCell.append, appendRecordField_eq] at h
  by_cases named : cell.name ∈ names
  · simp [named] at h
  simp only [List.contains_iff_mem, named, ↓reduceIte, bind, Option.bind] at h
  cases ht : cell.readType with
  | none => simp [ht] at h
  | some type =>
    cases hw : type.wellFormed with
    | error => simp [ht, hw, Except.toOption] at h
    | ok result =>
      cases result
      cases hv : cell.readValue id with
      | none => simp [ht, hw, hv, Except.toOption] at h
      | some value =>
        cases hp : serialize type value with
        | error => simp [ht, hw, hv, hp, Except.toOption] at h
        | ok part =>
          by_cases bound : out.size + part.size < offsetLimit
          · simp [ht, hw, hv, hp, Except.toOption, Nat.not_le.mpr bound] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨type, value, part, rfl, hw, rfl, hp, rfl, named, rfl,
              by simpa [ByteArray.size_append] using bound⟩
          · simp [ht, hw, hv, hp, Except.toOption, Nat.le_of_not_gt bound] at h

private theorem readType_fixed {cell : RecordCell} {type : Desc}
    (h : cell.readType = some type) : type.isFixed = true := by
  unfold RecordCell.readType at h
  split at h <;> simp_all <;> subst type <;> rfl

private theorem readType_tagged {cell : RecordCell} {type : Desc} (fuel : Nat)
    (h : cell.readType = some type) :
    descOf (fuel + 1) (.dict #[(cell.typeTag, .int cell.parameter)]) = .ok type := by
  unfold RecordCell.readType at h
  -- Reduce the tag switch without unfolding recursive cases for other descriptions.
  obtain cell := cell
  cases cell with
  | mk name tag size value payload =>
    simp only at h
    dsimp only [RecordCell.typeTag, RecordCell.parameter] at h ⊢
    split at h <;> simp_all [descOf, tagged, natOf, bind, Except.bind, pure, Except.pure]

private theorem readValue_tagged {cell : RecordCell} {B : Type} {value : ValueOf B}
    (bytes : ByteArray → B) (hex : Array UInt8 → B) (fuel : Nat)
    (h : cell.readValue bytes = some value) :
    valueOfWith bytes hex (fuel + 1) (.dict #[(cell.valueTag,
      match cell.payload with | .nat n => .int n | .bytes b => .bytes b)]) = .ok value := by
  unfold RecordCell.readValue at h
  cases cell with
  | mk name tag size key payload =>
    dsimp only [RecordCell.valueTag, RecordCell.payload] at h ⊢
    split at h <;>
      simp_all [valueOfWith, tagged, natOf, bind, Except.bind, pure, Except.pure]


private theorem fold_cells {cells : List RecordCell} {names names' : List String}
    {out out' : ByteArray} (distinct : names.Nodup) (bound : out.size < offsetLimit)
    (h : cells.foldlM RecordCell.append (names, out) = some (names', out')) :
    ∃ types values parts,
      cells.mapM RecordCell.readType = some types ∧
      cells.mapM (RecordCell.readValue id) = some values ∧
      types.length = cells.length ∧ parts.length = cells.length ∧
      types.all Desc.isFixed = true ∧ Desc.allWellFormed types = .ok () ∧
      names' = (cells.map RecordCell.name).reverse ++ names ∧ names'.Nodup ∧
      out' = parts.foldl (· ++ ·) out ∧ out'.size < offsetLimit ∧
      ∀ done : List ByteArray,
        serializeFieldsFrom types values done = .ok (done.reverse ++ parts) := by
  induction cells generalizing names out with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], [], rfl, rfl, rfl, rfl, rfl, rfl, rfl, distinct, rfl, bound,
      fun done => by simp [serializeFieldsFrom]⟩
  | cons cell rest ih =>
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases step : cell.append (names, out) with
    | none => simp [step] at h
    | some state =>
      obtain ⟨names1, out1⟩ := state
      simp only [step] at h
      obtain ⟨type, value, part, ht, hw, hv, hp, rfl, fresh, rfl, bound1⟩ := append_some step
      have distinct1 := List.nodup_cons.mpr ⟨fresh, distinct⟩
      obtain ⟨types, values, parts, ts, vs, typesLength, partsLength, fixed, valid,
        newNames, distinct', eqBytes, bound', fields⟩ := ih distinct1 bound1 h
      refine ⟨type :: types, value :: values, part :: parts, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        distinct', eqBytes, bound', ?_⟩
      · simp [List.mapM_cons, ht, ts, bind, Option.bind, pure]
      · simp [List.mapM_cons, hv, vs, bind, Option.bind, pure]
      · simp [typesLength]
      · simp [partsLength]
      · simp [readType_fixed ht, fixed]
      · simp [Desc.allWellFormed, hw, valid, bind, Except.bind]
      · simpa [List.reverse_cons, List.append_assoc] using newNames
      · intro done
        simp [serializeFieldsFrom, hp, bind, Except.bind, fields, List.append_assoc]


private theorem fixed_slots (parts : List ByteArray) (start : Nat) (out : ByteArray) :
    headWidthFrom (parts.map fun part => (true, part)) out.size =
      (parts.foldl (· ++ ·) out).size ∧
    bodyWidthFrom (parts.map fun part => (true, part)) start = start ∧
    headOfFrom start (parts.map fun part => (true, part)) out = parts.foldl (· ++ ·) out ∧
    bodiesOfFrom (parts.map fun part => (true, part)) out = out := by
  induction parts generalizing out with
  | nil => simp [headWidthFrom, bodyWidthFrom, headOfFrom, bodiesOfFrom]
  | cons part rest ih =>
    simpa [headWidthFrom, bodyWidthFrom, headOfFrom, bodiesOfFrom, ByteArray.size_append,
      ByteBuffer.size] using And.intro (ih (out ++ part)).1
        (And.intro (ih out).2.1 (And.intro (ih (out ++ part)).2.2.1 (ih out).2.2.2))

private theorem zip_fixed_parts (types : List Desc) (parts : List ByteArray)
    (length : types.length = parts.length) (fixed : types.all Desc.isFixed = true) :
    List.zipWith Prod.mk (types.map Desc.isFixed) parts = parts.map (true, ·) := by
  induction types generalizing parts with
  | nil => cases parts <;> simp_all
  | cons type types ih =>
    cases parts with
    | nil => simp at length
    | cons part parts =>
      simp_all

private theorem assemble_fixed_of_fold {types : List Desc} {parts : List ByteArray}
    {out : ByteArray}
    (length : types.length = parts.length) (fixed : types.all Desc.isFixed)
    (eq : parts.foldl (· ++ ·) (ByteArray.emptyWithCapacity 128) = out)
    (bound : out.size < offsetLimit) :
    assemble (types.map Desc.isFixed) parts = .ok out := by
  have empty (n : Nat) : ByteArray.emptyWithCapacity n = ByteArray.empty := rfl
  have widths := fixed_slots parts 0 ByteArray.empty
  have total : headWidthFrom (parts.map fun part => (true, part)) 0 =
      (parts.foldl (· ++ ·) ByteArray.empty).size := widths.1
  have head := fun start => (fixed_slots parts start ByteArray.empty).2.2.1
  have bodies := fun buf => (fixed_slots parts 0 buf).2.2.2
  simp only [assemble, zip_fixed_parts types parts length fixed, assembleSlots, headWidth,
    bodyWidth, total, widths.2.1, bodies, Nat.add_zero]
  change (if (parts.foldl (· ++ ·) ByteArray.empty).size ≥ offsetLimit then _ else _) = _
  rw [empty] at eq
  simp [eq, Nat.not_le.mpr bound, head, ByteBuffer.reserve, empty, pure, Except.pure]

private theorem serializeFields_empty_from (types : List Desc) (values : List (ValueOf ByteArray)) :
    serializeFields types values = serializeFieldsFrom types values [] := by
  cases types <;> cases values <;> simp [serializeFields, serializeFieldsFrom]

private def taggedType (cell : RecordCell) : PyValue :=
  .dict #[(cell.typeTag, .int cell.parameter)]

private def taggedValue (cell : RecordCell) : PyValue :=
  .dict #[(cell.valueTag, match cell.payload with
    | .nat n => .int n
    | .bytes b => .bytes b)]

private theorem read_fields {cells : List RecordCell} {types : List Desc} (fuel : Nat)
    (h : cells.mapM RecordCell.readType = some types) :
    (cells.map taggedType).mapM (descOf (fuel + 1)) = .ok types := by
  induction cells generalizing types with
  | nil => simpa [pure, Except.pure] using h
  | cons cell cells ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at h
    cases t : cell.readType with
    | none => simp [t] at h
    | some type =>
      cases ts : List.mapM RecordCell.readType cells with
      | none => simp [t, ts] at h
      | some rest =>
        have eq : type :: rest = types := by simpa [t, ts] using h
        subst types
        simp [taggedType, List.mapM_cons, readType_tagged fuel t, ih ts, bind, Except.bind, pure,
          Except.pure]

private theorem read_items {B : Type} {cells : List RecordCell} {values : List (ValueOf B)}
    (bytes : ByteArray → B) (hex : Array UInt8 → B) (fuel : Nat) (out : List (ValueOf B))
    (h : cells.mapM (RecordCell.readValue bytes) = some values) :
    (cells.map taggedValue).foldlM
      (fun done item => do pure ((← valueOfWith bytes hex (fuel + 1) item) :: done)) out =
        .ok (values.reverse ++ out) := by
  induction cells generalizing values out with
  | nil => simpa [pure, Except.pure] using h
  | cons cell cells ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at h
    cases v : cell.readValue bytes with
    | none => simp [v] at h
    | some value =>
      cases vs : List.mapM (RecordCell.readValue bytes) cells with
      | none => simp [v, vs] at h
      | some rest =>
        have eq : value :: rest = values := by simpa [v, vs] using h
        subst values
        simp [taggedValue, List.foldlM_cons, readValue_tagged bytes hex fuel v,
          bind, Except.bind, pure, Except.pure]
        simpa [bind, Except.bind, pure, Except.pure] using ih (value :: out) vs

private theorem record_desc {cells : Array RecordCell} {types : List Desc} (fuel : Nat)
    (valueTag : String) (h : cells.toList.mapM RecordCell.readType = some types) :
    descOf (fuel + 2) (recordArgs "container" valueTag cells).1 =
      .ok (.container (cells.toList.map RecordCell.name) types) := by
  simp [recordArgs, descOf, tagged, itemsOf, bind, Except.bind, pure, Except.pure]
  have pairs :
      List.mapM (fun cell => pair (PyValue.tuple #[.str cell.name, taggedType cell]))
        cells.toList = .ok (cells.toList.map fun cell => (.str cell.name, taggedType cell)) := by
    induction cells.toList with
    | nil => rfl
    | cons cell rest ih =>
      have head : pair (.tuple #[.str cell.name, taggedType cell]) =
          .ok (.str cell.name, taggedType cell) := rfl
      simp [head, ih, List.mapM_cons, bind, Except.bind, pure, Except.pure]
  rw [show (pair ∘ fun a : RecordCell => .tuple #[.str a.name,
      .dict #[(a.typeTag, .int a.parameter)]]) =
    (fun a : RecordCell => pair (.tuple #[.str a.name, taggedType a])) from rfl, pairs]
  have names : List.mapM (fun cell : RecordCell => strOf (.str cell.name)) cells.toList =
      .ok (cells.toList.map RecordCell.name) := by
    induction cells.toList with
    | nil => rfl
    | cons cell rest ih =>
      simp only [List.mapM_cons, List.map_cons, ih]
      rfl
  simp only [List.mapM_map, Function.comp_def, names]
  have reads := read_fields fuel h
  simp only [List.mapM_map, Function.comp_def] at reads
  rw [reads]

private theorem record_value {B : Type} {cells : Array RecordCell} {values : List (ValueOf B)}
    (bytes : ByteArray → B) (hex : Array UInt8 → B) (fuel : Nat) (typeTag : String)
    (h : cells.toList.mapM (RecordCell.readValue bytes) = some values) :
    valueOfWith bytes hex (fuel + 2) (recordArgs typeTag "seq" cells).2 = .ok (.seq values) := by
  rw [valueOfWith]
  change ((cells.map taggedValue).foldlM (fun acc item => do
    pure ((← valueOfWith bytes hex (fuel + 1) item) :: acc)) [] >>= fun vs =>
      Except.ok (ValueOf.seq vs.reverse)) = Except.ok (ValueOf.seq values)
  rw [← Array.foldlM_toList, Array.toList_map, read_items bytes hex fuel [] h]
  simp [bind, Except.bind]

/-- The compact serializer has the same result as the tagged serializer. -/
theorem serializeRecordExport_eq (typeTag valueTag : String) (cells : Array RecordCell) :
    serializeRecordExport typeTag valueTag cells =
      serializeOf (recordArgs typeTag valueTag cells) := by
  unfold serializeRecordExport
  cases h : serializeRecord typeTag valueTag cells with
  | none => rfl
  | some out =>
    have typeKey : typeTag = "container" := by
      by_cases valid : typeTag = "container"
      · exact valid
      · simp [serializeRecord, valid] at h
    have valueKey : valueTag = "seq" := by
      by_cases valid : valueTag = "seq"
      · exact valid
      · simp [serializeRecord, valid] at h
    have nonempty : cells.isEmpty = false := by
      cases empty : cells.isEmpty
      · rfl
      · simp [serializeRecord, empty] at h
    subst typeTag valueTag
    simp only [serializeRecord, bne_self_eq_false, Bool.false_or, nonempty, Bool.false_eq_true,
      ↓reduceIte, ← Array.foldlM_toList, bind, Option.bind, pure] at h
    cases fold : cells.toList.foldlM RecordCell.append ([], ByteArray.emptyWithCapacity 128) with
    | none => simp [fold] at h
    | some state =>
      obtain ⟨names, buffer⟩ := state
      have outEq : buffer = out := by simpa [fold] using h
      subst buffer
      obtain ⟨types, values, parts, cTypes, cValues, typesLen, partsLen, fixed, valid,
        namesEq, distinct, bytesEq, offset, fields⟩ := fold_cells List.nodup_nil (by decide) fold
      have allFields : serializeFields types values = .ok parts := by
        rw [serializeFields_empty_from]
        simpa only [List.reverse_nil, List.nil_append] using fields []
      have canonicalBytes :=
        assemble_fixed_of_fold (typesLen.trans partsLen.symm) fixed bytesEq.symm offset
      have parseType := record_desc (fuel := 254) "seq" cTypes
      have parseValue := record_value id ByteArray.mk 254 "container" cValues
      have distinctNames : (cells.toList.map RecordCell.name).Nodup := by
        simpa [namesEq, List.Nodup, List.pairwise_reverse, ne_comm] using distinct
      have typeNonempty : types ≠ [] := by
        intro empty
        have nc : cells.size = 0 := by simpa [empty] using typesLen.symm
        have hc : cells.isEmpty = true := by simp [Array.isEmpty, nc]
        simp [nonempty] at hc
      have typeWellFormed :
          (Desc.container (cells.toList.map RecordCell.name) types).wellFormed = .ok () := by
        apply (wellFormed_container_iff _ _).mpr
        exact ⟨typeNonempty, by simpa using typesLen.symm,
          firstDuplicate_of_nodup _ distinctNames, valid⟩
      simp only [serializeOf, readType, serializeValueOf, readValue, runSsz,
        show MAX_NESTING = 254 + 2 from rfl, parseType, parseValue, typeWellFormed,
        bind, Except.bind, Except.mapError, pure, Except.pure]
      simp [serialize, serializeStruct, allFields, canonicalBytes, bind, Except.bind]

private def readRootCell (state : List String × List Desc × List Value) (cell : RecordCell) :
    Option (List String × List Desc × List Value) := do
  return (cell.name :: state.1, (← cell.readType) :: state.2.1,
    (← cell.readValue ByteArray.data) :: state.2.2)

private theorem unfold_root_fold {cells : List RecordCell}
    {names names' : List String} {types types' : List Desc} {values values' : List Value}
    (h : cells.foldlM readRootCell (names, types, values) = some (names', types', values')) :
    ∃ fields items,
      cells.mapM RecordCell.readType = some fields ∧
      cells.mapM (RecordCell.readValue ByteArray.data) = some items ∧
      names' = (cells.map RecordCell.name).reverse ++ names ∧
      types' = fields.reverse ++ types ∧
      values' = items.reverse ++ values := by
  induction cells generalizing names types values with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨[], [], rfl, rfl, rfl, rfl, rfl⟩
  | cons cell rest ih =>
    simp only [List.foldlM_cons, readRootCell, bind, Option.bind, pure] at h
    cases ht : cell.readType with
    | none => simp [ht] at h
    | some type =>
      cases hv : cell.readValue ByteArray.data with
      | none => simp [ht, hv] at h
      | some value =>
        simp only [ht, hv] at h
        obtain ⟨fields, items, fs, vs, ns, ts, ws⟩ := ih h
        refine ⟨type :: fields, value :: items, ?_, ?_, ?_, ?_, ?_⟩
        · simp [List.mapM_cons, ht, fs, bind, Option.bind, pure]
        · simp [List.mapM_cons, hv, vs, bind, Option.bind, pure]
        · simpa [List.reverse_cons, List.append_assoc] using ns
        · simpa [List.reverse_cons, List.append_assoc] using ts
        · simpa [List.reverse_cons, List.append_assoc] using ws

/-- The compact root operation has the same result as the tagged root operation. -/
theorem hashTreeRootRecordExport_eq (typeTag valueTag : String) (cells : Array RecordCell) :
    hashTreeRootRecordExport typeTag valueTag cells =
      hashTreeRootOf (recordArgs typeTag valueTag cells) := by
  unfold hashTreeRootRecordExport
  cases h : hashTreeRootRecord typeTag valueTag cells with
  | none => rfl
  | some root =>
    have typeKey : typeTag = "container" := by
      by_cases valid : typeTag = "container"
      · exact valid
      · simp [hashTreeRootRecord, valid] at h
    have valueKey : valueTag = "seq" := by
      by_cases valid : valueTag = "seq"
      · exact valid
      · simp [hashTreeRootRecord, valid] at h
    subst typeTag valueTag
    simp only [hashTreeRootRecord, bne_self_eq_false, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, ← Array.foldlM_toList, bind, Option.bind, pure] at h
    change (cells.toList.foldlM readRootCell ([], [], []) >>= fun state => do
        let shape := Desc.container state.1.reverse state.2.1.reverse
        let () ← shape.wellFormed.toOption
        return ⟨← (hashTreeRoot shape (.seq state.2.2.reverse)).toOption⟩) = some root at h
    cases fold : cells.toList.foldlM readRootCell ([], [], []) with
    | none => simp [fold] at h
    | some state =>
      obtain ⟨names, types, values⟩ := state
      obtain ⟨fields, items, fieldRead, itemRead, rn, rt, rv⟩ := unfold_root_fold fold
      simp only [List.append_nil] at rn rt rv
      subst names types values
      let shape := Desc.container (cells.toList.map RecordCell.name) fields
      have parseType := record_desc (fuel := 254) "seq" fieldRead
      have parseValue := record_value ByteArray.data id 254 "container" itemRead
      simp only [fold] at h
      cases valid : shape.wellFormed with
      | error => simp [shape, valid, bind, Option.bind, Except.toOption] at h
      | ok legal =>
        cases legal
        cases hashed : hashTreeRoot shape (.seq items) with
        | error =>
          simp [shape, valid, hashed, bind, Option.bind, Except.toOption] at h
        | ok bytes =>
          have same : (⟨bytes⟩ : ByteArray) = root := by
            simpa [shape, valid, hashed, bind, Option.bind, pure, Except.toOption] using h
          subst root
          simp [hashTreeRootOf, hashTreeRootValueOf, readType, readValue, runSsz, valueOf,
            show MAX_NESTING = 254 + 2 from rfl, parseType, parseValue,
            shape, valid, hashed, bind, Except.bind, Except.mapError, pure, Except.pure]

end EthLib.Serialization.Ssz.Exports.Proofs
