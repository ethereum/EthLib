import EthLib.Consensus.Proofs.Ssz.Codec.RootLaws
import EthLib.Consensus.Proofs.Ssz.Merkle.Widths
import EthLib.Consensus.Proofs.Ssz.Type.Equality

/-! Admissible values have a Merkle root, independently of serialization's offset limit. -/

namespace EthLib.Consensus.Ssz

/-- Packed leaves have complete node widths.
Nested leaves admit rooting, and bounded trees hold every supplied position.
-/
def LayoutFits (layout : MerkleLayout) : Prop :=
  (match layout.leaves with
    | .packed chunks => ∀ chunk ∈ chunks, chunk.size = bytesPerChunk
    | .nested slots => ∀ shape value, some (shape, value) ∈ slots →
        Fits shape value ∧ shape.wellFormed = .ok ()) ∧
  ∀ capacity, layout.limit = some capacity → layout.leaves.count ≤ capacity

private theorem packed_fits (data : Bytes) (limit : Option Nat) (mixin : Option Bytes)
    (bounded : ∀ capacity, limit = some capacity → chunksForBytes data.size ≤ capacity) :
    LayoutFits (.packing (packBytes data) limit mixin) := by
  -- The byte count rounds up to whole nodes, which must fit the declared capacity.
  exact ⟨packBytes_mem_size data, by simpa [MerkleLayout.packing, Leaves.count, chunksForBytes] using bounded⟩

private theorem basic_encoding {shape : Desc} {value : Value}
    (basic : shape.isBasic = true) (fitted : Fits shape value) :
    ∃ bytes, serialize shape value = .ok bytes ∧ bytes.size = shape.itemLength := by
  -- Only booleans and integers share nodes with their neighbors.
  cases fitted <;> simp [Desc.isBasic] at basic
  case bool b => exact ⟨#[if b then 1 else 0], by simp [serialize], rfl⟩
  case uint width n bound => exact ⟨uintBytes width n, by simp [serialize, bound], uintBytes_size _ _⟩

/-- Basic elements serialize to exactly their fixed byte widths, without offset tables. -/
theorem serializeEach_basic_size {shape : Desc} (basic : shape.isBasic = true) :
    ∀ values, (∀ value ∈ values, Fits shape value) →
    ∃ parts, serializeEach shape values = .ok parts ∧
      (parts.foldl (fun total part => total ++ part) (#[] : Bytes)).size =
        values.length * shape.itemLength := by
  -- Concatenating basic encodings adds their fixed byte widths.
  -- The accumulated prefix contributes its existing width, followed by the sum of every encoded part.
  have fold_size : ∀ (parts : List Bytes) (front : Bytes),
      (parts.foldl (fun total part => total ++ part) front).size =
        front.size + (parts.map Array.size).sum := by
    intro parts
    induction parts <;> simp [*, Nat.add_assoc]
  intro values
  induction values with
  | nil => intro _; exact ⟨[], by simp [serializeEach], by simp⟩
  | cons value values ih =>
    intro each
    -- The first basic value contributes its fixed byte width to the remaining sequence.
    obtain ⟨head, wrote, sized⟩ := basic_encoding basic (each value List.mem_cons_self)
    obtain ⟨tail, rest, total⟩ := ih (fun item member => each item (List.mem_cons_of_mem _ member))
    refine ⟨head :: tail, by simp [serializeEach, wrote, rest, Bind.bind, Except.bind, pure, Except.pure], ?_⟩
    simp only [fold_size, Array.size_empty, Nat.zero_add] at total ⊢
    simp [sized, total, Nat.add_mul, Nat.add_comm]

private theorem sequence_fits {element : Desc} {values : List Value}
    (sound : element.wellFormed = .ok ()) (each : ∀ value ∈ values, Fits element value)
    (positions : Option Nat) (mixin : Option Bytes)
    (bounded : ∀ capacity, positions = some capacity → values.length ≤ capacity) :
    ∃ layout, sequenceLayout element values positions mixin = .ok layout ∧ LayoutFits layout := by
  -- Composite elements contribute individual roots.
  -- Basic elements contribute consecutive packed bytes.
  cases basic : element.isBasic with
  | false =>
    refine ⟨.nesting (values.map fun value => some (element, value)) positions mixin,
      by simp [sequenceLayout, basic, pure, Except.pure], ?_, ?_⟩
    · intro shape value member
      obtain ⟨inside, rfl⟩ := by simpa using member
      exact ⟨each value inside, sound⟩
    · simpa [MerkleLayout.nesting, Leaves.count] using bounded
  | true =>
    -- A basic sequence occupies its element count times its declared byte width.
    obtain ⟨parts, wrote, sized⟩ := serializeEach_basic_size basic values each
    refine ⟨.packing (packElements parts)
      (positions.map fun count => chunksForBytes (count * element.itemLength)) mixin,
      by simp [sequenceLayout, basic, wrote, Bind.bind, Except.bind, pure, Except.pure], ?_⟩
    apply packed_fits
    intro capacity named
    obtain ⟨count, rfl, rfl⟩ := Option.map_eq_some_iff.mp named
    change chunksForBytes (parts.foldl _ (#[] : Bytes)).size ≤ _
    rw [sized]
    unfold chunksForBytes
    exact Nat.div_le_div_right (Nat.sub_le_sub_right
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (bounded count rfl)) _) _)

/-- A matching active-field count supplies exactly one slot per layout position. -/
theorem placeSlots_exists : ∀ active fields,
    active.countP id = fields.length → ∃ slots, placeSlots active fields = .ok slots := by
  -- Each active position consumes one field, while gaps consume none.
  intro active
  induction active with
  | nil =>
    intro fields counted
    cases fields <;> simp_all [placeSlots]
  | cons bit active ih =>
    intro fields counted
    cases bit with
    | false =>
      obtain ⟨slots, placed⟩ := ih fields (by simpa using counted)
      exact ⟨none :: slots, by simp [placeSlots, placed, Bind.bind, Except.bind, pure, Except.pure]⟩
    | true =>
      cases fields with
      | nil => simp at counted
      | cons field fields =>
        obtain ⟨slots, placed⟩ := ih fields (by simpa using counted)
        exact ⟨some field :: slots, by simp [placeSlots, placed, Bind.bind, Except.bind, pure, Except.pure]⟩

/-- A well-formed progressive container declares one field per active position. -/
theorem progressive_count {active names fields}
    (sound : (Desc.progressiveContainer active names fields).wellFormed = .ok ()) :
    active.countP id = fields.length := by
  -- A legal progressive layout has exactly one active position per declared field.
  rw [Desc.wellFormed] at sound
  repeat' first | split at sound | simp only [Bind.bind, Except.bind] at sound
  all_goals simp_all
  change active.countP (fun x => x) = fields.length
  assumption

private theorem fixed_fits {shape : Desc} {value : Value} {bytes : Bytes}
    (wrote : serialize shape value = .ok bytes) :
    ∃ layout, fixedLeaf shape value = .ok layout ∧ LayoutFits layout := by
  -- A fixed leaf chooses precisely the capacity its own bytes require.
  refine ⟨.packing (packBytes bytes) (some (packBytes bytes).size),
    by simp [fixedLeaf, wrote, Bind.bind, Except.bind, pure, Except.pure], ?_⟩
  apply packed_fits
  rintro _ ⟨⟩
  simp [chunksForBytes]

private theorem bits_fits (data : Array Bool) (limit : Option Nat) (mixin : Option Bytes)
    (bounded : ∀ capacity, limit = some capacity → chunksForBits data.size ≤ capacity) :
    LayoutFits (.packing (packedBits data) limit mixin) := by
  -- Rounding bits to bytes and then nodes is the same as rounding directly to 256 bits.
  apply packed_fits
  intro capacity named
  have bound := bounded capacity named
  simp only [packBits, Array.size_ofFn, chunksForBytes, chunksForBits, bytesPerChunk] at *
  omega

/-- A well-formed type and an admissible value supply a valid layout before any hashes are computed. -/
theorem layout_exists {shape : Desc} {value : Value}
    (fitted : Fits shape value) (sound : shape.wellFormed = .ok ()) :
    ∃ layout, merkleLayout shape value = .ok layout ∧ LayoutFits layout := by
  -- Each admissibility constructor supplies exactly the count or bound its layout needs.
  cases fitted with
  | bool b => exact fixed_fits (bytes := #[if b then 1 else 0]) (by simp [serialize])
  | @uint width n bound => exact fixed_fits (bytes := uintBytes width n) (by simp [serialize, bound])
  | @byteVector length data exact =>
    refine ⟨.packing (packBytes data) (some (packBytes data).size),
      by simp [merkleLayout, exact, pure, Except.pure], ?_⟩
    apply packed_fits
    rintro _ ⟨⟩
    simp [chunksForBytes]
  | @byteList limit data within =>
    refine ⟨.packing (packBytes data) (some (chunksForBytes limit)) (lengthWord data.size),
      by simp [merkleLayout, Nat.not_lt.mpr within, pure, Except.pure], ?_⟩
    apply packed_fits
    rintro _ ⟨⟩
    unfold chunksForBytes
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right within _) _)
  | @bitVector length data exact =>
    refine ⟨.packing (packedBits data) (some (chunksForBits length)),
      by simp [merkleLayout, exact, pure, Except.pure], ?_⟩
    apply bits_fits
    rintro _ ⟨⟩
    simp [exact]
  | @bitList limit data within =>
    refine ⟨.packing (packedBits data) (some (chunksForBits limit)) (lengthWord data.size),
      by simp [merkleLayout, Nat.not_lt.mpr within, pure, Except.pure], ?_⟩
    apply bits_fits
    rintro _ ⟨⟩
    unfold chunksForBits
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right within _) _)
  | @progressiveBitList limit data within =>
    refine ⟨_, by simp [merkleLayout, boundCheck_of_withinBound limit _ within, Bind.bind,
      Except.bind]; rfl, ?_⟩
    apply bits_fits
    simp
  | @vector element length elements count each =>
    simpa [merkleLayout, count] using
      sequence_fits (wellFormed_vector sound) each (some length) none (by simp [count])
  | @list element limit elements within each =>
    simpa [merkleLayout, Nat.not_lt.mpr within] using
      sequence_fits (wellFormed_list sound) each (some limit) (lengthWord elements.length)
        (by intro capacity named; cases named; exact within)
  | @progressiveList element limit elements within each =>
    simpa [merkleLayout, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind] using
      sequence_fits (wellFormed_progressiveList sound) each none (lengthWord elements.length) (by simp)
  | @container names fields values paired each =>
    refine ⟨.nesting ((fields.zip values).map some) (some fields.length),
      by simp [merkleLayout, paired, pure, Except.pure], ?_, ?_⟩
    · intro child inner member
      replace member : (child, inner) ∈ fields.zip values := by simpa using member
      exact ⟨each (child, inner) member, allWellFormed_mem _ (wellFormed_container sound)
        child (List.of_mem_zip member).1⟩
    · simp [MerkleLayout.nesting, Leaves.count, paired]
  | @progressiveContainer active names fields values paired each =>
    -- Gaps remain explicit leaves, but only occupied positions need recursive roots.
    obtain ⟨slots, placed⟩ := placeSlots_exists active (fields.zip values)
      (by simp [progressive_count sound, paired])
    refine ⟨.nesting slots none (activeFieldsWord active), ?_, ?_, by intro capacity named; cases named⟩
    · simp [merkleLayout, layoutSlots, paired, progressive_count sound, placed,
        Bind.bind, Except.bind, pure, Except.pure]
    · intro child inner member
      -- Removing the inserted gaps recovers membership in the original field-value pairing.
      have pairedMember : (child, inner) ∈ fields.zip values := by
        rw [← placeSlots_fields placed]
        exact List.mem_filterMap.mpr ⟨some (child, inner), member, rfl⟩
      exact ⟨each _ pairedMember, allWellFormed_mem _ (wellFormed_progressiveContainer sound)
        child (List.of_mem_zip pairedMember).1⟩
  | @compatibleUnion selectors options selector option data bounded named inner =>
    refine ⟨.nesting [some (option, data)] (some 1) (lengthWord selector),
      by simp [merkleLayout, named, selectorWord, checkSelector_of_range bounded,
      Bind.bind, Except.bind, pure, Except.pure], ?_, ?_⟩
    · intro child value member
      obtain ⟨rfl, rfl⟩ := by simpa using member
      exact ⟨inner, allWellFormed_mem _ (wellFormed_union sound) _ (lookupOption_mem _ _ _ _ named)⟩
    · simp [MerkleLayout.nesting, Leaves.count]

private theorem root_slots (budget : Nat) : ∀ slots : List (Option (Desc × Value)),
    (∀ shape value, some (shape, value) ∈ slots →
      ∃ root, hashTreeRootAt budget shape value = .ok root ∧ root.size = bytesPerChunk) →
    ∃ chunks, slots.mapM (m := Except Err) (fun slot => match slot with
      | none => Except.ok zeroChunk
      | some (shape, value) => hashTreeRootAt budget shape value) = .ok chunks ∧
      ∀ chunk ∈ chunks, chunk.size = bytesPerChunk := by
  -- Root the occupied slots in order and fill every gap with one zero node.
  intro slots
  induction slots with
  | nil => intro _; exact ⟨[], rfl, by simp⟩
  | cons slot slots ih =>
    intro each
    obtain ⟨tail, rooted, widths⟩ := ih (fun shape value member =>
      each shape value (List.mem_cons_of_mem _ member))
    -- An inactive position contributes the complete zero node, while an occupied position supplies its child root.
    have head : ∃ root, (match slot with
        | none => Except.ok zeroChunk
        | some (shape, value) => hashTreeRootAt budget shape value) = .ok root ∧
        root.size = bytesPerChunk := by
      cases slot with
      | none => exact ⟨zeroChunk, rfl, zeroChunk_size⟩
      | some pair => exact each pair.1 pair.2 List.mem_cons_self
    obtain ⟨root, first, sized⟩ := head
    refine ⟨root :: tail, ?_, ?_⟩
    · simp only [List.mapM_cons, first, rooted, Bind.bind, Except.bind, pure, Except.pure]
    · exact List.forall_mem_cons.mpr ⟨sized, widths⟩

private theorem materialize_layout (budget : Nat) (layout : MerkleLayout)
    (fitted : LayoutFits layout)
    (each : ∀ slots, layout.leaves = .nested slots → ∀ shape value,
      some (shape, value) ∈ slots →
      ∃ root, hashTreeRootAt budget shape value = .ok root ∧ root.size = bytesPerChunk) :
    ∃ chunks, layoutChunksAt budget layout = .ok chunks ∧
      (∀ chunk ∈ chunks, chunk.size = bytesPerChunk) ∧
      ∀ capacity, layout.limit = some capacity → chunks.size ≤ capacity := by
  -- Materialization preserves the leaf count and the width of every node.
  rcases layout with ⟨leaves, limit, mixin⟩
  cases leaves with
  | packed chunks =>
    refine ⟨chunks, ?_, fitted.1, fitted.2⟩
    simp [layoutChunksAt, Leaves.count, pure, Except.pure]
  | nested slots =>
    obtain ⟨chunks, rooted, widths⟩ := root_slots budget slots (each slots rfl)
    have wrote : layoutChunksAt budget ⟨.nested slots, limit, mixin⟩ = .ok chunks.toArray := by
      simp only [layoutChunksAt, Leaves.count, Option.getD_none, List.drop_zero, Nat.sub_zero,
        List.take_length, pure, Except.pure]
      apply Eq.trans ?_ (congrArg (fun result : Except Err (List Bytes) =>
        result.bind fun result => Except.ok result.toArray) rooted)
      congr 2
    refine ⟨chunks.toArray, wrote, ?_, ?_⟩
    · simpa using widths
    · exact layoutChunksAt_size _ _ _ wrote ▸ fitted.2

/-- A sufficient type-depth budget roots every admissible value into one complete node. -/
theorem hashTreeRootAt_total (budget : Nat) (shape : Desc) (value : Value)
    (enough : shape.nesting ≤ budget) (sound : shape.wellFormed = .ok ())
    (fitted : Fits shape value) :
    ∃ root, hashTreeRootAt budget shape value = .ok root ∧ root.size = bytesPerChunk := by
  -- Every nested type is shallower, so one less recursion step still suffices.
  induction budget generalizing shape value with
  | zero => have positive := shape.nesting_pos; omega
  | succ budget ih =>
    -- The admissibility proof provides both complete packed leaves and valid nested values.
    obtain ⟨layout, laid, valid⟩ := layout_exists fitted sound
    obtain ⟨chunks, materialized, widths, bounded⟩ := materialize_layout budget layout valid
      (by
        intro slots nested child inner member
        -- A nested child consumes one less depth level than the declaration enclosing it.
        have smaller := merkleLayout_child_nesting shape value layout laid slots nested child inner member
        have admissible := valid.1
        rw [nested] at admissible
        obtain ⟨childFits, childSound⟩ := admissible child inner member
        exact ih child inner (by omega) childSound childFits)
    -- The declared capacity holds all materialized leaves, so no tree truncates data.
    have contents : ∃ root, (match layout.limit with
        | none => Except.ok (ε := Err) (merkleizeProgressiveUnchecked chunks.toList)
        | some capacity => merkleizeBoundedUnchecked chunks (some capacity)) = .ok root ∧
        root.size = bytesPerChunk := by
      cases capacity : layout.limit with
      | none => exact ⟨_, rfl, merkleizeProgressiveUnchecked_size _ _⟩
      | some limit =>
        have within := bounded limit capacity
        refine ⟨subtreeAt chunks (depthFor limit) 0, ?_, subtreeAt_size chunks widths _ _⟩
        simp [merkleizeBoundedUnchecked, Nat.not_lt.mpr within, pure, Except.pure]
    -- An optional count, layout, or selector is hashed with the contents root.
    obtain ⟨contents, rooted, sized⟩ := contents
    refine ⟨match layout.mixin with | none => contents | some word => mixIn contents word, ?_, ?_⟩
    · cases limit : layout.limit with
      | none =>
        simp only [limit, Except.ok.injEq] at rooted
        subst contents
        simp only [hashTreeRootAt, bind, Except.bind, laid, materialized, limit, pure, Except.pure,
          Except.ok.injEq]
        cases layout.mixin <;> rfl
      | some capacity =>
        simp only [limit] at rooted
        simp only [hashTreeRootAt, bind, Except.bind, laid, materialized, limit, rooted, pure, Except.pure,
          Except.ok.injEq]
        cases layout.mixin <;> rfl
    · cases layout.mixin <;> simp [sized]

/-- Every admissible value of a well-formed type has a 32-byte SSZ root. -/
theorem hashTreeRoot_total (shape : Desc) (value : Value)
    (sound : shape.wellFormed = .ok ()) (fitted : Fits shape value) :
    ∃ root, hashTreeRoot shape value = .ok root ∧ root.size = bytesPerChunk :=
  hashTreeRootAt_total shape.nesting shape value (Nat.le_refl _) sound fitted

end EthLib.Consensus.Ssz
