import EthLib.Serialization.Proofs.Ssz.Type.Equality

/-! Byte-array aliases and the limits of tree-shape compatibility. -/

namespace EthLib.Serialization.Ssz

/-- A fixed byte array has the tree shape of a vector of one-byte integers. -/
@[simp] theorem isCompatible_byteVector (length : Nat) :
    isCompatible (.byteVector length) (.vector (.uint 1) length) = true := by
  -- Both spellings normalize to the same byte-array shape before nested comparison.
  simp only [isCompatible, Desc.nesting]
  rw [compatibleAt.eq_def]
  simp [Desc.byteSequence, show (Desc.byteVector length == Desc.vector (.uint 1) length) = false from rfl]

/-- The byte-vector alias is recognized in either direction. -/
@[simp] theorem isCompatible_vectorByte (length : Nat) :
    isCompatible (.vector (.uint 1) length) (.byteVector length) = true := by
  -- Normalization also recognizes the byte-array spelling on the right.
  simp only [isCompatible, Desc.nesting]
  rw [compatibleAt.eq_def]
  simp [Desc.byteSequence]

/-- A bounded byte array has the tree shape of a list of one-byte integers. -/
@[simp] theorem isCompatible_byteList (limit : Nat) :
    isCompatible (.byteList limit) (.list (.uint 1) limit) = true := by
  -- Both spellings retain the same capacity and length-word placement.
  simp only [isCompatible, Desc.nesting]
  rw [compatibleAt.eq_def]
  simp [Desc.byteSequence]

/-- The byte-list alias is recognized in either direction. -/
@[simp] theorem isCompatible_listByte (limit : Nat) :
    isCompatible (.list (.uint 1) limit) (.byteList limit) = true := by
  -- Capacity-preserving normalization works in either comparison order.
  simp only [isCompatible, Desc.nesting]
  rw [compatibleAt.eq_def]
  simp [Desc.byteSequence]

/-- Even valid progressive declarations can agree through disjoint fields without transitivity. -/
theorem isCompatible_not_transitive :
    ∃ left middle right : Desc,
      left.wellFormed = .ok () ∧ middle.wellFormed = .ok () ∧ right.wellFormed = .ok () ∧
      isCompatible left middle = true ∧ isCompatible middle right = true ∧
      isCompatible left right = false := by
  -- The middle declaration occupies position one, sharing no field with either outer declaration.
  -- The outer declarations both occupy position zero but disagree on the field's type.
  refine ⟨.progressiveContainer [true] ["a"] [.bool],
    .progressiveContainer [false, true] ["b"] [.bool],
    .progressiveContainer [true] ["a"] [.uint 1], ?_⟩
  -- The two occupied positions are zero and one, so only the outer pair shares a position.
  have first : placedOrdinals [true] ["a"] = [(0, "a", 0)] := by simp [placedOrdinals, placedFields]
  have second : placedOrdinals [false, true] ["b"] = [(1, "b", 0)] := by simp [placedOrdinals, placedFields]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    change compatibleAt 4 _ _ = _
    rw [compatibleAt.eq_def]
    simp only [beq_iff_eq, Desc.progressiveContainer.injEq, List.cons.injEq,
      Bool.true_eq_false, Bool.false_eq_true, false_and, ↓reduceIte, Desc.byteSequence]
    rw [layoutsAgree.eq_def]
    simp [first, second, layoutPairAgree.eq_def]
  rw [compatibleAt.eq_def]
  simp [Desc.byteSequence]

end EthLib.Serialization.Ssz
