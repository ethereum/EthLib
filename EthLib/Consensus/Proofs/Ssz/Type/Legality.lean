import EthLib.Consensus.Ssz.Type.Valid

/-! What a legal composite type declares, read off the checks that validity makes. -/

namespace EthLib.Consensus.Ssz

/-- A legal container declares fields, each under one name of its own, each legal. -/
theorem wellFormed_container_iff (names : List String) (fields : List Desc) :
    (Desc.container names fields).wellFormed = .ok () ↔
      fields ≠ [] ∧ names.length = fields.length ∧ firstDuplicate names = none ∧
        Desc.allWellFormed fields = .ok () := by
  -- Each check either refuses or passes, so every combination of outcomes is settled by evaluation.
  simp only [Desc.wellFormed]
  by_cases e : fields.isEmpty = true <;> by_cases l : (names.length != fields.length) = true <;>
    cases d : firstDuplicate names <;> cases a : Desc.allWellFormed fields <;>
    simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

/-- A legal progressive container declares a layout ending on a field, one set position per field, and fields each
under one name of its own and each legal. -/
theorem wellFormed_progressiveContainer_iff (active : List Bool) (names : List String) (fields : List Desc) :
    (Desc.progressiveContainer active names fields).wellFormed = .ok () ↔
      active ≠ [] ∧ active.getLast! = true ∧ active.length ≤ maxActiveFields ∧ fields ≠ [] ∧
        active.countP (· == true) = fields.length ∧ names.length = fields.length ∧
        firstDuplicate names = none ∧ Desc.allWellFormed fields = .ok () := by
  -- The checks run in order, so each one is settled before the next is read.
  simp only [Desc.wellFormed]
  by_cases e : active.isEmpty = true
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [e, Bool.false_eq_true, ite_false]
  by_cases g : (active.getLast! == false) = true
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [g, Bool.false_eq_true, ite_false]
  by_cases w : active.length > maxActiveFields
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    omega
  simp only [w, ite_false]
  by_cases f : fields.isEmpty = true
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [f, Bool.false_eq_true, ite_false]
  by_cases c : (active.countP (· == true) != fields.length) = true
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [c, Bool.false_eq_true, ite_false]
  by_cases l : (names.length != fields.length) = true
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [l, Bool.false_eq_true, ite_false]
  cases d : firstDuplicate names
  · simp_all
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

/-- A legal union declares options, each under a selector of its own in range, all legal, every two compatible. -/
theorem wellFormed_compatibleUnion_iff (selectors : List Nat) (options : List Desc) :
    (Desc.compatibleUnion selectors options).wellFormed = .ok () ↔
      selectors ≠ [] ∧ options ≠ [] ∧ selectors.length = options.length ∧ firstDuplicate selectors = none ∧
        selectors.find? (fun s => s < minSelector || s > maxSelector) = none ∧
        Desc.allWellFormed options = .ok () ∧ Desc.optionsCompatible selectors options = .ok () := by
  -- The checks run in order, so each one is settled before the next is read.
  simp only [Desc.wellFormed]
  by_cases e : (selectors.isEmpty || options.isEmpty) = true
  · have : selectors = [] ∨ options = [] := by simpa using e
    rcases this with h | h <;> simp [h, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [e, Bool.false_eq_true, ite_false]
  by_cases l : (selectors.length != options.length) = true
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [l, Bool.false_eq_true, ite_false]
  cases d : firstDuplicate selectors
  · cases f : selectors.find? (fun s => s < minSelector || s > maxSelector)
    · simp_all [Bind.bind, Except.bind]
      cases Desc.allWellFormed options <;> simp
    · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

/-- The element of a legal vector is legal. -/
theorem wellFormed_vector_element {element : Desc} {length : Nat}
    (sound : (Desc.vector element length).wellFormed = .ok ()) : element.wellFormed = .ok () := by
  -- An empty vector is refused outright, and otherwise the element's own check is what remains.
  by_cases z : length = 0
  · simp [Desc.wellFormed, z, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound
  · simpa [Desc.wellFormed, z] using sound

/-- A list with no repeated entry reports no duplicate. -/
theorem firstDuplicate_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ items : List α, items.Nodup → firstDuplicate items = none
  | [], _ => rfl
  | item :: rest, distinct => by
    -- The head is absent from the rest, and the rest has no duplicate either.
    rw [List.nodup_cons] at distinct
    simp [firstDuplicate, distinct.1, firstDuplicate_of_nodup rest distinct.2]

end EthLib.Consensus.Ssz
