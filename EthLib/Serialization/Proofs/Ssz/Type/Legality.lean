module

public import EthLib.Serialization.Ssz.Type.Valid
public import EthLib.Base.Proofs.List

/-! What a legal composite type declares, read off the checks that validity makes. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A legal container declares fields, each under one name of its own, each legal. -/
theorem wellFormed_container_iff (names : List String) (fields : List Desc) :
    (Desc.container names fields).wellFormed = .ok () ↔
      fields ≠ [] ∧ names.length = fields.length ∧ names.Nodup ∧
        Desc.allWellFormed fields = .ok () := by
  -- Each check either refuses or passes, so every combination of outcomes is settled by evaluation.
  simp only [Desc.wellFormed]
  by_cases e : fields.isEmpty = true <;> by_cases l : (names.length != fields.length) = true <;>
    by_cases d : names.Nodup <;> cases a : Desc.allWellFormed fields <;>
    simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

/-- A legal progressive container declares a layout ending on a field.

It has one set position per field.

Its fields are each under one name of its own, and each legal. -/
theorem wellFormed_progressiveContainer_iff (active : List Bool) (names : List String) (fields : List Desc) :
    (Desc.progressiveContainer active names fields).wellFormed = .ok () ↔
      active ≠ [] ∧ active.getLast? = some true ∧ active.length ≤ maxActiveFields ∧ fields ≠ [] ∧
        active.countP (· == true) = fields.length ∧ names.length = fields.length ∧
        names.Nodup ∧ Desc.allWellFormed fields = .ok () := by
  -- The checks run in order, so each one is settled before the next is read.
  simp only [Desc.wellFormed]
  by_cases e : active.isEmpty = true
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  simp only [e, Bool.false_eq_true, ite_false]
  by_cases g : (active.getLast? == some false) = true
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
  -- A nonempty layout has a last position, and the gap check says it is set.
  obtain ⟨x, hx⟩ : ∃ x, active.getLast? = some x := by
    cases h : active.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) (by simpa using e)
    | some x => exact ⟨x, rfl⟩
  have hx' : x = true := by simpa [hx] using g
  subst hx'
  by_cases d : names.Nodup
  · simp_all
  · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

/-- A legal union declares options, each under a selector of its own in range, all legal, every two compatible. -/
theorem wellFormed_compatibleUnion_iff (selectors : List Nat) (options : List Desc) :
    (Desc.compatibleUnion selectors options).wellFormed = .ok () ↔
      selectors ≠ [] ∧ options ≠ [] ∧ selectors.length = options.length ∧ selectors.Nodup ∧
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
  cases d : Base.firstRepeated selectors
  · have d := (Base.firstRepeated_eq_none_iff selectors).mp d
    cases f : selectors.find? (fun s => s < minSelector || s > maxSelector)
    · simp_all [Bind.bind, Except.bind]
      cases Desc.allWellFormed options <;> simp
    · simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  · -- A repeated selector is found exactly when the selectors are not distinct.
    have repeated : ¬ selectors.Nodup := fun distinct => by
      rw [(Base.firstRepeated_eq_none_iff selectors).mpr distinct] at d
      contradiction
    simp_all [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

end EthLib.Serialization.Ssz
