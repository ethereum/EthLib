module

public import EthLib.Serialization.Ssz.Type.Default

/-! Equality of values, and the values that are zeroed for their type. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- Two values compare equal exactly when they are equal. -/
theorem Value.beq_eq (left right : Value) : Value.beq left right = true ↔ left = right := by
  -- Nested induction covers the elements of a sequence along with the values around them.
  induction left using Value.rec
    (motive_2 := fun left => ∀ right, Value.beqList left right = true ↔ left = right)
    generalizing right <;> (first | cases right | (rename_i right; cases right)) <;>
    simp [Value.beq, Value.beqList, *]

/-- The comparison `==` on values is equality. -/
instance : LawfulBEq Value where
  rfl := (Value.beq_eq _ _).mpr rfl
  eq_of_beq := (Value.beq_eq _ _).mp

/-- A value is zeroed for a type exactly when it is the default of that type. -/
theorem Desc.isZero_ok_iff {shape : Desc} {value : Value} :
    shape.isZero value = .ok true ↔ shape.default = .ok value := by
  unfold Desc.isZero
  cases h : shape.default with
  | error e => simp [Bind.bind, Except.bind]
  | ok d =>
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq, beq_iff_eq]

end EthLib.Serialization.Ssz
