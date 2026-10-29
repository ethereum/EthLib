import EthLib.Serialization.Ssz.Type.Default
import EthLib.Serialization.Ssz.Type.Valid

/-! Structural equality and recognition of default values. -/

namespace EthLib.Serialization.Ssz

/-- Comparing nested declarations succeeds exactly when the declarations are equal. -/
theorem Desc.beq_eq (left right : Desc) : Desc.beq left right = true ↔ left = right := by
  -- Nested induction covers field lists and union options along with their enclosing types.
  induction left using Desc.rec
    (motive_2 := fun left => ∀ right, Desc.beqList left right = true ↔ left = right)
    generalizing right <;> (first | cases right | (rename_i right; cases right)) <;>
    simp [Desc.beq, Desc.beqList, and_assoc, *]

/-- Declaration comparison can be used as ordinary equality throughout the specification. -/
instance : LawfulBEq Desc where
  rfl := (Desc.beq_eq _ _).mpr rfl
  eq_of_beq := (Desc.beq_eq _ _).mp

/-- Every type has at least one level, including a type with no nested components. -/
theorem Desc.nesting_pos (shape : Desc) : 0 < shape.nesting := by
  -- Every constructor contributes one level above any nested components.
  cases shape <;> simp [Desc.nesting]

/-- One remaining comparison step suffices to recognize the same declaration. -/
@[simp] theorem compatibleAt_self (budget : Nat) (shape : Desc) :
    compatibleAt (budget + 1) shape shape = true := by
  -- Structural equality takes the first branch before any nested comparison is needed.
  rw [compatibleAt.eq_def]
  simp

/-- Every declaration is compatible with itself. -/
@[simp] theorem isCompatible_self (shape : Desc) : isCompatible shape shape = true := by
  -- The public comparison allocates a positive budget even for a type with no children.
  have positive := shape.nesting_pos
  unfold isCompatible
  cases total : shape.nesting + shape.nesting with
  | zero => omega
  | succ budget => exact compatibleAt_self budget shape

end EthLib.Serialization.Ssz
