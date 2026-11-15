module

public import CheckTheoremsTest.Spec

/-! An export module is outside the checked library. -/

@[expose] public section

namespace CheckTheoremsTest.Exports

/-- An export cannot retain a specification theorem. -/
def usesSpecification (n : Nat) : Fin (n + 1) :=
  ⟨n, Spec.used_only_from_exports n⟩

/-- A theorem in the export tree is no finding. -/
theorem unused (n : Nat) : n + 0 = n := Nat.add_zero n

end CheckTheoremsTest.Exports
