module

public import CheckTheoremsTest.Spec

/-! A property module is outside the checked library. -/

@[expose] public section

namespace CheckTheoremsTest.Proofs

/-- A property cannot retain a specification theorem. -/
def usesSpecification (n : Nat) : Fin (n + 1) :=
  ⟨n, Spec.used_only_from_proofs n⟩

/-- A theorem in the property tree is no finding. -/
theorem unused (n : Nat) : n + 0 = n := Nat.add_zero n

end CheckTheoremsTest.Proofs
