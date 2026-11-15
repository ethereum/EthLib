module

import CheckTheoremsTest.PrivateDependency

/-!
# Dependencies behind a module boundary

The checker loads private declaration bodies and private imports.
-/

public section

namespace CheckTheoremsTest.Hidden

/-- A hidden definition retains this private theorem. -/
private theorem hidden_bound (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- A definition without an exposed body retains both imported and private proofs. -/
def hidden (n : Nat) : Fin (n + 1) × Fin (n + 1) :=
  (⟨n, hidden_bound n⟩, ⟨n, CheckTheoremsTest.PrivateDependency.imported_bound n⟩)

/-- This private finding has the same user-facing name as a finding in another module. -/
private theorem _root_.CheckTheoremsTest.Spec.private_unused (n : Nat) : n + 0 = n :=
  Nat.add_zero n

end CheckTheoremsTest.Hidden
