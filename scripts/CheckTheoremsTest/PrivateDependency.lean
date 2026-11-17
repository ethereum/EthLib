module

/-! A module reached through a private import. -/

@[expose] public section

namespace CheckTheoremsTest.PrivateDependency

/-- A definition in the importing module needs this theorem. -/
theorem imported_bound (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- Importing the module does not retain its unused theorem. -/
theorem imported_unused (n : Nat) : n + 0 = n := Nat.add_zero n

end CheckTheoremsTest.PrivateDependency
