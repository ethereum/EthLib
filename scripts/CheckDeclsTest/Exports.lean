module

/-!
# `CheckDeclsTest.Exports`

An export module: it may reach `IO`, which the specification may not.
-/

@[expose] public section

namespace CheckDeclsTest.Exports

/-- Reads and writes a mutable reference, as the C exports may. -/
def roundTrip (n : Nat) : IO Nat := do
  let r ← IO.mkRef n
  r.get

end CheckDeclsTest.Exports
