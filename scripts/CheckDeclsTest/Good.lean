/-!
# `CheckDeclsTest.Good`

Declarations the declaration check must pass.
-/

namespace CheckDeclsTest.Good

/-- A plain definition. -/
def double (n : Nat) : Nat := n + n

/-- A theorem the kernel checks. -/
theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double
  omega

/-- Structural recursion: it unfolds in the kernel. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- A known answer the kernel decides. -/
theorem sumTo_three : sumTo 3 = 6 := by decide

/-- A fold over an array.
Lean core compiles `Array.foldl` with `@[implemented_by]`, but its definition unfolds, so it is not a finding. -/
def total (xs : Array Nat) : Nat := xs.foldl (· + ·) 0

/-- A panic with a plain fallback.
Its message is built from `String` operations the kernel cannot unfold, but the message is not part of the value. -/
def checked (n : Nat) : Nat :=
  if n < 10 then n else panic! s!"too large: {n}"

end CheckDeclsTest.Good
