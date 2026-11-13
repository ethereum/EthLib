module

/-!
# A site in a hidden body, and one that the check cannot see

The body of a definition that is not exposed is not in the public part of its module.

The check loads the private level, so it still counts the site.

The body of a `partial def` is only in its compiled copy, which the check skips.

`lake exe check-decls` rejects `partial` in the specification, so the check need not count it.
-/

public section

namespace CheckAccessorsTest.Hidden

/-- Not exposed: `GetElem?.getElem!`, once. -/
def opaqueBody (xs : Array Nat) : Nat := xs[0]!

/-- The blind spot of the check: this declaration has no entry. -/
partial def scan (xs : Array Nat) (i : Nat) : Nat :=
  if i < 3 then scan xs (i + 1) else xs[i]!

end CheckAccessorsTest.Hidden
