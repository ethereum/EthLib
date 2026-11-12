module

/-!
# An export module

The check reads only the specification, so this site has no entry.
-/

@[expose] public section

namespace CheckAccessorsTest.Exports.Api

/-- Outside the scope of the check. -/
def inExports (xs : Array Nat) : Nat := xs[0]!

end CheckAccessorsTest.Exports.Api
