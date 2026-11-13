module

/-!
# A proof module

The check reads only the specification, so this site has no entry.
-/

@[expose] public section

namespace CheckAccessorsTest.Proofs.Lemmas

/-- Outside the scope of the check. -/
def inProofs (xs : Array Nat) : Nat := xs[0]!

end CheckAccessorsTest.Proofs.Lemmas
