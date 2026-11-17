module

public import CheckTheoremsTest.Spec
public import CheckTheoremsTest.Hidden
public import CheckTheoremsTest.LocalSyntax
public import CheckTheoremsTest.Proofs.Lemmas
public import CheckTheoremsTest.Exports.Api

/-!
# Fixtures for the theorem placement check

The check uses the defining module, including this root, rather than the declaration's namespace.
-/

@[expose] public section

/-- A theorem declared in the library root is a finding too. -/
theorem root_unused (n : Nat) : n + 0 = n := Nat.add_zero n

/-- A definition in the root makes the root part of a nonempty specification. -/
def root_value : Nat := 0
