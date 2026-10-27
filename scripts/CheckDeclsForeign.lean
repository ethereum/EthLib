/-!
# `CheckDeclsForeign`

Declarations from outside the checked scope, as a dependency would provide them.
The fixtures in `CheckDeclsTest` use them, and the check must still see what they bring in.
-/

namespace CheckDeclsForeign

/-- An axiom of a dependency. -/
axiom T : Type

/-- An opaque constant of a dependency. -/
opaque hiddenNat : Nat

end CheckDeclsForeign
