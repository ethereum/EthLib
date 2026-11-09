module

/-!
# `CheckDeclsForeign`

Declarations from outside the checked scope, as a dependency would provide them.
The fixtures in `CheckDeclsTest` use them, and the check must still see what they bring in.
-/

@[expose] public section

namespace CheckDeclsForeign

/-- An axiom of a dependency. -/
axiom T : Type

/-- A second axiom of a dependency, used only through `Cycle`. -/
axiom U : Type

/-- A proposition of a dependency that holds only if its axiom has an element. -/
def P : Prop := Nonempty U

/-- An inductive type of a dependency whose constructor carries its axiom, through `P`.

The type and its constructor each inherit the axiom from the other. -/
inductive Cycle where
  | mk (h : P)

/-- An opaque constant of a dependency. -/
opaque hiddenNat : Nat

end CheckDeclsForeign
